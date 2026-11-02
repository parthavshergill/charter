// Charter `attention` encoder. src/ocean.cu includes it for the charter env (rl/puffer/patches/0003-attention-encoder.patch).
// Needs precision_t, Prec, Allocator, puf_mm*, puf_kaiming_init from pufferl.cu and algo.cu.
//
// What it computes, per observation (attention_ref.py is the plain PyTorch version):
//   c       = relu(W_ctx [global; proposal])                       context, width D
//   x_i     = relu(W_t row_i)  for each row i of token table t     tokens, width D; padding rows dropped
//   head h: q_h = (Wq c)_h,  a_hi = softmax_i over real rows of (q_h . (Wk x_i)_h) / sqrt(DH)
//           y_h = sum_i a_hi (Wv x_i)_h
//   out     = Wout [y; c]                                          width = trainer hidden size
// A row is real when its column 0 (`real`) is above 0.5. A head with no real row returns 0.
//
// Wk and Wv are folded out of the loop over rows: q_h . (Wk x_i)_h = (Wk_h^T q_h) . x_i and
// sum_i a_hi (Wv x_i)_h = Wv_h (sum_i a_hi x_i). Same numbers, HEADS*D work per row instead of 3*ATT*D.
//
// Embeddings are cuBLAS GEMMs; weight gradients use a split-K kernel (ca_mm_tn). Two kernels do the attention, one block per
// observation; the backward kernel recomputes the softmax instead of saving it.
//
// Plain CUDA with float math, no tensor-core intrinsics, so it runs on the T4 (sm_75) in bf16 or float.

#include "attention_layout.h"

static constexpr int CA_D = 32;
static constexpr int CA_H = 8;
static constexpr int CA_DH = 8;
static constexpr int CA_A = CA_H * CA_DH;   // width of the heads' answers
static constexpr int CA_P = CA_A + CA_D;    // width of [y; c]
static constexpr int CA_HD = CA_H * CA_D;
static constexpr int CA_XS = CA_D + 2;      // row stride of the shared token tile: no bank conflicts
static constexpr int CA_THREADS = 256;
static constexpr int CA_WARPS = CA_THREADS / 32;

static const int CA_CTX_OFF[CA_N_CTX] = {CA_CTX_OFF_LIST};
static const int CA_CTX_WS[CA_N_CTX] = {CA_CTX_W_LIST};
static const int CA_TAB_OFF[CA_N_TAB] = {CA_TAB_OFF_LIST};
static const int CA_TAB_ROWS[CA_N_TAB] = {CA_TAB_ROWS_LIST};
static const int CA_TAB_W[CA_N_TAB] = {CA_TAB_W_LIST};
__constant__ int ca_tab_rows_d[CA_N_TAB] = {CA_TAB_ROWS_LIST};
__constant__ int ca_tab_w_d[CA_N_TAB] = {CA_TAB_W_LIST};

// Per-table pointers, passed to kernels by value.
struct CaTabs { precision_t* p[CA_N_TAB]; };

struct CaWeights {
    Prec w_ctx;
    Prec w_tab[CA_N_TAB];
    Prec wq, wk, wv, wout;
    int obs_size, hidden;
};

struct CaActs {
    // forward
    Prec ctx_in, cpre, c, q, pooled, out;
    Prec ents[CA_N_TAB], xpre[CA_N_TAB];
    // backward, train only
    Prec dpooled, dy, z, dqk, dq, dc, blk;
    Float part;   // partial sums for ca_mm_tn
    Prec dx[CA_N_TAB];
    // weight gradients, in the order of ca_reg_params
    Prec g_ctx;
    Prec g_tab[CA_N_TAB];
    Prec gq, gk, gv, gout;
};

static CaTabs ca_tabs(Prec* arr) {
    CaTabs t;
    for (int i = 0; i < CA_N_TAB; i++) t.p[i] = arr[i].data;
    return t;
}

// Which table and row token i is.
__device__ __forceinline__ void ca_token(int i, int& t, int& r) {
    t = 0;
    while (i >= ca_tab_rows_d[t]) { i -= ca_tab_rows_d[t]; t++; }
    r = i;
}

// Copy n numbers per observation from src (stride src_stride, start src_off) to dst (stride dst_stride,
// start dst_off).
__global__ void ca_gather_kernel(precision_t* __restrict__ dst, int dst_stride, int dst_off,
        const precision_t* __restrict__ src, int src_stride, int src_off, int n, int B) {
    int64_t idx = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= (int64_t)B * n) return;
    int b = idx / n, j = idx - (int64_t)b * n;
    dst[(int64_t)b * dst_stride + dst_off + j] = src[(int64_t)b * src_stride + src_off + j];
}

__global__ void ca_relu_kernel(precision_t* __restrict__ dst, const precision_t* __restrict__ src, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) dst[i] = from_float(fmaxf(0.0f, to_float(src[i])));
}

// dc <- (dc + dpooled[:, A:]) * (cpre > 0)
__global__ void ca_ctx_grad_kernel(precision_t* __restrict__ dc, const precision_t* __restrict__ dpooled,
        const precision_t* __restrict__ cpre, int B) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= B * CA_D) return;
    int b = i / CA_D, d = i - b * CA_D;
    float g = to_float(dc[i]) + to_float(dpooled[(int64_t)b * CA_P + CA_A + d]);
    dc[i] = from_float(to_float(cpre[i]) > 0.0f ? g : 0.0f);
}

// dst[r][d] = blk[r][head(r)*D + d]: keep the blocks on the diagonal of a [A, H*D] product.
__global__ void ca_block_diag_kernel(precision_t* __restrict__ dst, const precision_t* __restrict__ blk) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= CA_A * CA_D) return;
    int r = i / CA_D, d = i - r * CA_D;
    dst[i] = blk[r * CA_HD + (r / CA_DH) * CA_D + d];
}

// out[M, N] = A[K, M]^T @ B[K, N], for the weight gradients. cuBLAS is slow when K is huge and M, N are tiny
// (here K is batch x rows, up to millions), so: each block sums one chunk of K into a float partial, then
// a second kernel adds the partials.
static constexpr int CA_TN_TILE = 32;
static constexpr int CA_TN_MAX_SPLIT = 256;

__global__ void __launch_bounds__(256) ca_tn_partial_kernel(float* __restrict__ part,
        const precision_t* __restrict__ A, const precision_t* __restrict__ Bm,
        int64_t K, int M, int N, int64_t chunk) {
    __shared__ float As[CA_TN_TILE][CA_TN_TILE + 1];
    __shared__ float Bs[CA_TN_TILE][CA_TN_TILE + 1];
    int split = blockIdx.z;
    int m0 = blockIdx.x * CA_TN_TILE, n0 = blockIdx.y * CA_TN_TILE;
    int tid = threadIdx.x;
    int tm = tid >> 3, tn = (tid & 7) * 4;
    float acc[4] = {0.0f, 0.0f, 0.0f, 0.0f};
    int64_t k0 = (int64_t)split * chunk;
    int64_t k1 = k0 + chunk < K ? k0 + chunk : K;
    for (int64_t kb = k0; kb < k1; kb += CA_TN_TILE) {
        for (int i = tid; i < CA_TN_TILE * CA_TN_TILE; i += 256) {
            int r = i / CA_TN_TILE, c = i - r * CA_TN_TILE;
            int64_t k = kb + r;
            As[r][c] = (k < k1 && m0 + c < M) ? to_float(A[k * M + m0 + c]) : 0.0f;
            Bs[r][c] = (k < k1 && n0 + c < N) ? to_float(Bm[k * N + n0 + c]) : 0.0f;
        }
        __syncthreads();
#pragma unroll 8
        for (int r = 0; r < CA_TN_TILE; r++) {
            float a = As[r][tm];
            acc[0] += a * Bs[r][tn];
            acc[1] += a * Bs[r][tn + 1];
            acc[2] += a * Bs[r][tn + 2];
            acc[3] += a * Bs[r][tn + 3];
        }
        __syncthreads();
    }
    int m = m0 + tm;
    for (int j = 0; j < 4; j++) {
        int n = n0 + tn + j;
        if (m < M && n < N) part[((int64_t)split * M + m) * N + n] = acc[j];
    }
}

__global__ void ca_tn_reduce_kernel(precision_t* __restrict__ out, const float* __restrict__ part,
        int splits, int MN) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= MN) return;
    float acc = 0.0f;
    for (int s = 0; s < splits; s++) acc += part[(int64_t)s * MN + i];
    out[i] = from_float(acc);
}

// out = a^T b, with a [K, M] and b [K, N] contiguous; part is [CA_TN_MAX_SPLIT, at least M*N] floats.
static void ca_mm_tn(const Prec* a, const Prec* b, Prec* out, int64_t K, int M, int N, Float* part,
        cudaStream_t stream) {
    assert((int64_t)M * N <= part->shape[1]);
    int64_t splits = (K + 2047) / 2048;
    if (splits > CA_TN_MAX_SPLIT) splits = CA_TN_MAX_SPLIT;
    if (splits < 1) splits = 1;
    int64_t chunk = (K + splits - 1) / splits;
    chunk = (chunk + CA_TN_TILE - 1) / CA_TN_TILE * CA_TN_TILE;
    splits = (K + chunk - 1) / chunk;
    if (splits < 1) splits = 1;
    dim3 grid((M + CA_TN_TILE - 1) / CA_TN_TILE, (N + CA_TN_TILE - 1) / CA_TN_TILE, (unsigned)splits);
    ca_tn_partial_kernel<<<grid, 256, 0, stream>>>(part->data, a->data, b->data, K, M, N, chunk);
    ca_tn_reduce_kernel<<<grid_size(M * N), BLOCK_SIZE, 0, stream>>>(out->data, part->data, (int)splits, M * N);
}

// Shared memory of both attention kernels. Xs holds relu'd tokens with padding rows zeroed.
struct CaSmem {
    precision_t* Xs;   // [N, CA_XS]
    float* AL;         // [H, N] scores, then softmax weights
    float* DS;         // [H, N] backward only
    float* qks;        // [H, D] (Wk_h^T q_h) / sqrt(DH)
    float* v1;         // [H, D] z (forward) or dz (backward)
    float* v2;         // [H, D] backward: dqk, scaled
    unsigned char* real;  // [N]
};

static size_t ca_smem_bytes(bool backward) {
    size_t n = (size_t)CA_N_TOK * CA_XS * sizeof(precision_t);
    n = (n + 15) & ~(size_t)15;
    n += (size_t)CA_H * CA_N_TOK * sizeof(float) * (backward ? 2 : 1);
    n += (size_t)CA_HD * sizeof(float) * 3;
    n += CA_N_TOK;
    return n;
}

__device__ __forceinline__ CaSmem ca_smem(char* base, bool backward) {
    CaSmem s;
    size_t n = (size_t)CA_N_TOK * CA_XS * sizeof(precision_t);
    n = (n + 15) & ~(size_t)15;
    s.Xs = (precision_t*)base;
    s.AL = (float*)(base + n);
    s.DS = s.AL + CA_H * CA_N_TOK;
    float* f = s.AL + CA_H * CA_N_TOK * (backward ? 2 : 1);
    s.qks = f;
    s.v1 = f + CA_HD;
    s.v2 = f + 2 * CA_HD;
    s.real = (unsigned char*)(f + 3 * CA_HD);
    return s;
}

// Load tokens, compute (Wk_h^T q_h)/sqrt(DH), the scores, and the masked softmax into s.AL.
__device__ void ca_attention_weights(CaSmem s, int b, const CaTabs& xpre, const CaTabs& ents,
        const precision_t* __restrict__ q, const precision_t* __restrict__ wk) {
    int tid = threadIdx.x;
    for (int i = tid; i < CA_N_TOK; i += CA_THREADS) {
        int t, r;
        ca_token(i, t, r);
        s.real[i] = to_float(ents.p[t][((int64_t)b * ca_tab_rows_d[t] + r) * ca_tab_w_d[t]]) > 0.5f;
    }
    __syncthreads();
    for (int idx = tid; idx < CA_N_TOK * CA_D; idx += CA_THREADS) {
        int i = idx / CA_D, d = idx - i * CA_D;
        int t, r;
        ca_token(i, t, r);
        float v = to_float(xpre.p[t][((int64_t)b * ca_tab_rows_d[t] + r) * CA_D + d]);
        s.Xs[i * CA_XS + d] = from_float((s.real[i] && v > 0.0f) ? v : 0.0f);
    }
    const float scale = rsqrtf((float)CA_DH);
    for (int idx = tid; idx < CA_HD; idx += CA_THREADS) {
        int h = idx / CA_D, d = idx - h * CA_D;
        float acc = 0.0f;
#pragma unroll
        for (int a = 0; a < CA_DH; a++) {
            acc += to_float(q[(int64_t)b * CA_A + h * CA_DH + a]) * to_float(wk[(h * CA_DH + a) * CA_D + d]);
        }
        s.qks[idx] = acc * scale;
    }
    __syncthreads();
    for (int i = tid; i < CA_N_TOK; i += CA_THREADS) {
        if (!s.real[i]) {
            for (int h = 0; h < CA_H; h++) s.AL[h * CA_N_TOK + i] = -INFINITY;
            continue;
        }
        float x[CA_D];
#pragma unroll
        for (int d = 0; d < CA_D; d++) x[d] = to_float(s.Xs[i * CA_XS + d]);
#pragma unroll
        for (int h = 0; h < CA_H; h++) {
            float acc = 0.0f;
#pragma unroll
            for (int d = 0; d < CA_D; d++) acc += s.qks[h * CA_D + d] * x[d];
            s.AL[h * CA_N_TOK + i] = acc;
        }
    }
    __syncthreads();
    // One warp per head at a time.
    int warp = tid >> 5, lane = tid & 31;
    for (int h = warp; h < CA_H; h += CA_WARPS) {
        float* row = s.AL + h * CA_N_TOK;
        float m = -INFINITY;
        for (int i = lane; i < CA_N_TOK; i += 32) m = fmaxf(m, row[i]);
        for (int o = 16; o > 0; o >>= 1) m = fmaxf(m, __shfl_xor_sync(0xffffffff, m, o));
        float sum = 0.0f;
        for (int i = lane; i < CA_N_TOK; i += 32) {
            float e = (m == -INFINITY || row[i] == -INFINITY) ? 0.0f : expf(row[i] - m);
            row[i] = e;
            sum += e;
        }
        for (int o = 16; o > 0; o >>= 1) sum += __shfl_xor_sync(0xffffffff, sum, o);
        float inv = sum > 0.0f ? 1.0f / sum : 0.0f;
        for (int i = lane; i < CA_N_TOK; i += 32) row[i] *= inv;
    }
    __syncthreads();
}

// sum_i w[i] x_i[d], with four independent sums so the loop is not one long chain.
__device__ __forceinline__ float ca_weighted_sum(const float* w, const precision_t* Xs, int d) {
    float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
    int i = 0;
    for (; i + 4 <= CA_N_TOK; i += 4) {
        a0 += w[i] * to_float(Xs[i * CA_XS + d]);
        a1 += w[i + 1] * to_float(Xs[(i + 1) * CA_XS + d]);
        a2 += w[i + 2] * to_float(Xs[(i + 2) * CA_XS + d]);
        a3 += w[i + 3] * to_float(Xs[(i + 3) * CA_XS + d]);
    }
    for (; i < CA_N_TOK; i++) a0 += w[i] * to_float(Xs[i * CA_XS + d]);
    return (a0 + a1) + (a2 + a3);
}

// z[h][d] = sum_i a_hi x_i[d]
__device__ __forceinline__ float ca_z(const CaSmem& s, int h, int d) {
    return ca_weighted_sum(s.AL + h * CA_N_TOK, s.Xs, d);
}

__global__ void __launch_bounds__(CA_THREADS) ca_attn_fwd_kernel(
        precision_t* __restrict__ pooled, CaTabs xpre, CaTabs ents,
        const precision_t* __restrict__ q, const precision_t* __restrict__ c,
        const precision_t* __restrict__ wk, const precision_t* __restrict__ wv, int B) {
    extern __shared__ __align__(16) char ca_smem_raw[];
    int b = blockIdx.x;
    if (b >= B) return;
    CaSmem s = ca_smem(ca_smem_raw, false);
    ca_attention_weights(s, b, xpre, ents, q, wk);
    int tid = threadIdx.x;
    for (int idx = tid; idx < CA_HD; idx += CA_THREADS) s.v1[idx] = ca_z(s, idx / CA_D, idx % CA_D);
    __syncthreads();
    for (int idx = tid; idx < CA_A; idx += CA_THREADS) {
        int h = idx / CA_DH;
        float acc = 0.0f;
#pragma unroll
        for (int d = 0; d < CA_D; d++) acc += to_float(wv[idx * CA_D + d]) * s.v1[h * CA_D + d];
        pooled[(int64_t)b * CA_P + idx] = from_float(acc);
    }
    for (int d = tid; d < CA_D; d += CA_THREADS) {
        pooled[(int64_t)b * CA_P + CA_A + d] = c[(int64_t)b * CA_D + d];
    }
}

__global__ void __launch_bounds__(CA_THREADS) ca_attn_bwd_kernel(
        CaTabs dx, precision_t* __restrict__ z_out, precision_t* __restrict__ dqk_out,
        precision_t* __restrict__ dq_out, precision_t* __restrict__ dy_out,
        CaTabs xpre, CaTabs ents, const precision_t* __restrict__ q,
        const precision_t* __restrict__ wk, const precision_t* __restrict__ wv,
        const precision_t* __restrict__ dpooled, int B) {
    extern __shared__ __align__(16) char ca_smem_raw[];
    int b = blockIdx.x;
    if (b >= B) return;
    CaSmem s = ca_smem(ca_smem_raw, true);
    ca_attention_weights(s, b, xpre, ents, q, wk);
    int tid = threadIdx.x;
    const precision_t* dp = dpooled + (int64_t)b * CA_P;
    for (int idx = tid; idx < CA_HD; idx += CA_THREADS) {
        int h = idx / CA_D, d = idx - h * CA_D;
        z_out[(int64_t)b * CA_HD + idx] = from_float(ca_z(s, h, d));
        // dz[h][d] = sum_a Wv[h*DH+a][d] dy[h*DH+a]
        float acc = 0.0f;
#pragma unroll
        for (int a = 0; a < CA_DH; a++) acc += to_float(wv[(h * CA_DH + a) * CA_D + d]) * to_float(dp[h * CA_DH + a]);
        s.v1[idx] = acc;
    }
    for (int idx = tid; idx < CA_A; idx += CA_THREADS) dy_out[(int64_t)b * CA_A + idx] = dp[idx];
    __syncthreads();
    // d(weight) for each head and row: dz_h . x_i
    for (int i = tid; i < CA_N_TOK; i += CA_THREADS) {
        float x[CA_D];
#pragma unroll
        for (int d = 0; d < CA_D; d++) x[d] = to_float(s.Xs[i * CA_XS + d]);
#pragma unroll
        for (int h = 0; h < CA_H; h++) {
            float acc = 0.0f;
#pragma unroll
            for (int d = 0; d < CA_D; d++) acc += s.v1[h * CA_D + d] * x[d];
            s.DS[h * CA_N_TOK + i] = acc;
        }
    }
    __syncthreads();
    // Through the softmax: ds = a * (da - sum_j a_j da_j)
    int warp = tid >> 5, lane = tid & 31;
    for (int h = warp; h < CA_H; h += CA_WARPS) {
        const float* a = s.AL + h * CA_N_TOK;
        float* g = s.DS + h * CA_N_TOK;
        float r = 0.0f;
        for (int i = lane; i < CA_N_TOK; i += 32) r += a[i] * g[i];
        for (int o = 16; o > 0; o >>= 1) r += __shfl_xor_sync(0xffffffff, r, o);
#ifdef CA_SEEDED_ERROR
        r = 0.0f;  // a deliberate bug, for the reference test to catch: drops the softmax's sum term
#endif
        for (int i = lane; i < CA_N_TOK; i += 32) g[i] = a[i] * (g[i] - r);
    }
    __syncthreads();
    const float scale = rsqrtf((float)CA_DH);
    // dqk[h][d] = scale * sum_i ds_hi x_i[d]   (gradient for the unscaled Wk_h^T q_h)
    for (int idx = tid; idx < CA_HD; idx += CA_THREADS) {
        int h = idx / CA_D, d = idx - h * CA_D;
        float acc = ca_weighted_sum(s.DS + h * CA_N_TOK, s.Xs, d) * scale;
        s.v2[idx] = acc;
        dqk_out[(int64_t)b * CA_HD + idx] = from_float(acc);
    }
    // dx_i[d] = sum_h a_hi dz_h[d] + ds_hi qks_h[d], through the ReLU; 0 for padding rows
    for (int idx = tid; idx < CA_N_TOK * CA_D; idx += CA_THREADS) {
        int i = idx / CA_D, d = idx - i * CA_D;
        float g = 0.0f;
        if (to_float(s.Xs[i * CA_XS + d]) > 0.0f) {
#pragma unroll
            for (int h = 0; h < CA_H; h++) {
                g += s.AL[h * CA_N_TOK + i] * s.v1[h * CA_D + d] + s.DS[h * CA_N_TOK + i] * s.qks[h * CA_D + d];
            }
        }
        int t, r;
        ca_token(i, t, r);
        dx.p[t][((int64_t)b * ca_tab_rows_d[t] + r) * CA_D + d] = from_float(g);
    }
    __syncthreads();
    // dq[h*DH+a] = sum_d Wk[h*DH+a][d] dqk[h][d]
    for (int idx = tid; idx < CA_A; idx += CA_THREADS) {
        int h = idx / CA_DH;
        float acc = 0.0f;
#pragma unroll
        for (int d = 0; d < CA_D; d++) acc += to_float(wk[idx * CA_D + d]) * s.v2[h * CA_D + d];
        dq_out[(int64_t)b * CA_A + idx] = from_float(acc);
    }
}

static void ca_set_smem_limit(const void* fn, size_t bytes) {
    if (bytes > 48 * 1024) {
        cudaFuncSetAttribute(fn, cudaFuncAttributeMaxDynamicSharedMemorySize, (int)bytes);
    }
}

static void ca_gather(Prec* dst, int dst_stride, int dst_off, Prec* obs, int obs_size, int off, int n,
        int B, cudaStream_t stream) {
    int64_t total = (int64_t)B * n;
    int blocks = (int)((total + BLOCK_SIZE - 1) / BLOCK_SIZE);
    ca_gather_kernel<<<blocks, BLOCK_SIZE, 0, stream>>>(dst->data, dst_stride, dst_off, obs->data,
        obs_size, off, n, B);
}

static Prec ca_view(Prec* p, int64_t d0, int64_t d1, int64_t d2 = 0) {
    Prec v = {.data = p->data, .shape = {d0, d1, d2}};
    return v;
}

#ifdef CA_PROFILE
static cudaEvent_t ca_ev[12];
static float ca_prof_ms[12];
static void ca_mark(int i, cudaStream_t s) {
    if (!ca_ev[0]) for (int k = 0; k < 12; k++) cudaEventCreate(&ca_ev[k]);
    cudaEventRecord(ca_ev[i], s);
}
static void ca_prof_collect(int k0, int n) {
    cudaEventSynchronize(ca_ev[n - 1]);
    for (int k = k0 + 1; k < n; k++) { float ms; cudaEventElapsedTime(&ms, ca_ev[k - 1], ca_ev[k]); ca_prof_ms[k] += ms; }
}
#define CA_MARK(i) ca_mark(i, stream)
#else
#define CA_MARK(i)
#endif

static Prec ca_forward(void* vw, void* va, Prec input, cudaStream_t stream) {
    CaWeights* w = (CaWeights*)vw;
    CaActs* a = (CaActs*)va;
    int B = input.shape[0];
    assert(input.shape[1] == CA_OBS_SIZE && "attention encoder: observation size does not match the layout");
    CA_MARK(5);
    int at = 0;
    for (int k = 0; k < CA_N_CTX; k++) {
        ca_gather(&a->ctx_in, CA_CTX_W, at, &input, CA_OBS_SIZE, CA_CTX_OFF[k], CA_CTX_WS[k], B, stream);
        at += CA_CTX_WS[k];
    }
    Prec ctx_in = ca_view(&a->ctx_in, B, CA_CTX_W);
    Prec cpre = ca_view(&a->cpre, B, CA_D);
    puf_mm(&ctx_in, &w->w_ctx, &cpre, stream);
    ca_relu_kernel<<<grid_size(B * CA_D), BLOCK_SIZE, 0, stream>>>(a->c.data, a->cpre.data, B * CA_D);
    Prec c = ca_view(&a->c, B, CA_D);
    Prec q = ca_view(&a->q, B, CA_A);
    puf_mm(&c, &w->wq, &q, stream);
    CA_MARK(6);
    for (int t = 0; t < CA_N_TAB; t++) {
        int n = CA_TAB_ROWS[t] * CA_TAB_W[t];
        ca_gather(&a->ents[t], n, 0, &input, CA_OBS_SIZE, CA_TAB_OFF[t], n, B, stream);
        Prec e = ca_view(&a->ents[t], B, CA_TAB_ROWS[t], CA_TAB_W[t]);
        Prec x = ca_view(&a->xpre[t], B, CA_TAB_ROWS[t], CA_D);
        puf_mm(&e, &w->w_tab[t], &x, stream);
    }
    CA_MARK(7);
    size_t smem = ca_smem_bytes(false);
    ca_set_smem_limit((const void*)ca_attn_fwd_kernel, smem);
    ca_attn_fwd_kernel<<<B, CA_THREADS, smem, stream>>>(a->pooled.data, ca_tabs(a->xpre), ca_tabs(a->ents),
        a->q.data, a->c.data, w->wk.data, w->wv.data, B);
    CA_MARK(8);
    Prec pooled = ca_view(&a->pooled, B, CA_P);
    Prec out = ca_view(&a->out, B, w->hidden);
    puf_mm(&pooled, &w->wout, &out, stream);
    CA_MARK(9);
#ifdef CA_PROFILE
    ca_prof_collect(5, 10);
#endif
    return out;
}


static void ca_backward(void* vw, void* va, Prec grad, cudaStream_t stream) {
    CaWeights* w = (CaWeights*)vw;
    CaActs* a = (CaActs*)va;
    int B = grad.shape[0];
    Prec g = ca_view(&grad, B, w->hidden);
    Prec pooled = ca_view(&a->pooled, B, CA_P);
    Prec dpooled = ca_view(&a->dpooled, B, CA_P);
    CA_MARK(0);
    ca_mm_tn(&g, &pooled, &a->gout, B, w->hidden, CA_P, &a->part, stream);
    puf_mm_nn(&g, &w->wout, &dpooled, stream);
    CA_MARK(1);

    size_t smem = ca_smem_bytes(true);
    ca_set_smem_limit((const void*)ca_attn_bwd_kernel, smem);
    ca_attn_bwd_kernel<<<B, CA_THREADS, smem, stream>>>(ca_tabs(a->dx), a->z.data, a->dqk.data, a->dq.data,
        a->dy.data, ca_tabs(a->xpre), ca_tabs(a->ents), a->q.data, w->wk.data, w->wv.data, a->dpooled.data, B);
    CA_MARK(2);

    Prec dy = ca_view(&a->dy, B, CA_A);
    Prec z = ca_view(&a->z, B, CA_HD);
    Prec q = ca_view(&a->q, B, CA_A);
    Prec dqk = ca_view(&a->dqk, B, CA_HD);
    Prec dq = ca_view(&a->dq, B, CA_A);
    Prec c = ca_view(&a->c, B, CA_D);
    Prec dc = ca_view(&a->dc, B, CA_D);
    ca_mm_tn(&dy, &z, &a->blk, B, CA_A, CA_HD, &a->part, stream);
    ca_block_diag_kernel<<<grid_size(CA_A * CA_D), BLOCK_SIZE, 0, stream>>>(a->gv.data, a->blk.data);
    ca_mm_tn(&q, &dqk, &a->blk, B, CA_A, CA_HD, &a->part, stream);
    ca_block_diag_kernel<<<grid_size(CA_A * CA_D), BLOCK_SIZE, 0, stream>>>(a->gk.data, a->blk.data);
    ca_mm_tn(&dq, &c, &a->gq, B, CA_A, CA_D, &a->part, stream);
    puf_mm_nn(&dq, &w->wq, &dc, stream);
    ca_ctx_grad_kernel<<<grid_size(B * CA_D), BLOCK_SIZE, 0, stream>>>(a->dc.data, a->dpooled.data,
        a->cpre.data, B);
    Prec ctx_in = ca_view(&a->ctx_in, B, CA_CTX_W);
    ca_mm_tn(&dc, &ctx_in, &a->g_ctx, B, CA_D, CA_CTX_W, &a->part, stream);
    CA_MARK(3);
    for (int t = 0; t < CA_N_TAB; t++) {
        Prec d = ca_view(&a->dx[t], B, CA_TAB_ROWS[t], CA_D);
        Prec e = ca_view(&a->ents[t], B, CA_TAB_ROWS[t], CA_TAB_W[t]);
        ca_mm_tn(&d, &e, &a->g_tab[t], (int64_t)B * CA_TAB_ROWS[t], CA_D, CA_TAB_W[t], &a->part, stream);
    }
    CA_MARK(4);
#ifdef CA_PROFILE
    ca_prof_collect(0, 5);
#endif
}

static void ca_init_weights(void* vw, uint64_t* seed, cudaStream_t stream) {
    CaWeights* w = (CaWeights*)vw;
    puf_kaiming_init(&w->w_ctx, sqrtf(2.0f), (*seed)++, stream);
    for (int t = 0; t < CA_N_TAB; t++) puf_kaiming_init(&w->w_tab[t], sqrtf(2.0f), (*seed)++, stream);
    puf_kaiming_init(&w->wq, 1.0f, (*seed)++, stream);
    puf_kaiming_init(&w->wk, 1.0f, (*seed)++, stream);
    puf_kaiming_init(&w->wv, 1.0f, (*seed)++, stream);
    puf_kaiming_init(&w->wout, 1.0f, (*seed)++, stream);
}

// The order here is the checkpoint's order, and ca_reg_train registers gradients in the same order.
static void ca_reg_params(void* vw, Allocator* alloc) {
    CaWeights* w = (CaWeights*)vw;
    w->w_ctx = {.shape = {CA_D, CA_CTX_W}};
    alloc_register(alloc, &w->w_ctx);
    for (int t = 0; t < CA_N_TAB; t++) {
        w->w_tab[t] = {.shape = {CA_D, CA_TAB_W[t]}};
        alloc_register(alloc, &w->w_tab[t]);
    }
    w->wq = {.shape = {CA_A, CA_D}};
    w->wk = {.shape = {CA_A, CA_D}};
    w->wv = {.shape = {CA_A, CA_D}};
    w->wout = {.shape = {w->hidden, CA_P}};
    alloc_register(alloc, &w->wq);
    alloc_register(alloc, &w->wk);
    alloc_register(alloc, &w->wv);
    alloc_register(alloc, &w->wout);
}

static void ca_reg_forward(CaWeights* w, CaActs* a, Allocator* acts, int B) {
    a->ctx_in = {.shape = {B, CA_CTX_W}};
    a->cpre = {.shape = {B, CA_D}};
    a->c = {.shape = {B, CA_D}};
    a->q = {.shape = {B, CA_A}};
    a->pooled = {.shape = {B, CA_P}};
    a->out = {.shape = {B, w->hidden}};
    alloc_register(acts, &a->ctx_in);
    alloc_register(acts, &a->cpre);
    alloc_register(acts, &a->c);
    alloc_register(acts, &a->q);
    alloc_register(acts, &a->pooled);
    alloc_register(acts, &a->out);
    for (int t = 0; t < CA_N_TAB; t++) {
        a->ents[t] = {.shape = {B, CA_TAB_ROWS[t], CA_TAB_W[t]}};
        a->xpre[t] = {.shape = {B, CA_TAB_ROWS[t], CA_D}};
        alloc_register(acts, &a->ents[t]);
        alloc_register(acts, &a->xpre[t]);
    }
}

static void ca_reg_train(void* vw, void* va, Allocator* acts, Allocator* grads, int B_TT) {
    CaWeights* w = (CaWeights*)vw;
    CaActs* a = (CaActs*)va;
    *a = {};
    ca_reg_forward(w, a, acts, B_TT);
    a->dpooled = {.shape = {B_TT, CA_P}};
    a->dy = {.shape = {B_TT, CA_A}};
    a->z = {.shape = {B_TT, CA_HD}};
    a->dqk = {.shape = {B_TT, CA_HD}};
    a->dq = {.shape = {B_TT, CA_A}};
    a->dc = {.shape = {B_TT, CA_D}};
    a->blk = {.shape = {CA_A, CA_HD}};
    alloc_register(acts, &a->dpooled);
    alloc_register(acts, &a->dy);
    alloc_register(acts, &a->z);
    alloc_register(acts, &a->dqk);
    alloc_register(acts, &a->dq);
    alloc_register(acts, &a->dc);
    alloc_register(acts, &a->blk);
    int64_t cap = std::max<int64_t>(std::max<int64_t>(CA_A * CA_HD, (int64_t)w->hidden * CA_P), CA_D * CA_CTX_W);
    for (int t = 0; t < CA_N_TAB; t++) cap = std::max<int64_t>(cap, CA_D * CA_TAB_W[t]);
    a->part = {.shape = {CA_TN_MAX_SPLIT, cap}};
    alloc_register(acts, &a->part);
    for (int t = 0; t < CA_N_TAB; t++) {
        a->dx[t] = {.shape = {B_TT, CA_TAB_ROWS[t], CA_D}};
        alloc_register(acts, &a->dx[t]);
    }
    a->g_ctx = {.shape = {CA_D, CA_CTX_W}};
    alloc_register(grads, &a->g_ctx);
    for (int t = 0; t < CA_N_TAB; t++) {
        a->g_tab[t] = {.shape = {CA_D, CA_TAB_W[t]}};
        alloc_register(grads, &a->g_tab[t]);
    }
    a->gq = {.shape = {CA_A, CA_D}};
    a->gk = {.shape = {CA_A, CA_D}};
    a->gv = {.shape = {CA_A, CA_D}};
    a->gout = {.shape = {w->hidden, CA_P}};
    alloc_register(grads, &a->gq);
    alloc_register(grads, &a->gk);
    alloc_register(grads, &a->gv);
    alloc_register(grads, &a->gout);
}

static void ca_reg_rollout(void* vw, void* va, Allocator* alloc, int B) {
    CaWeights* w = (CaWeights*)vw;
    CaActs* a = (CaActs*)va;
    *a = {};
    ca_reg_forward(w, a, alloc, B);
}

static void* ca_create_weights(void* self) {
    Encoder* e = (Encoder*)self;
    assert(e->in_dim == CA_OBS_SIZE && "attention encoder: obs size does not match attention_layout.h");
    CaWeights* w = (CaWeights*)calloc(1, sizeof(CaWeights));
    w->obs_size = e->in_dim;
    w->hidden = e->out_dim;
    return w;
}

static void create_charter_attn_encoder(Encoder* enc) {
    *enc = Encoder{
        .forward = ca_forward,
        .backward = ca_backward,
        .init_weights = ca_init_weights,
        .reg_params = ca_reg_params,
        .reg_train = ca_reg_train,
        .reg_rollout = ca_reg_rollout,
        .create_weights = ca_create_weights,
        .in_dim = enc->in_dim, .out_dim = enc->out_dim,
        .activation_size = sizeof(CaActs),
    };
}
