// Charter entity encoder: one small shared layer per table, a mean over the
// table's real rows, then one layer to the hidden size.
//
//   for each table t:  h[r]   = relu(W_t x[r])                 (E numbers per row)
//                      p_t    = mean of h[r] over rows with x[r][0] = 1, or 0 if none
//   out                       = W_out [p_0, ..., p_8]
//
// No biases: column 0 of every real row is 1, so it plays that part.
// Same shape as ocean/asteroids/asteroids.cu, with a masked mean instead of a
// max. With a mean, W_out can sit after the pool, which saves a layer per row.
// rl/entity/entity_torch.py is the reference this file must match.
// Included by src/ocean.cu. Needs precision_t, Prec, Allocator, puf_mm, etc.

// Written by rl/entity/gen_layout.py from rl/layout.json: CE_NUM_TABLES, CE_OBS_SIZE,
// CE_TOTAL_ROWS and the lists CE_OFF_LIST, CE_ROWS_LIST, CE_WIDTH_LIST, CE_ROWSTART_LIST.
#include "charter_entity_layout.h"

static constexpr int CE_E = 32;  // numbers per row after the shared layer

// The reference test builds with CE_SEEDED_ERROR=1 (padding rows counted in the
// mean) and =2 (padding rows get gradient) to show it catches each one.
#ifndef CE_SEEDED_ERROR
#define CE_SEEDED_ERROR 0
#endif

struct CharterEntityWeights {
    Prec w_in[CE_NUM_TABLES];
    Prec w_out;
    int obs_size, hidden;
};

struct CharterEntityActivations {
    Prec ent_in;    // obs regrouped table by table: block t is (B, rows_t, width_t)
    Prec ent_h;     // W_t x before relu: block t is (B, rows_t, E)
    Prec count;     // real rows per (b, t), at least 1: (B, T)
    Prec pooled;    // (B, T*E)
    Prec out;       // (B, H)
    Prec grad_pooled, grad_h;
    Prec w_in_grad[CE_NUM_TABLES];
    Prec w_out_grad;
};

// Fixed at compile time, so nothing is copied to the GPU during a captured graph.
static constexpr int CE_OFF[CE_NUM_TABLES] = CE_OFF_LIST;
static constexpr int CE_ROWS[CE_NUM_TABLES] = CE_ROWS_LIST;
static constexpr int CE_WIDTH[CE_NUM_TABLES] = CE_WIDTH_LIST;
static constexpr int CE_ROWSTART[CE_NUM_TABLES] = CE_ROWSTART_LIST;  // rows before table t
__constant__ int ce_off_dev[CE_NUM_TABLES] = CE_OFF_LIST;
__constant__ int ce_rows_dev[CE_NUM_TABLES] = CE_ROWS_LIST;
__constant__ int ce_width_dev[CE_NUM_TABLES] = CE_WIDTH_LIST;
__constant__ int ce_rowstart_dev[CE_NUM_TABLES] = CE_ROWSTART_LIST;

// Start of table t inside ent_in, and inside ent_h, for batch B.
static inline int64_t ce_in_start(int t, int B) { return (int64_t)B * CE_OFF[t]; }
static inline int64_t ce_h_start(int t, int B) { return (int64_t)CE_ROWSTART[t] * B * CE_E; }

__global__ void ce_regroup_kernel(precision_t* __restrict__ ent_in,
        const precision_t* __restrict__ obs, int B, int obs_size) {
    int64_t idx = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= (int64_t)B * CE_OBS_SIZE) return;
    int b = idx / CE_OBS_SIZE;
    int j = idx - (int64_t)b * CE_OBS_SIZE;
    int t = 0;
    while (t + 1 < CE_NUM_TABLES && j >= ce_off_dev[t + 1]) t++;
    int size = ce_rows_dev[t] * ce_width_dev[t];
    int64_t dst = (int64_t)B * ce_off_dev[t] + (int64_t)b * size + (j - ce_off_dev[t]);
    ent_in[dst] = obs[(int64_t)b * obs_size + j];
}

// One thread per (b, t, e): the masked mean of relu(h) over table t's rows.
__global__ void ce_pool_kernel(precision_t* __restrict__ pooled,
        precision_t* __restrict__ count_out,
        const precision_t* __restrict__ ent_in,
        const precision_t* __restrict__ ent_h, int B) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= B * CE_NUM_TABLES * CE_E) return;
    int e = idx % CE_E;
    int t = (idx / CE_E) % CE_NUM_TABLES;
    int b = idx / (CE_E * CE_NUM_TABLES);
    int rows = ce_rows_dev[t], width = ce_width_dev[t];
    const precision_t* x = ent_in + (int64_t)B * ce_off_dev[t] + (int64_t)b * rows * width;
    const precision_t* h = ent_h + ((int64_t)ce_rowstart_dev[t] * B + (int64_t)b * rows) * CE_E;
    float sum = 0.0f, n = 0.0f;
    for (int r = 0; r < rows; r++) {
        if (CE_SEEDED_ERROR == 1) n += 1.0f;
        if (to_float(x[(int64_t)r * width]) > 0.5f) {
            if (CE_SEEDED_ERROR != 1) n += 1.0f;
            sum += fmaxf(0.0f, to_float(h[(int64_t)r * CE_E + e]));
        }
    }
    n = fmaxf(n, 1.0f);
    pooled[(int64_t)b * CE_NUM_TABLES * CE_E + t * CE_E + e] = from_float(sum / n);
    if (e == 0) count_out[(int64_t)b * CE_NUM_TABLES + t] = from_float(n);
}

// One thread per (t, b, r, e): gradient of the loss with respect to h before relu.
__global__ void ce_unpool_kernel(precision_t* __restrict__ grad_h,
        const precision_t* __restrict__ grad_pooled,
        const precision_t* __restrict__ count,
        const precision_t* __restrict__ ent_in,
        const precision_t* __restrict__ ent_h, int B, int total_rows) {
    int64_t idx = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= (int64_t)B * total_rows * CE_E) return;
    int e = idx % CE_E;
    int64_t row = idx / CE_E;          // row inside ent_h, table-major
    int t = 0;
    while (t + 1 < CE_NUM_TABLES && row >= (int64_t)ce_rowstart_dev[t + 1] * B) t++;
    int64_t local = row - (int64_t)ce_rowstart_dev[t] * B;
    int rows = ce_rows_dev[t], width = ce_width_dev[t];
    int b = local / rows;
    int r = local - (int64_t)b * rows;
    float real = to_float(ent_in[(int64_t)B * ce_off_dev[t] + ((int64_t)b * rows + r) * width]) > 0.5f;
    if (CE_SEEDED_ERROR == 2) real = 1.0f;
    float active = to_float(ent_h[idx]) > 0.0f;
    float g = to_float(grad_pooled[(int64_t)b * CE_NUM_TABLES * CE_E + t * CE_E + e]);
    float n = to_float(count[(int64_t)b * CE_NUM_TABLES + t]);
    grad_h[idx] = from_float(real * active * g / n);
}

static Prec ce_view(Prec& buf, int64_t start, int d0, int d1, int d2) {
    Prec v = {.data = buf.data + start, .shape = {d0, d1, d2}};
    return v;
}

static Prec ce_encoder_forward(void* w, void* activations, Prec input, cudaStream_t stream) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    CharterEntityActivations* a = (CharterEntityActivations*)activations;
    int B = numel(input.shape) / ew->obs_size;
    ce_regroup_kernel<<<grid_size(B * CE_OBS_SIZE), BLOCK_SIZE, 0, stream>>>(
        a->ent_in.data, input.data, B, ew->obs_size);
    for (int t = 0; t < CE_NUM_TABLES; t++) {
        Prec x = ce_view(a->ent_in, ce_in_start(t, B), B, CE_ROWS[t], CE_WIDTH[t]);
        Prec h = ce_view(a->ent_h, ce_h_start(t, B), B, CE_ROWS[t], CE_E);
        puf_mm(&x, &ew->w_in[t], &h, stream);
    }
    ce_pool_kernel<<<grid_size(B * CE_NUM_TABLES * CE_E), BLOCK_SIZE, 0, stream>>>(
        a->pooled.data, a->count.data, a->ent_in.data, a->ent_h.data, B);
    Prec pooled = {.data = a->pooled.data, .shape = {B, CE_NUM_TABLES * CE_E}};
    Prec out = {.data = a->out.data, .shape = {B, ew->hidden}};
    puf_mm(&pooled, &ew->w_out, &out, stream);
    return out;
}

static void ce_encoder_backward(void* w, void* activations, Prec grad, cudaStream_t stream) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    CharterEntityActivations* a = (CharterEntityActivations*)activations;
    int B = numel(grad.shape) / ew->hidden;
    int T_E = CE_NUM_TABLES * CE_E;
    Prec g = {.data = grad.data, .shape = {B, ew->hidden}};
    Prec pooled = {.data = a->pooled.data, .shape = {B, T_E}};
    Prec grad_pooled = {.data = a->grad_pooled.data, .shape = {B, T_E}};
    puf_mm_tn(&g, &pooled, &a->w_out_grad, stream);        // (H, T*E)
    puf_mm_nn(&g, &ew->w_out, &grad_pooled, stream);       // (B, T*E)
    int total_rows = CE_TOTAL_ROWS;
    ce_unpool_kernel<<<grid_size(B * total_rows * CE_E), BLOCK_SIZE, 0, stream>>>(
        a->grad_h.data, a->grad_pooled.data, a->count.data, a->ent_in.data, a->ent_h.data,
        B, total_rows);
    for (int t = 0; t < CE_NUM_TABLES; t++) {
        Prec gh = ce_view(a->grad_h, ce_h_start(t, B), B, CE_ROWS[t], CE_E);
        Prec x = ce_view(a->ent_in, ce_in_start(t, B), B, CE_ROWS[t], CE_WIDTH[t]);
        puf_mm_tn(&gh, &x, &a->w_in_grad[t], stream);       // (E, width_t)
    }
}

static void ce_encoder_init_weights(void* w, uint64_t* seed, cudaStream_t stream) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    for (int t = 0; t < CE_NUM_TABLES; t++) {
        puf_kaiming_init(&ew->w_in[t], std::sqrt(2.0f), (*seed)++, stream);
    }
    puf_kaiming_init(&ew->w_out, 1.0f, (*seed)++, stream);
}

static void ce_encoder_reg_params(void* w, Allocator* alloc) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    for (int t = 0; t < CE_NUM_TABLES; t++) {
        ew->w_in[t] = {.shape = {CE_E, CE_WIDTH[t]}};
        alloc_register(alloc, &ew->w_in[t]);
    }
    ew->w_out = {.shape = {ew->hidden, CE_NUM_TABLES * CE_E}};
    alloc_register(alloc, &ew->w_out);
}

static void ce_reg_forward(CharterEntityWeights* ew, CharterEntityActivations* a,
        Allocator* acts, int B) {
    a->ent_in = {.shape = {B, CE_OBS_SIZE}};
    a->ent_h = {.shape = {B, CE_TOTAL_ROWS, CE_E}};
    a->count = {.shape = {B, CE_NUM_TABLES}};
    a->pooled = {.shape = {B, CE_NUM_TABLES * CE_E}};
    a->out = {.shape = {B, ew->hidden}};
    alloc_register(acts, &a->ent_in);
    alloc_register(acts, &a->ent_h);
    alloc_register(acts, &a->count);
    alloc_register(acts, &a->pooled);
    alloc_register(acts, &a->out);
}

static void ce_encoder_reg_train(void* w, void* activations, Allocator* acts, Allocator* grads, int B_TT) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    CharterEntityActivations* a = (CharterEntityActivations*)activations;
    *a = {};
    ce_reg_forward(ew, a, acts, B_TT);
    a->grad_pooled = {.shape = {B_TT, CE_NUM_TABLES * CE_E}};
    a->grad_h = {.shape = {B_TT, CE_TOTAL_ROWS, CE_E}};
    alloc_register(acts, &a->grad_pooled);
    alloc_register(acts, &a->grad_h);
    // Same order as ce_encoder_reg_params: the optimizer pairs them by position.
    for (int t = 0; t < CE_NUM_TABLES; t++) {
        a->w_in_grad[t] = {.shape = {CE_E, CE_WIDTH[t]}};
        alloc_register(grads, &a->w_in_grad[t]);
    }
    a->w_out_grad = {.shape = {ew->hidden, CE_NUM_TABLES * CE_E}};
    alloc_register(grads, &a->w_out_grad);
}

static void ce_encoder_reg_rollout(void* w, void* activations, Allocator* alloc, int B) {
    CharterEntityWeights* ew = (CharterEntityWeights*)w;
    CharterEntityActivations* a = (CharterEntityActivations*)activations;
    *a = {};
    ce_reg_forward(ew, a, alloc, B);
}

static void* ce_encoder_create_weights(void* self) {
    Encoder* e = (Encoder*)self;
    assert(e->in_dim == CE_OBS_SIZE && "charter entity encoder expects the base observation layout");
    CharterEntityWeights* ew = (CharterEntityWeights*)calloc(1, sizeof(CharterEntityWeights));
    ew->obs_size = e->in_dim;
    ew->hidden = e->out_dim;
    return ew;
}

static void create_charter_entity_encoder(Encoder* enc) {
    *enc = Encoder{
        .forward = ce_encoder_forward,
        .backward = ce_encoder_backward,
        .init_weights = ce_encoder_init_weights,
        .reg_params = ce_encoder_reg_params,
        .reg_train = ce_encoder_reg_train,
        .reg_rollout = ce_encoder_reg_rollout,
        .create_weights = ce_encoder_create_weights,
        .in_dim = enc->in_dim, .out_dim = enc->out_dim,
        .activation_size = sizeof(CharterEntityActivations),
    };
}
