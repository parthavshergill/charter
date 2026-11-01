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

#ifndef CE_ENTITY_DIM
#define CE_ENTITY_DIM 32
#endif
static constexpr int CE_E = CE_ENTITY_DIM;  // numbers per row after the shared layer (-DCE_ENTITY_DIM=N)

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
    Prec ext_grad;  // CE_POINTER, training only: gradient from the decoder on relu(h), same layout as ent_h
};

// The pointer decoder reads the encoder's rows. arch_reg_train and arch_reg_rollout register the encoder's
// activations just before the decoder's, so the decoder takes the ones registered last.
static CharterEntityActivations* ce_last_acts = NULL;

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
        const precision_t* __restrict__ ent_h, int B, int total_rows,
        const precision_t* __restrict__ ext_grad) {
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
    float ext = (ext_grad && CE_SEEDED_ERROR != 3) ? to_float(ext_grad[idx]) : 0.0f;
    grad_h[idx] = from_float(active * (real * g / n + ext));
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
        B, total_rows, a->ext_grad.data);
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
#ifdef CE_POINTER
    a->ext_grad = {.shape = {B_TT, CE_TOTAL_ROWS, CE_E}};
    alloc_register(acts, &a->ext_grad);
#endif
    ce_last_acts = a;
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
    ce_last_acts = a;
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

// ---- Pointer decoder (built with -DCE_POINTER), layout version 2 ----------------------------------------
//
// The plain decoder gives every action one fixed output: logits = W h. A placement is an action by its row of the
// `places` table, and a bank trade by a pair of rows of `resources`, whose order is shuffled each game, so a fixed
// output cannot know what the row holds. The pointer decoder adds a score from those rows, as the encoder saw them
// (r = relu(W_t x), E numbers per row), and a query from the hidden state:
//
//   q_place, q_give, q_get = A h                                              (E numbers each; A is 3E x H)
//   logit(place p)     += q_place . r_places[p]                               at CE_ACT_PLACE + p
//   logit(bank i -> j) += q_give . r_res[i] + q_get . r_res[j]                at CE_ACT_BANK + i * resources + j
//
// Action numbers follow rl/layout.json (rl/lean/CharterRL/Actions.lean). The decoder's gradient on r goes back into
// the encoder through ext_grad. rl/entity/entity_torch.py `pointer_logits` is the reference. (The layout-1 version,
// which scored spots and links, is in this file's history.)
#ifdef CE_POINTER
static constexpr int CE_NPLACE = CE_ROWS[CE_PLACE_TABLE];
static constexpr int CE_NRES = CE_ROWS[CE_RES_TABLE];
static constexpr int CE_NBANK = CE_NRES * CE_NRES;
static constexpr int CE_PQ = 3;
static_assert(CE_ACT_BANK + CE_NBANK <= CE_ACT_PLACE && CE_ACT_PLACE + CE_NPLACE == CE_ACT_SIZE, "layout 2 actions");

struct CharterPointerWeights {
    DecoderWeights base;  // first, so code that reads DecoderWeights (pufferl.cu reads .continuous) still works
    Prec ptr;             // A: (3E, H): place, bank give, bank get
};

struct CharterPointerActivations {
    DecoderActivations base;
    CharterEntityActivations* enc;
    Prec q;        // (B, 3E)
    Prec grad_q;   // (B, 3E), training only
    Prec ptr_wgrad, grad_in2;
};

// relu(h) of row r of table t for sample b, from ent_h laid out table-major.
__device__ __forceinline__ float ce_r(const precision_t* ent_h, int B, int t, int b, int r, int e) {
    float v = to_float(ent_h[((int64_t)ce_rowstart_dev[t] * B + (int64_t)b * ce_rows_dev[t] + r) * CE_E + e]);
    return fmaxf(v, 0.0f);
}

// One thread per (b, place row) and per (b, bank pair): add the pointer score to that action's logit.
__global__ void cp_forward_kernel(precision_t* __restrict__ out, const precision_t* __restrict__ q,
        const precision_t* __restrict__ ent_h, int B, int od1) {
    int64_t idx = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const int per = CE_NPLACE + CE_NBANK;
    if (idx >= (int64_t)B * per) return;
    int b = idx / per, i = idx - (int64_t)b * per;
    const precision_t* qb = q + (int64_t)b * CE_PQ * CE_E;
    float sum = 0.0f;
    int act;
    if (i < CE_NPLACE) {
        for (int e = 0; e < CE_E; e++) sum += to_float(qb[e]) * ce_r(ent_h, B, CE_PLACE_TABLE, b, i, e);
        act = CE_ACT_PLACE + i;
    } else {
        int m = i - CE_NPLACE, gi = m / CE_NRES, gj = m - gi * CE_NRES;
        for (int e = 0; e < CE_E; e++)
            sum += to_float(qb[CE_E + e]) * ce_r(ent_h, B, CE_RES_TABLE, b, gi, e)
                 + to_float(qb[2 * CE_E + e]) * ce_r(ent_h, B, CE_RES_TABLE, b, gj, e);
        act = CE_ACT_BANK + m;
    }
    int64_t o = (int64_t)b * od1 + act;
    out[o] = from_float(to_float(out[o]) + sum);
}

// One thread per (b, e): gradients on q and on every places and resources row's r, for that e.
// G is the assembled logit gradient (B, od1). ext_grad gets d loss / d r (the encoder applies relu').
__global__ void cp_backward_kernel(precision_t* __restrict__ grad_q, precision_t* __restrict__ ext_grad,
        const precision_t* __restrict__ G, const precision_t* __restrict__ q,
        const precision_t* __restrict__ ent_h, int B, int od1) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= B * CE_E) return;
    int b = idx / CE_E, e = idx - b * CE_E;
    const precision_t* g = G + (int64_t)b * od1;
    const precision_t* qb = q + (int64_t)b * CE_PQ * CE_E;
    precision_t* gq = grad_q + (int64_t)b * CE_PQ * CE_E;
    auto ext = [&](int t, int r) -> precision_t& {
        return ext_grad[((int64_t)ce_rowstart_dev[t] * B + (int64_t)b * ce_rows_dev[t] + r) * CE_E + e];
    };
    float qp = to_float(qb[e]), dqp = 0.0f;
    for (int p = 0; p < CE_NPLACE; p++) {
        float gv = to_float(g[CE_ACT_PLACE + p]);
        dqp += gv * ce_r(ent_h, B, CE_PLACE_TABLE, b, p, e);
        ext(CE_PLACE_TABLE, p) = from_float(gv * qp);
    }
    float qg = to_float(qb[CE_E + e]), qt = to_float(qb[2 * CE_E + e]), dqg = 0.0f, dqt = 0.0f;
    float rr[CE_NRES], dr[CE_NRES];
    for (int i = 0; i < CE_NRES; i++) { rr[i] = ce_r(ent_h, B, CE_RES_TABLE, b, i, e); dr[i] = 0.0f; }
    for (int i = 0; i < CE_NRES; i++)
        for (int j = 0; j < CE_NRES; j++) {
            float gv = to_float(g[CE_ACT_BANK + i * CE_NRES + j]);
            dqg += gv * rr[i];
            dqt += gv * rr[j];
            dr[i] += gv * qg;
            dr[j] += gv * qt;
        }
    for (int i = 0; i < CE_NRES; i++) ext(CE_RES_TABLE, i) = from_float(dr[i]);
#if CE_SEEDED_ERROR == 4
    dqp *= 1.5f;  // seeded error: a wrong gradient on A
#endif
    gq[e] = from_float(dqp);
    gq[CE_E + e] = from_float(dqg);
    gq[2 * CE_E + e] = from_float(dqt);
}

static Prec cp_forward(void* w, void* activations, Prec input, cudaStream_t stream) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    CharterPointerActivations* a = (CharterPointerActivations*)activations;
    Prec out = decoder_forward(&cw->base, &a->base, input, stream);
    int B = input.shape[0];
    Prec q = {.data = a->q.data, .shape = {B, CE_PQ * CE_E}};
    puf_mm(&input, &cw->ptr, &q, stream);
    int od1 = cw->base.output_dim + 1;
    cp_forward_kernel<<<grid_size(B * (CE_NPLACE + CE_NBANK)), BLOCK_SIZE, 0, stream>>>(
        out.data, q.data, a->enc->ent_h.data, B, od1);
    return out;
}

static Prec cp_backward(void* w, void* activations, Float grad_logits, Float grad_logstd, Float grad_value,
        cudaStream_t stream) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    CharterPointerActivations* a = (CharterPointerActivations*)activations;
    Prec grad_in = decoder_backward(&cw->base, &a->base, grad_logits, grad_logstd, grad_value, stream);
    int B = a->base.saved_input.shape[0];
    int od1 = cw->base.output_dim + 1;
    // Every places and resources row is written for every (b, e); other tables keep zero.
    cudaMemsetAsync(a->enc->ext_grad.data, 0, numel(a->enc->ext_grad.shape) * sizeof(precision_t), stream);
    cp_backward_kernel<<<grid_size(B * CE_E), BLOCK_SIZE, 0, stream>>>(
        a->grad_q.data, a->enc->ext_grad.data, a->base.grad_out.data, a->q.data, a->enc->ent_h.data, B, od1);
    puf_mm_tn(&a->grad_q, &a->base.saved_input, &a->ptr_wgrad, stream);   // (3E, H)
    puf_mm_nn(&a->grad_q, &cw->ptr, &a->grad_in2, stream);                // (B, H)
    int n = B * cw->base.hidden_dim;
    add_kernel<<<grid_size(n), BLOCK_SIZE, 0, stream>>>(grad_in.data, a->grad_in2.data, n);
    return grad_in;
}

static void cp_init_weights(void* w, ulong* seed, cudaStream_t stream) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    decoder_init_weights(&cw->base, seed, stream);
    puf_kaiming_init(&cw->ptr, 0.1f, (*seed)++, stream);  // small: the pointer starts as a nudge
}

static void cp_reg_params(void* w, Allocator* alloc) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    decoder_reg_params(&cw->base, alloc);
    cw->ptr = {.shape = {CE_PQ * CE_E, cw->base.hidden_dim}};
    alloc_register(alloc, &cw->ptr);
}

static void cp_reg_train(void* w, void* activations, Allocator* acts, Allocator* grads, int B_TT) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    CharterPointerActivations* a = (CharterPointerActivations*)activations;
    assert(!cw->base.continuous && ce_last_acts && ce_last_acts->ext_grad.shape[0] == B_TT);
    decoder_reg_train(&cw->base, &a->base, acts, grads, B_TT);
    a->enc = ce_last_acts;
    a->q = {.shape = {B_TT, CE_PQ * CE_E}};
    a->grad_q = {.shape = {B_TT, CE_PQ * CE_E}};
    a->grad_in2 = {.shape = {B_TT, cw->base.hidden_dim}};
    a->ptr_wgrad = {.shape = {CE_PQ * CE_E, cw->base.hidden_dim}};
    alloc_register(acts, &a->q);
    alloc_register(acts, &a->grad_q);
    alloc_register(acts, &a->grad_in2);
    alloc_register(grads, &a->ptr_wgrad);  // same order as cp_reg_params: the optimizer pairs them by position
}

static void cp_reg_rollout(void* w, void* activations, Allocator* alloc, int B) {
    CharterPointerWeights* cw = (CharterPointerWeights*)w;
    CharterPointerActivations* a = (CharterPointerActivations*)activations;
    assert(ce_last_acts);
    decoder_reg_rollout(&cw->base, &a->base, alloc, B);
    a->enc = ce_last_acts;
    a->q = {.shape = {B, CE_PQ * CE_E}};
    alloc_register(alloc, &a->q);
}

static void* cp_create_weights(void* self) {
    Decoder* d = (Decoder*)self;
    CharterPointerWeights* cw = (CharterPointerWeights*)calloc(1, sizeof(CharterPointerWeights));
    cw->base.hidden_dim = d->hidden_dim;
    cw->base.output_dim = d->output_dim;
    cw->base.continuous = d->continuous;
    assert(d->output_dim == CE_ACT_SIZE + 1 && "the layout's actions and the no-op");
    return cw;
}

static void create_charter_pointer_decoder(Decoder* dec) {
    dec->forward = cp_forward;
    dec->backward = cp_backward;
    dec->init_weights = cp_init_weights;
    dec->reg_params = cp_reg_params;
    dec->reg_train = cp_reg_train;
    dec->reg_rollout = cp_reg_rollout;
    dec->create_weights = cp_create_weights;
    dec->activation_size = sizeof(CharterPointerActivations);
}
#endif
