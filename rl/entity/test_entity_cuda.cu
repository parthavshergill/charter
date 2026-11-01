// Runs the entity encoder alone, on host buffers, for rl/entity/test_reference.py.
// Host buffers are float; on the GPU they are precision_t, so this works for float and bf16 builds.
// Build: nvcc -shared [-DPRECISION_FLOAT] [-DCE_SEEDED_ERROR=1|2] -I <puffer>/src -I <puffer>/vendor
//        -I <raylib>/include -I rl/entity rl/entity/test_entity_cuda.cu ...
#define ENV_HEADER "../ocean/minimal/minimal.h"
#define PUFFER_ENV_NAME "minimal"
#include "../src/pufferl.cu"
#include "charter_entity.cu"

__global__ void ce_to_prec(precision_t* dst, const float* src, int64_t n) {
    int64_t i = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) dst[i] = from_float(src[i]);
}
__global__ void ce_from_prec(float* dst, const precision_t* src, int64_t n) {
    int64_t i = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) dst[i] = to_float(src[i]);
}

// Host float -> device precision_t, and back.
static void ce_put(precision_t* dst, const float* host, int64_t n) {
    float* tmp;
    cudaMalloc(&tmp, n * sizeof(float));
    cudaMemcpy(tmp, host, n * sizeof(float), cudaMemcpyHostToDevice);
    ce_to_prec<<<grid_size(n), BLOCK_SIZE>>>(dst, tmp, n);
    cudaDeviceSynchronize();
    cudaFree(tmp);
}
static void ce_get(float* host, const precision_t* src, int64_t n) {
    float* tmp;
    cudaMalloc(&tmp, n * sizeof(float));
    ce_from_prec<<<grid_size(n), BLOCK_SIZE>>>(tmp, src, n);
    cudaMemcpy(host, tmp, n * sizeof(float), cudaMemcpyDeviceToHost);
    cudaFree(tmp);
}

extern "C" {

static Encoder ce_enc;
static CharterEntityWeights* ce_w;
static CharterEntityActivations* ce_a;
static Allocator ce_params, ce_acts, ce_grads;
static bool ce_cublas_ready;
static int ce_batch;

static void ce_free(Allocator* x) {
    if (x->mem) cudaFree(x->mem);
    free(x->regs);
    *x = {};
}

int ce_test_num_params() { return CE_NUM_TABLES + 1; }

int ce_test_init(int batch, int hidden) {
    ce_free(&ce_params); ce_free(&ce_acts); ce_free(&ce_grads);
    free(ce_w); free(ce_a);
    if (!ce_cublas_ready) { cublas_init_handle(); ce_cublas_ready = true; }
    ce_batch = batch;
    ce_enc = {};
    ce_enc.in_dim = CE_OBS_SIZE;
    ce_enc.out_dim = hidden;
    create_charter_entity_encoder(&ce_enc);
    ce_w = (CharterEntityWeights*)ce_enc.create_weights(&ce_enc);
    ce_enc.reg_params(ce_w, &ce_params);
    alloc_create(&ce_params);
    ce_a = (CharterEntityActivations*)calloc(1, ce_enc.activation_size);
    ce_enc.reg_train(ce_w, ce_a, &ce_acts, &ce_grads, batch);
    alloc_create(&ce_acts);
    alloc_create(&ce_grads);
    uint64_t seed = 1;
    ce_enc.init_weights(ce_w, &seed, 0);
    cudaDeviceSynchronize();
    return CE_OBS_SIZE;
}

static Prec* ce_param(int i) { return i < CE_NUM_TABLES ? &ce_w->w_in[i] : &ce_w->w_out; }
static Prec* ce_grad(int i) { return i < CE_NUM_TABLES ? &ce_a->w_in_grad[i] : &ce_a->w_out_grad; }

void ce_test_param_shape(int i, int* rows, int* cols) {
    *rows = ce_param(i)->shape[0];
    *cols = ce_param(i)->shape[1];
}

void ce_test_set_param(int i, const float* host) {
    Prec* p = ce_param(i);
    ce_put(p->data, host, numel(p->shape));
}

void ce_test_get_param(int i, float* host) {
    Prec* p = ce_param(i);
    ce_get(host, p->data, numel(p->shape));
}

void ce_test_forward(const float* obs_host, float* out_host) {
    int64_t n = (int64_t)ce_batch * CE_OBS_SIZE;
    precision_t* obs;
    cudaMalloc(&obs, n * sizeof(precision_t));
    ce_put(obs, obs_host, n);
    Prec input = {.data = obs, .shape = {ce_batch, CE_OBS_SIZE}};
    Prec out = ce_enc.forward(ce_w, ce_a, input, 0);
    cudaDeviceSynchronize();
    ce_get(out_host, out.data, (int64_t)ce_batch * ce_enc.out_dim);
    cudaFree(obs);
}

void ce_test_backward(const float* grad_host) {
    int64_t n = (int64_t)ce_batch * ce_enc.out_dim;
    precision_t* g;
    cudaMalloc(&g, n * sizeof(precision_t));
    ce_put(g, grad_host, n);
    Prec grad = {.data = g, .shape = {ce_batch, ce_enc.out_dim}};
    ce_enc.backward(ce_w, ce_a, grad, 0);
    cudaDeviceSynchronize();
    cudaFree(g);
}

void ce_test_get_grad(int i, float* host) {
    Prec* p = ce_grad(i);
    ce_get(host, p->data, numel(p->shape));
}

#ifdef CE_POINTER
// The pointer decoder on top of the encoder: h = encoder(obs) goes straight to the decoder (no GRU here).
// Parameters 0..CE_NUM_TABLES are the encoder's, then the decoder's weight, then the pointer block A.
static Decoder cp_dec;
static CharterPointerWeights* cp_w;
static CharterPointerActivations* cp_a;
static Allocator cp_params, cp_acts, cp_grads;

int cp_test_num_params() { return CE_NUM_TABLES + 3; }

int cp_test_init(int batch, int hidden, int act_size) {
    ce_test_init(batch, hidden);  // the encoder; registers its activations last, so the decoder finds them
    ce_free(&cp_params); ce_free(&cp_acts); ce_free(&cp_grads);
    free(cp_w); free(cp_a);
    cp_dec = {};
    cp_dec.hidden_dim = hidden;
    cp_dec.output_dim = act_size;
    cp_dec.continuous = false;
    create_charter_pointer_decoder(&cp_dec);
    cp_w = (CharterPointerWeights*)cp_dec.create_weights(&cp_dec);
    cp_dec.reg_params(cp_w, &cp_params);
    alloc_create(&cp_params);
    cp_a = (CharterPointerActivations*)calloc(1, cp_dec.activation_size);
    cp_dec.reg_train(cp_w, cp_a, &cp_acts, &cp_grads, batch);
    alloc_create(&cp_acts);
    alloc_create(&cp_grads);
    uint64_t seed = 2;
    cp_dec.init_weights(cp_w, &seed, 0);
    cudaDeviceSynchronize();
    return CE_OBS_SIZE;
}

static Prec* cp_param(int i) { return i <= CE_NUM_TABLES ? ce_param(i) : i == CE_NUM_TABLES + 1 ? &cp_w->base.weight : &cp_w->ptr; }
static Prec* cp_grad(int i) { return i <= CE_NUM_TABLES ? ce_grad(i) : i == CE_NUM_TABLES + 1 ? &cp_a->base.wgrad_scratch : &cp_a->ptr_wgrad; }

void cp_test_param_shape(int i, int* rows, int* cols) { *rows = cp_param(i)->shape[0]; *cols = cp_param(i)->shape[1]; }
void cp_test_set_param(int i, const float* host) { ce_put(cp_param(i)->data, host, numel(cp_param(i)->shape)); }
void cp_test_get_grad(int i, float* host) { ce_get(host, cp_grad(i)->data, numel(cp_grad(i)->shape)); }

// logits_host: (batch, act_size + 1), the last column the value.
void cp_test_forward(const float* obs_host, float* logits_host) {
    int64_t n = (int64_t)ce_batch * CE_OBS_SIZE;
    precision_t* obs;
    cudaMalloc(&obs, n * sizeof(precision_t));
    ce_put(obs, obs_host, n);
    Prec input = {.data = obs, .shape = {ce_batch, CE_OBS_SIZE}};
    Prec h = ce_enc.forward(ce_w, ce_a, input, 0);
    Prec out = cp_dec.forward(cp_w, cp_a, h, 0);
    cudaDeviceSynchronize();
    ce_get(logits_host, out.data, (int64_t)ce_batch * (cp_dec.output_dim + 1));
    cudaFree(obs);
}

// grad_logits: (batch, act_size) and grad_value: (batch), in float, as PufferLib's loss gives them.
void cp_test_backward(const float* grad_logits_host, const float* grad_value_host) {
    int64_t n = (int64_t)ce_batch * cp_dec.output_dim;
    float *gl, *gv;
    cudaMalloc(&gl, n * sizeof(float));
    cudaMalloc(&gv, ce_batch * sizeof(float));
    cudaMemcpy(gl, grad_logits_host, n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(gv, grad_value_host, ce_batch * sizeof(float), cudaMemcpyHostToDevice);
    Float grad_logits = {.data = gl, .shape = {ce_batch, cp_dec.output_dim}};
    Float grad_value = {.data = gv, .shape = {ce_batch}};
    Float none = {};
    Prec grad_h = cp_dec.backward(cp_w, cp_a, grad_logits, none, grad_value, 0);
    ce_enc.backward(ce_w, ce_a, grad_h, 0);
    cudaDeviceSynchronize();
    cudaFree(gl);
    cudaFree(gv);
}
#endif

const char* ce_test_last_error() { return cudaGetErrorString(cudaGetLastError()); }

}
