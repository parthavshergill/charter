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

const char* ce_test_last_error() { return cudaGetErrorString(cudaGetLastError()); }

}
