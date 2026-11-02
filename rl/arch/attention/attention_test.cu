// Runs the CUDA attention encoder on one case written by reference_test.py, and writes what it computed.
//   attention_test DIR B HIDDEN [BENCH_B]
// Reads DIR/obs.f32 [B, obs], DIR/weights.f32 (parameters in registration order), DIR/gout.f32 [B, HIDDEN].
// Writes DIR/out.f32 (training forward), DIR/out_rollout.f32 (rollout forward), DIR/grads.f32 (weight
// gradients in registration order). With BENCH_B, also times forward and backward at that batch size.
// Built with -DENV_HEADER=<any PufferLib env header>; the env is not used.
#include <algorithm>
#include <string>
#include <vector>
#include "src/pufferl.cu"
#include "attention.cu"

static std::vector<float> read_f32(const char* dir, const char* name, size_t n) {
    std::string path = std::string(dir) + "/" + name;
    FILE* f = fopen(path.c_str(), "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", path.c_str()); exit(2); }
    std::vector<float> v(n);
    size_t got = fread(v.data(), sizeof(float), n, f);
    fclose(f);
    if (got != n) { fprintf(stderr, "%s: wanted %zu floats, got %zu\n", path.c_str(), n, got); exit(2); }
    return v;
}

static void write_f32(const char* dir, const char* name, const std::vector<float>& v) {
    std::string path = std::string(dir) + "/" + name;
    FILE* f = fopen(path.c_str(), "wb");
    fwrite(v.data(), sizeof(float), v.size(), f);
    fclose(f);
}

__global__ void ca_test_to_f32(float* dst, const precision_t* src, int64_t n) {
    int64_t i = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) dst[i] = to_float(src[i]);
}

__global__ void ca_test_from_f32(precision_t* dst, const float* src, int64_t n) {
    int64_t i = (int64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) dst[i] = from_float(src[i]);
}

static void upload(precision_t* dst, const float* host, int64_t n) {
    float* tmp;
    cudaMalloc(&tmp, n * sizeof(float));
    cudaMemcpy(tmp, host, n * sizeof(float), cudaMemcpyHostToDevice);
    ca_test_from_f32<<<(n + 255) / 256, 256>>>(dst, tmp, n);
    cudaDeviceSynchronize();
    cudaFree(tmp);
}

static void download(float* host, const precision_t* src, int64_t n) {
    float* tmp;
    cudaMalloc(&tmp, n * sizeof(float));
    ca_test_to_f32<<<(n + 255) / 256, 256>>>(tmp, src, n);
    cudaDeviceSynchronize();
    cudaMemcpy(host, tmp, n * sizeof(float), cudaMemcpyDeviceToHost);
    cudaFree(tmp);
}

static void check_cuda(const char* where) {
    cudaError_t e = cudaDeviceSynchronize();
    if (e == cudaSuccess) e = cudaGetLastError();
    if (e != cudaSuccess) { fprintf(stderr, "CUDA error at %s: %s\n", where, cudaGetErrorString(e)); exit(3); }
}

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s DIR B HIDDEN [BENCH_B]\n", argv[0]); return 2; }
    const char* dir = argv[1];
    int B = atoi(argv[2]), hidden = atoi(argv[3]);
    int bench_B = argc > 4 ? atoi(argv[4]) : 0;
    cublas_init_handle();

    Encoder enc = {};
    enc.in_dim = CA_OBS_SIZE;
    enc.out_dim = hidden;
    create_charter_attn_encoder(&enc);
    void* w = enc.create_weights(&enc);
    Allocator params = {}, acts = {}, grads = {}, roll = {};
    enc.reg_params(w, &params);
    alloc_create(&params);
    int64_t n_params = 0;
    for (int i = 0; i < params.num_regs; i++) n_params += numel(params.regs[i].shape);
    std::vector<float> wh = read_f32(dir, "weights.f32", n_params);
    int64_t at = 0;
    for (int i = 0; i < params.num_regs; i++) {
        int64_t n = numel(params.regs[i].shape);
        upload((precision_t*)*params.regs[i].data_ptr, wh.data() + at, n);
        at += n;
    }
    void* act = calloc(1, enc.activation_size);
    enc.reg_train(w, act, &acts, &grads, B);
    alloc_create(&acts);
    alloc_create(&grads);
    void* ract = calloc(1, enc.activation_size);
    enc.reg_rollout(w, ract, &roll, B);
    alloc_create(&roll);

    std::vector<float> oh = read_f32(dir, "obs.f32", (size_t)B * CA_OBS_SIZE);
    std::vector<float> gh = read_f32(dir, "gout.f32", (size_t)B * hidden);
    Prec obs = {.shape = {B, CA_OBS_SIZE}};
    Prec gout = {.shape = {B, hidden}};
    cudaMalloc(&obs.data, (size_t)B * CA_OBS_SIZE * sizeof(precision_t));
    cudaMalloc(&gout.data, (size_t)B * hidden * sizeof(precision_t));
    upload(obs.data, oh.data(), (int64_t)B * CA_OBS_SIZE);
    upload(gout.data, gh.data(), (int64_t)B * hidden);

    Prec out = enc.forward(w, act, obs, 0);
    check_cuda("forward");
    std::vector<float> out_h((size_t)B * hidden);
    download(out_h.data(), out.data, (int64_t)B * hidden);
    write_f32(dir, "out.f32", out_h);

    Prec rout = enc.forward(w, ract, obs, 0);
    check_cuda("rollout forward");
    download(out_h.data(), rout.data, (int64_t)B * hidden);
    write_f32(dir, "out_rollout.f32", out_h);

    enc.backward(w, act, gout, 0);
    check_cuda("backward");
    std::vector<float> g_h(n_params);
    at = 0;
    for (int i = 0; i < grads.num_regs; i++) {
        int64_t n = numel(grads.regs[i].shape);
        assert(n == numel(params.regs[i].shape));
        download(g_h.data() + at, (precision_t*)*grads.regs[i].data_ptr, n);
        at += n;
    }
    assert(at == n_params);
    write_f32(dir, "grads.f32", g_h);
    printf("params %ld\n", (long)n_params);
    printf("smem fwd %zu bwd %zu\n", ca_smem_bytes(false), ca_smem_bytes(true));

    if (bench_B > 0) {
        Allocator bacts = {}, bgrads = {}, broll = {};
        void* bact = calloc(1, enc.activation_size);
        void* bract = calloc(1, enc.activation_size);
        enc.reg_train(w, bact, &bacts, &bgrads, bench_B);
        enc.reg_rollout(w, bract, &broll, bench_B);
        alloc_create(&bacts);
        alloc_create(&bgrads);
        alloc_create(&broll);
        Prec bobs = {.shape = {bench_B, CA_OBS_SIZE}};
        Prec bg = {.shape = {bench_B, hidden}};
        cudaMalloc(&bobs.data, (size_t)bench_B * CA_OBS_SIZE * sizeof(precision_t));
        cudaMalloc(&bg.data, (size_t)bench_B * hidden * sizeof(precision_t));
        for (int64_t s = 0; s < bench_B; s += B) {   // tile the test case's observations
            int64_t n = std::min<int64_t>(B, bench_B - s);
            upload(bobs.data + s * CA_OBS_SIZE, oh.data(), n * CA_OBS_SIZE);
            upload(bg.data + s * hidden, gh.data(), n * hidden);
        }
        cudaEvent_t e0, e1;
        cudaEventCreate(&e0);
        cudaEventCreate(&e1);
        const int iters = 20;
        enc.forward(w, bract, bobs, 0);
        check_cuda("bench warmup");
        cudaEventRecord(e0);
        for (int i = 0; i < iters; i++) enc.forward(w, bract, bobs, 0);
        cudaEventRecord(e1);
        cudaEventSynchronize(e1);
        float ms_roll;
        cudaEventElapsedTime(&ms_roll, e0, e1);
        enc.forward(w, bact, bobs, 0);
        enc.backward(w, bact, bg, 0);
        check_cuda("bench warmup train");
        cudaEventRecord(e0);
        for (int i = 0; i < iters; i++) {
            enc.forward(w, bact, bobs, 0);
            enc.backward(w, bact, bg, 0);
        }
        cudaEventRecord(e1);
        cudaEventSynchronize(e1);
        float ms_train;
        cudaEventElapsedTime(&ms_train, e0, e1);
        check_cuda("bench");
#ifdef CA_PROFILE
        printf("backward stages ms/iter: out-GEMMs %.3f attn-kernel %.3f small-GEMMs %.3f table-wgrads %.3f\n",
            ca_prof_ms[1] / (iters + 2), ca_prof_ms[2] / (iters + 2), ca_prof_ms[3] / (iters + 2), ca_prof_ms[4] / (iters + 2));
        int nf = 2 * iters + 4;
        printf("forward stages ms/call: ctx %.3f tables %.3f attn-kernel %.3f out-GEMM %.3f\n",
            ca_prof_ms[6] / nf, ca_prof_ms[7] / nf, ca_prof_ms[8] / nf, ca_prof_ms[9] / nf);
#endif
        printf("bench B=%d rollout_forward_ms %.3f train_fwd_bwd_ms %.3f obs_per_s_rollout %.0f\n",
            bench_B, ms_roll / iters, ms_train / iters, bench_B / (ms_roll / iters / 1000.0));
    }
    return 0;
}
