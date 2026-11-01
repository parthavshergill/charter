// Per-call cost of the Lean game from plain C threads, against the same game in C.
// Usage: bench THREADS GAMES init|noinit
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

uint32_t smoke_add(uint32_t a, uint32_t b);
void* smoke_new(uint32_t seed);
void* smoke_step(void* s, uint32_t action);
uint8_t smoke_done(void* s);
uint32_t smoke_bot_greedy(void* s);
void smoke_runtime_init(void);
void smoke_thread_init(void);
void smoke_thread_finish(void);
void smoke_release(void* s);
void smoke_read_obs(void* s, uint8_t* out);

static long g_games;
static int g_init;

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec / 1e9;
}

typedef struct {
    int id;
    double add_ns, step_ns, full_ns;
    uint64_t sink;
} Arg;

static void* worker(void* p) {
    Arg* a = (Arg*)p;
    if (g_init) {
        smoke_thread_init();
    }
    uint64_t sink = 0;
    long n = g_games * 200;
    double t0 = now();
    uint32_t x = a->id;
    for (long i = 0; i < n; i++) {
        x = smoke_add(x, (uint32_t)i);
    }
    a->add_ns = (now() - t0) * 1e9 / n;
    sink += x;

    t0 = now();
    long steps = 0;
    for (long g = 0; g < g_games; g++) {
        void* s = smoke_new((uint32_t)g + 7u * a->id);
        while (!smoke_done(s)) {
            s = smoke_step(s, smoke_bot_greedy(s));
            steps++;
        }
        smoke_release(s);
    }
    a->step_ns = (now() - t0) * 1e9 / steps;

    uint8_t obs[68];
    t0 = now();
    steps = 0;
    for (long g = 0; g < g_games; g++) {
        void* s = smoke_new((uint32_t)g + 7u * a->id);
        while (!smoke_done(s)) {
            s = smoke_step(s, smoke_bot_greedy(s));
            smoke_read_obs(s, obs);
            sink += obs[3];
            steps++;
        }
        smoke_release(s);
    }
    a->full_ns = (now() - t0) * 1e9 / steps;
    a->sink = sink;
    if (g_init) {
        smoke_thread_finish();
    }
    return NULL;
}

int main(int argc, char** argv) {
    int threads = atoi(argv[1]);
    g_games = atol(argv[2]);
    g_init = strcmp(argv[3], "init") == 0;
    smoke_runtime_init();
    pthread_t t[64];
    Arg a[64];
    memset(a, 0, sizeof(a));
    for (int i = 0; i < threads; i++) {
        a[i].id = i;
        pthread_create(&t[i], NULL, worker, &a[i]);
    }
    double add = 0, step = 0, full = 0;
    for (int i = 0; i < threads; i++) {
        pthread_join(t[i], NULL);
        add += a[i].add_ns;
        step += a[i].step_ns;
        full += a[i].full_ns;
    }
    printf("threads=%d init=%d add_ns=%.2f step_with_bot_ns=%.1f step_bot_obs_ns=%.1f sink=%llu\n",
        threads, g_init, add / threads, step / threads, full / threads,
        (unsigned long long)a[0].sink);
    return 0;
}
