// Four seats, one acting at a time. Twelve cells; each seat claims one in turn;
// the game ends after eight claims. Seats not on turn see only NOOP as legal.
// SMOKE_LEAN picks the Lean game; otherwise the same game runs in plain C.
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "raylib.h"
typedef float obs_t;
#define PUF_HAS_BOT_POLICY
#include "pufferenv.h"

#define CELLS 12
#define SEATS 4
#define PLIES 8
#define NOOP_ACTION CELLS
#define ACT_SIZES {CELLS + 1}
#define OBS_SIZE 17
#define NUM_ATNS 1
enum { BOT_RANDOM = 0, BOT_GREEDY = 1 };

struct Log {
    float perf, score, episode_return, episode_length;
    float hist_score, hist_n, top_cell_rate, policy_0_score;
    float n;
};

struct Env {
    Log log;
    Agent agents[SEATS];
    int tag;
    int boundary_reached;
    int num_agents;
    unsigned int rng;
    int bot_policy;
    int first_seat;
    int top_claims, claims;
#ifdef SMOKE_LEAN
    void* game;
#else
    uint32_t cells[CELLS], scores[SEATS], seat, ply, grng;
#endif
};

static inline void puf_set_bot_policy(Env* env, int bot_policy) {
    env->bot_policy = bot_policy;
}

#ifdef SMOKE_LEAN
#ifdef __cplusplus
extern "C" {
#endif
void* smoke_new(uint32_t seed);
void* smoke_step(void* s, uint32_t action);
uint32_t smoke_current(void* s);
uint8_t smoke_done(void* s);
uint32_t smoke_score(void* s, uint32_t seat);
uint32_t smoke_legal(void* s);
uint32_t smoke_bot_random(void* s, uint32_t seed);
uint32_t smoke_bot_greedy(void* s);
void smoke_runtime_init(void);
void smoke_thread_init(void);
void smoke_release(void* s);
void smoke_read_obs(void* s, uint8_t* out);
#ifdef __cplusplus
}
#endif

static void g_new(Env* e, uint32_t seed) {
    smoke_thread_init();
    if (e->game) {
        smoke_release(e->game);
    }
    e->game = smoke_new(seed);
}
static void g_step(Env* e, uint32_t a) { e->game = smoke_step(e->game, a); }
static uint32_t g_cur(Env* e) { return smoke_current(e->game); }
static int g_done(Env* e) { return smoke_done(e->game); }
static uint32_t g_score(Env* e, uint32_t s) { return smoke_score(e->game, s); }
static uint32_t g_legal(Env* e) { return smoke_legal(e->game); }
static uint32_t g_bot(Env* e, int bot, uint32_t seed) {
    return bot == BOT_GREEDY ? smoke_bot_greedy(e->game) : smoke_bot_random(e->game, seed);
}
static void g_obs(Env* e, uint8_t* o) { smoke_read_obs(e->game, o); }
#else
static uint32_t c_next(uint32_t x) { return x * 1664525u + 1013904223u; }
static void g_new(Env* e, uint32_t seed) {
    uint32_t r = seed;
    for (int i = 0; i < CELLS; i++) {
        r = c_next(r);
        e->cells[i] = 1 + ((r >> 16) % 15);
    }
    memset(e->scores, 0, sizeof(e->scores));
    e->seat = (r >> 24) & 3;
    e->ply = 0;
    e->grng = r;
}
static void g_step(Env* e, uint32_t a) {
    e->scores[e->seat] += e->cells[a];
    e->cells[a] = 0;
    e->seat = (e->seat + 1) % SEATS;
    e->ply++;
    e->grng = c_next(e->grng);
}
static uint32_t g_cur(Env* e) { return e->seat; }
static int g_done(Env* e) { return e->ply >= PLIES; }
static uint32_t g_score(Env* e, uint32_t s) { return e->scores[s]; }
static uint32_t g_legal(Env* e) {
    uint32_t m = 0;
    for (int i = 0; i < CELLS; i++) {
        if (e->cells[i]) {
            m |= 1u << i;
        }
    }
    return m;
}
static uint32_t g_bot(Env* e, int bot, uint32_t seed) {
    uint32_t best = 0, best_v = 0;
    if (bot == BOT_GREEDY) {
        for (int i = 0; i < CELLS; i++) {
            if (e->cells[i] > best_v) {
                best_v = e->cells[i];
                best = i;
            }
        }
        return best;
    }
    uint32_t start = c_next(seed + e->grng) >> 16;
    for (int k = 0; k < CELLS; k++) {
        uint32_t i = (start + k) % CELLS;
        if (e->cells[i]) {
            return i;
        }
    }
    return 0;
}
static void g_obs(Env* e, uint8_t* o) {
    for (int s = 0; s < SEATS; s++) {
        uint8_t* p = o + s * OBS_SIZE;
        for (int i = 0; i < CELLS; i++) {
            p[i] = e->cells[i];
        }
        p[CELLS] = e->seat == (uint32_t)s;
        for (int k = 0; k < SEATS; k++) {
            p[CELLS + 1 + k] = e->scores[(s + k) % SEATS];
        }
    }
}
#endif

static void write_outputs(Env* env) {
    uint8_t raw[SEATS * OBS_SIZE];
    g_obs(env, raw);
    uint32_t legal = g_legal(env);
    uint32_t cur = g_cur(env);
    for (int s = 0; s < env->num_agents; s++) {
        Agent* a = &env->agents[s];
        for (int i = 0; i < OBS_SIZE; i++) {
            a->observations[i] = raw[s * OBS_SIZE + i] / 16.0f;
        }
        for (int i = 0; i < CELLS; i++) {
            a->action_mask[i] = (uint32_t)s == cur ? (legal >> i) & 1 : 0;
        }
        a->action_mask[NOOP_ACTION] = (uint32_t)s != cur;
    }
}

// Bots fill every seat that has no agent. They act inside the env, so a seat 0
// learner in bot mode never sees a waiting step.
static void run_bots(Env* env) {
    while (!g_done(env) && (int)g_cur(env) >= env->num_agents) {
        g_step(env, g_bot(env, env->bot_policy, rand_r(&env->rng)));
    }
}

static void start_game(Env* env) {
    g_new(env, rand_r(&env->rng));
    run_bots(env);
}

void puf_reset(Env* env) {
    start_game(env);
    write_outputs(env);
}

static void finish(Env* env) {
    uint32_t top = 0;
    for (int s = 0; s < SEATS; s++) {
        if (g_score(env, s) > top) {
            top = g_score(env, s);
        }
    }
    int winners = 0;
    for (int s = 0; s < SEATS; s++) {
        winners += g_score(env, s) == top;
    }
    float s0 = g_score(env, 0) == top ? 1.0f / winners : 0.0f;
    for (int s = 0; s < env->num_agents; s++) {
        float own = g_score(env, s) / 60.0f;
        env->agents[s].rewards[0] = own;
        env->agents[s].terminals[0] = 1.0f;
    }
    env->log.perf += s0;
    env->log.score += s0;
    env->log.policy_0_score += s0;
    env->log.episode_return += g_score(env, 0) / 60.0f;
    env->log.episode_length += PLIES;
    env->log.top_cell_rate += env->claims ? (float)env->top_claims / env->claims : 0.0f;
    env->top_claims = env->claims = 0;
    if (env->tag > 0) {
        env->log.hist_score += s0;
        env->log.hist_n += 1.0f;
        env->boundary_reached = 1;
    }
    env->log.n += 1.0f;
}

void puf_step(Env* env) {
#ifdef SMOKE_LEAN
    smoke_thread_init();
#endif
    uint32_t cur = g_cur(env);
    assert((int)cur < env->num_agents);
    int action = (int)env->agents[cur].actions[0];
    uint32_t legal = g_legal(env);
    if (action < 0 || action >= CELLS || !((legal >> action) & 1)) {
        action = g_bot(env, BOT_RANDOM, rand_r(&env->rng));
    }
    if ((int)g_bot(env, BOT_GREEDY, 0) == action) {
        env->top_claims++;
    }
    env->claims++;
    g_step(env, action);
    run_bots(env);
    if (g_done(env)) {
        finish(env);
        start_game(env);
    }
    write_outputs(env);
}

void puf_render(Env* env) {
}

void puf_close(Env* env) {
}

void puf_init(Env* env, Dict* kwargs) {
#ifdef SMOKE_LEAN
    smoke_runtime_init();
#endif
    env->num_agents = dict_get(kwargs, "num_agents");
    env->bot_policy = dict_get(kwargs, "bot_policy");
    assert(env->num_agents == 1 || env->num_agents == SEATS);
    for (int s = 0; s < env->num_agents; s++) {
        // Seat 0 learns. On the frozen share of envs the other seats play a
        // past policy; env_setup sets every seat to policy 0 on all other envs.
        env->agents[s].policy = s == 0 ? 0 : (dict_get(kwargs, "distinct_opps") ? s : 1);
        env->agents[s].action_mask = NULL;
    }
}

void puf_log(Log* log, Dict* out) {
    dict_set(out, "perf", log->perf);
    dict_set(out, "score", log->score);
    dict_set(out, "policy_0_score", log->policy_0_score);
    dict_set(out, "policy_0_score", log->policy_0_score);
    dict_set(out, "episode_return", log->episode_return);
    dict_set(out, "episode_length", log->episode_length);
    dict_set(out, "hist_score", log->hist_score);
    dict_set(out, "hist_n", log->hist_n);
    dict_set(out, "top_cell_rate", log->top_cell_rate);
    dict_set(out, "n", log->n);
}
