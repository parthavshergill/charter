// PufferLib env for Charter: four seats, one deciding at a time, every move through the Lean engine's Engine.step.
//
// rl/puffer/README section of rl/README.md says how to build it. The game itself is rl/build/libcharter_rl.so,
// reached only through rl/env/charter_rl.h, so nvcc never parses lean.h.
//
// Seats: agent i plays game seat seat_of[i], drawn afresh each game, so no agent always sits first. A waiting agent
// sees zeros and a mask with only the no-op. With num_agents = 1 (the bot ladder), bots fill the other seats:
// bot_policy 0 plays random legal actions, 1 is hand, 2 fair, 3 closed. With no offers made, 1, 2 and 3 play the same.
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "raylib.h"
typedef float obs_t;
#define PUF_HAS_BOT_POLICY
#include "pufferenv.h"
#include "charter_rl.h"

#define SEATS 4
#define MAX_GAMES 8
#define CHARTER_ACTS 695
#define CHARTER_BASE_OBS 4434
#define CHARTER_FULL_OBS 7122
#ifdef CHARTER_MOVE_ROWS
#define OBS_SIZE CHARTER_FULL_OBS
#else
#define OBS_SIZE CHARTER_BASE_OBS
#endif
#define NOOP_ACTION CHARTER_ACTS
#define ACT_SIZES {CHARTER_ACTS + 1}
#define NUM_ATNS 1
#define REWARD_SEATS 6
enum { BOT_RANDOM = 0, BOT_HAND = 1, BOT_FAIR = 2, BOT_CLOSED = 3 };
static const char* BOT_NAMES[] = {"caller", "hand", "fair", "closed"};

struct Log {
    float perf, score, policy_0_score, draw_rate;
    float episode_return, episode_length, win_seat0, win_seat1, win_seat2, win_seat3;
    float points, points_share, rounds, decisions, invalid_rate, laws_proposed, laws_passed;
    float hist_score, hist_n;
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
    int num_games;
    void* games[MAX_GAMES];
    int current;
    int seat_of[SEATS];    // agent -> game seat
    int agent_at[SEATS];   // game seat -> agent, or -1 for a bot seat
    int random_seat[SEATS];
    float returns[SEATS];
    int moves, invalid;
    uint8_t mask[CHARTER_ACTS];
};

static inline void puf_set_bot_policy(Env* env, int bot_policy) {
    env->bot_policy = bot_policy;
}

static void* G(Env* e) { return e->games[e->current]; }

static void start_game(Env* env);

static int random_legal(Env* env) {
    int n = 0;
    for (int i = 0; i < CHARTER_ACTS; i++) {
        n += env->mask[i];
    }
    if (n == 0) {
        return -1;
    }
    int k = rand_r(&env->rng) % n;
    for (int i = 0; i < CHARTER_ACTS; i++) {
        if (env->mask[i] && k-- == 0) {
            return i;
        }
    }
    return -1;
}

// Seats played by the random bot are callers in the Lean game, so the env plays them here.
static void run_random_bots(Env* env) {
    while (!charter_over(G(env))) {
        int seat = charter_seat(G(env));
        if (seat < 0 || !env->random_seat[seat]) {
            return;
        }
        charter_mask(G(env), env->mask, CHARTER_ACTS);
        int a = random_legal(env);
        if (a < 0) {
            return;
        }
        env->games[env->current] = charter_step(G(env), (uint32_t)a);
    }
}

static void write_outputs(Env* env) {
    int seat = charter_seat(G(env));
    int deciding = seat >= 0 ? env->agent_at[seat] : -1;
    for (int i = 0; i < env->num_agents; i++) {
        Agent* a = &env->agents[i];
        if (i == deciding) {
            charter_obs(G(env), a->observations, OBS_SIZE);
            charter_mask(G(env), a->action_mask, CHARTER_ACTS);
            a->action_mask[NOOP_ACTION] = 0;
        } else {
            memset(a->observations, 0, OBS_SIZE * sizeof(obs_t));
            memset(a->action_mask, 0, CHARTER_ACTS);
            a->action_mask[NOOP_ACTION] = 1;
        }
    }
}

static void add_rewards(Env* env) {
    float r[REWARD_SEATS];
    charter_rewards(G(env), r, REWARD_SEATS);
    for (int i = 0; i < env->num_agents; i++) {
        float x = r[env->seat_of[i]];
        env->agents[i].rewards[0] += x;
        env->returns[i] += x;
    }
}

static void finish(Env* env) {
    float info[32] = {0};
    charter_info(G(env), info, 32);
    // info: over, winner, round, events, rejected, proposed, passed, decisions, offers, points0..5, opening0..5
    int winner = (int)info[1];
    int me = env->seat_of[0];
    float won = winner == me ? 1.0f : 0.0f;
    float total = 0;
    for (int s = 0; s < SEATS; s++) {
        total += info[9 + s];
    }
    Log* l = &env->log;
    l->perf += won;
    l->score += won;
    l->policy_0_score += won;
    l->draw_rate += winner < 0 ? 1.0f : 0.0f;
    l->episode_return += env->returns[0];
    l->episode_length += env->moves;
    float* by_seat[SEATS] = {&l->win_seat0, &l->win_seat1, &l->win_seat2, &l->win_seat3};
    *by_seat[me] += won;
    l->points += info[9 + me];
    l->points_share += total > 0 ? info[9 + me] / total : 0.25f;
    l->rounds += info[2];
    l->decisions += info[7];
    l->invalid_rate += env->moves ? (float)env->invalid / env->moves : 0.0f;
    l->laws_proposed += info[5];
    l->laws_passed += info[6];
    if (env->tag > 0) {
        l->hist_score += won;
        l->hist_n += 1.0f;
        env->boundary_reached = 1;
    }
    l->n += 1.0f;
    for (int i = 0; i < env->num_agents; i++) {
        env->agents[i].terminals[0] = 1.0f;
    }
}

static void start_game(Env* env) {
    charter_thread_init();
    env->current = env->num_games > 1 ? rand_r(&env->rng) % env->num_games : 0;
    int seats = charter_seats(G(env));
    assert(seats == SEATS);
    // A fresh seat for each agent.
    int perm[SEATS];
    for (int s = 0; s < SEATS; s++) {
        perm[s] = s;
    }
    for (int s = SEATS - 1; s > 0; s--) {
        int j = rand_r(&env->rng) % (s + 1);
        int t = perm[s];
        perm[s] = perm[j];
        perm[j] = t;
    }
    char lineup[128] = {0};
    for (int s = 0; s < SEATS; s++) {
        env->agent_at[s] = -1;
        env->random_seat[s] = 0;
    }
    for (int i = 0; i < env->num_agents; i++) {
        env->seat_of[i] = perm[i];
        env->agent_at[perm[i]] = i;
    }
    for (int s = 0; s < SEATS; s++) {
        const char* who = env->agent_at[s] >= 0 ? "caller" : BOT_NAMES[env->bot_policy];
        if (env->agent_at[s] < 0 && env->bot_policy == BOT_RANDOM) {
            env->random_seat[s] = 1;
        }
        strcat(lineup, s ? "," : "");
        strcat(lineup, who);
    }
    uint64_t seed = ((uint64_t)rand_r(&env->rng) << 31) ^ (uint64_t)rand_r(&env->rng);
    env->games[env->current] = charter_restart(G(env), lineup, seed);
    if (charter_refused(G(env))) {
        fprintf(stderr, "charter: could not start a game with lineup %s\n", lineup);
        abort();
    }
    env->moves = env->invalid = 0;
    for (int i = 0; i < SEATS; i++) {
        env->returns[i] = 0;
    }
    run_random_bots(env);
    add_rewards(env);
}

void puf_reset(Env* env) {
    start_game(env);
    for (int i = 0; i < env->num_agents; i++) {
        env->agents[i].rewards[0] = 0;
        env->agents[i].terminals[0] = 0;
    }
    write_outputs(env);
}

void puf_step(Env* env) {
    charter_thread_init();
    for (int i = 0; i < env->num_agents; i++) {
        env->agents[i].rewards[0] = 0;
        env->agents[i].terminals[0] = 0;
    }
    int seat = charter_seat(G(env));
    if (seat >= 0 && env->agent_at[seat] >= 0) {
        int who = env->agent_at[seat];
        int action = (int)env->agents[who].actions[0];
        charter_mask(G(env), env->mask, CHARTER_ACTS);
        if (action < 0 || action >= CHARTER_ACTS || !env->mask[action]) {
            if (who == 0) {
                env->invalid++;
            }
            action = random_legal(env);
        }
        if (who == 0) {
            env->moves++;
        }
        if (action >= 0) {
            env->games[env->current] = charter_step(G(env), (uint32_t)action);
        }
        run_random_bots(env);
        add_rewards(env);
    }
    if (charter_over(G(env))) {
        finish(env);
        float keep[SEATS];
        for (int i = 0; i < env->num_agents; i++) {
            keep[i] = env->agents[i].rewards[0];
        }
        start_game(env);
        for (int i = 0; i < env->num_agents; i++) {
            env->agents[i].rewards[0] = keep[i];
        }
    }
    write_outputs(env);
}

void puf_render(Env* env) {
}

void puf_close(Env* env) {
    for (int g = 0; g < env->num_games; g++) {
        if (env->games[g]) {
            charter_free(env->games[g]);
            env->games[g] = NULL;
        }
    }
}

static const char* opt_str(Dict* kwargs, const char* key, const char* dflt) {
    DictItem* it = dict_find(kwargs, key);
    return it && it->str ? it->str : dflt;
}

static double opt_num(Dict* kwargs, const char* key, double dflt) {
    DictItem* it = dict_find(kwargs, key);
    return it ? it->value : dflt;
}

void puf_init(Env* env, Dict* kwargs) {
    charter_init();
    charter_thread_init();
    assert(charter_act_size() == CHARTER_ACTS);
    assert(charter_base_size() == CHARTER_BASE_OBS && charter_full_size() == CHARTER_FULL_OBS);
    env->num_agents = (int)dict_get(kwargs, "num_agents");
    env->bot_policy = (int)opt_num(kwargs, "bot_policy", BOT_HAND);
    assert(env->num_agents == 1 || env->num_agents == SEATS);
    int move_rows = (int)opt_num(kwargs, "move_rows", 0);
#ifdef CHARTER_MOVE_ROWS
    assert(move_rows && "built with CHARTER_MOVE_ROWS: set env.move_rows = 1");
#else
    assert(!move_rows && "env.move_rows = 1 needs a build with -DCHARTER_MOVE_ROWS");
#endif
    const char* vote = opt_str(kwargs, "vote_mode", "bot");
    const char* slots = opt_str(kwargs, "slot_order", "shuffled");
    char games[256];
    snprintf(games, sizeof(games), "%s", opt_str(kwargs, "games", "island"));
    env->num_games = 0;
    char* save = NULL;
    for (char* id = strtok_r(games, ",", &save); id; id = strtok_r(NULL, ",", &save)) {
        assert(env->num_games < MAX_GAMES);
        char cfg[1024];
        snprintf(cfg, sizeof(cfg),
            "{\"game\": \"%s\", \"lineup\": [\"caller\", \"caller\", \"caller\", \"caller\"], \"seed\": %u, "
            "\"vote_mode\": \"%s\", \"slot_order\": \"%s\", \"move_rows\": %s, \"law_every\": %d, "
            "\"random_map\": %s, \"preview\": %s, \"reward_win\": %g, \"reward_standing\": %g, \"shaping_points\": %g}",
            id, env->rng, vote, slots, move_rows ? "true" : "false", (int)opt_num(kwargs, "law_every", 8),
            opt_num(kwargs, "random_map", 1) ? "true" : "false", opt_num(kwargs, "preview", 1) ? "true" : "false",
            opt_num(kwargs, "reward_win", 1.0), opt_num(kwargs, "reward_standing", 0.25),
            opt_num(kwargs, "shaping_points", 0.0));
        char err[512];
        if (charter_error(cfg, err, sizeof(err))) {
            fprintf(stderr, "charter: bad [env] settings: %s\n", err);
            exit(1);
        }
        env->games[env->num_games++] = charter_make(cfg);
    }
    for (int s = 0; s < env->num_agents; s++) {
        // Agent 0 learns. On the frozen share of envs the others play past policies.
        env->agents[s].policy = s == 0 ? 0 : (opt_num(kwargs, "distinct_opps", 0) ? s : 1);
        env->agents[s].action_mask = NULL;
    }
}

void puf_log(Log* log, Dict* out) {
    dict_set(out, "perf", log->perf);
    dict_set(out, "score", log->score);
    dict_set(out, "policy_0_score", log->policy_0_score);
    dict_set(out, "draw_rate", log->draw_rate);
    dict_set(out, "episode_return", log->episode_return);
    dict_set(out, "episode_length", log->episode_length);
    dict_set(out, "win_seat0", log->win_seat0);
    dict_set(out, "win_seat1", log->win_seat1);
    dict_set(out, "win_seat2", log->win_seat2);
    dict_set(out, "win_seat3", log->win_seat3);
    dict_set(out, "points", log->points);
    dict_set(out, "points_share", log->points_share);
    dict_set(out, "rounds", log->rounds);
    dict_set(out, "decisions", log->decisions);
    dict_set(out, "invalid_rate", log->invalid_rate);
    dict_set(out, "laws_proposed", log->laws_proposed);
    dict_set(out, "laws_passed", log->laws_passed);
    dict_set(out, "hist_score", log->hist_score);
    dict_set(out, "hist_n", log->hist_n);
}
