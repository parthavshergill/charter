// Runs rl/puffer/charter.h on the CPU, without the trainer: random legal actions from each agent's mask, checking
// that exactly one agent may act, that waiting agents may only wait, and that games end. Prints steps per second.
// Build: see rl/puffer/test_env.sh.
#include <time.h>
#include "charter.h"

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static int run(const char* games, int num_agents, int bot, double seconds, const char* vote, const char* share) {
    Dict kw = {0};
    char buf[32];
    puf_ini_set(&kw, "games", games);
    snprintf(buf, sizeof(buf), "%d", num_agents);
    puf_ini_set(&kw, "num_agents", buf);
    snprintf(buf, sizeof(buf), "%d", bot);
    puf_ini_set(&kw, "bot_policy", buf);
    puf_ini_set(&kw, "vote_mode", vote);
    puf_ini_set(&kw, "bot_share", share);
#ifdef CHARTER_MOVE_ROWS
    puf_ini_set(&kw, "move_rows", "1");
#endif
    Env env = {0};
    env.rng = 12345;
    puf_init(&env, &kw);
    static obs_t obs[SEATS][OBS_SIZE];
    static float act[SEATS], rew[SEATS], term[SEATS];
    static unsigned char mask[SEATS][CHARTER_ACTS + 1];
    for (int i = 0; i < env.num_agents; i++) {
        env.agents[i].observations = obs[i];
        env.agents[i].actions = &act[i];
        env.agents[i].rewards = &rew[i];
        env.agents[i].terminals = &term[i];
        env.agents[i].action_mask = mask[i];
    }
    puf_reset(&env);
    unsigned int r = 7;
    long ticks = 0, games_done = 0, bad = 0;
    double total_reward = 0, t0 = now();
    while (now() - t0 < seconds) {
        int acting = 0;
        for (int i = 0; i < env.num_agents; i++) {
            int n = 0;
            for (int a = 0; a < CHARTER_ACTS; a++) {
                n += mask[i][a];
            }
            if (n > 0) {
                acting++;
                if (mask[i][NOOP_ACTION]) {
                    bad++;
                }
                int k = rand_r(&r) % n;
                for (int a = 0; a < CHARTER_ACTS; a++) {
                    if (mask[i][a] && k-- == 0) {
                        act[i] = a;
                        break;
                    }
                }
            } else {
                if (!mask[i][NOOP_ACTION]) {
                    bad++;
                }
                act[i] = NOOP_ACTION;
            }
        }
        if (acting != 1) {
            bad++;
        }
        puf_step(&env);
        ticks++;
        for (int i = 0; i < env.num_agents; i++) {
            total_reward += rew[i];
        }
        games_done += term[0] > 0;
    }
    double dt = now() - t0;
    printf("games=%s agents=%d bot=%d vote=%s bot_share=%s: %.0f ticks/s (%.0f agent rows/s), %.1f games/s, perf=%.3f "
           "invalid=%.3f bad=%ld mean_reward_per_game=%.3f\n",
        games, num_agents, bot, vote, share, ticks / dt, ticks * num_agents / dt, games_done / dt,
        env.log.n ? env.log.perf / env.log.n : 0, env.log.n ? env.log.invalid_rate / env.log.n : 0, bad,
        games_done ? total_reward / games_done : 0);
    puf_close(&env);
    return bad == 0 && games_done > 0 ? 0 : 1;
}

int main(int argc, char** argv) {
    double s = argc > 1 ? atof(argv[1]) : 3;
    int fails = 0;
    fails += run("island,not-catan", 4, 0, s, "bot", "0");
    fails += run("island,not-catan", 4, 0, s, "policy", "0");
    fails += run("island", 1, BOT_RANDOM, s, "bot", "0");
    fails += run("island", 1, BOT_HAND, s, "bot", "0");
    fails += run("not-catan", 1, BOT_HAND, s, "random", "0");
    fails += run("island,not-catan", 1, BOT_CHAMPION, s, "bot", "0");
    fails += run("island,not-catan", 1, BOT_CHAMPION_CLOSED, s, "bot", "0");
    // Half the games against three champions, half in self-play. Rewards no longer sum to 1 per game.
    fails += run("island,not-catan", 4, BOT_CHAMPION, s, "bot", "0.5");
    printf(fails ? "FAIL\n" : "PASS\n");
    return fails ? 1 : 0;
}
