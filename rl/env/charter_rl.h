// The Charter training environment, as a C library. Built by rl/env/build.sh into rl/build/libcharter_rl.so.
//
// A game is an opaque handle. charter_step and charter_restart take the handle over and give back a new one: never
// use the old one again. Every other call only reads. charter_copy gives a second handle to the same game, and each
// handle must be freed once. Call charter_init once per process, and charter_thread_init once on each thread before
// that thread makes any other call. A handle may move between threads, but two threads must not use one at once.
#pragma once
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void charter_init(void);
void charter_thread_init(void);

// A new game from a JSON configuration (see rl/README.md). If the configuration is wrong the handle is still valid,
// charter_refused is 1, charter_over is 1, and charter_error says why.
void* charter_make(const char* cfg);
// What is wrong with a configuration, as text, or "" if nothing. Returns the full length.
int charter_error(const char* cfg, char* out, int cap);
// The same settings, with a new lineup ("caller,hand,caller,caller") and seed.
void* charter_restart(void* game, const char* lineup, uint64_t seed);
// Play an action for the seat that must decide. A refused action changes nothing and sets charter_refused.
void* charter_step(void* game, uint32_t action);
void* charter_copy(void* game);
void charter_free(void* game);

int charter_seat(void* game);      // the seat that must decide, or -1
int charter_over(void* game);      // 1 when the game is over
int charter_refused(void* game);   // 1 when the last step was refused
int charter_voting(void* game);    // 1 when the deciding seat is voting
int charter_seats(void* game);
// Each copies at most cap numbers and returns how many there are.
int charter_obs(void* game, float* out, int cap);
int charter_mask(void* game, uint8_t* out, int cap);
int charter_rewards(void* game, float* out, int cap);  // one per seat, maxSeats of them
int charter_info(void* game, float* out, int cap);
// What a named strategy (hand, fair, closed) would do now, as an action, or -1.
int charter_suggest(void* game, const char* name);

int charter_obs_size(void* game);
int charter_act_size(void);
int charter_base_size(void);
int charter_full_size(void);
int charter_layout(char* out, int cap);
int charter_info_names(char* out, int cap);

#ifdef __cplusplus
}
#endif
