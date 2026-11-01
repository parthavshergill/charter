// The C side of rl/lean/CharterRL/Capi.lean: runtime start, thread start, and copies into the caller's buffers.
// Lean exports take their arguments over, so every call that only reads adds a reference first.
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "charter_rl.h"

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
lean_object* initialize_charter_CharterRL_Capi(uint8_t builtin);

lean_object* charter_rl_make(lean_object* cfg);
lean_object* charter_rl_error(lean_object* cfg);
lean_object* charter_rl_restart(lean_object* e, lean_object* lineup, uint64_t seed);
lean_object* charter_rl_step(lean_object* e, uint32_t action);
uint32_t charter_rl_seat(lean_object* e);
uint8_t charter_rl_over(lean_object* e);
uint8_t charter_rl_refused(lean_object* e);
uint8_t charter_rl_voting(lean_object* e);
lean_object* charter_rl_obs(lean_object* e);
lean_object* charter_rl_mask(lean_object* e);
lean_object* charter_rl_rewards(lean_object* e);
lean_object* charter_rl_info(lean_object* e);
uint32_t charter_rl_suggest(lean_object* e, lean_object* name);
uint32_t charter_rl_seats(lean_object* e);
lean_object* charter_rl_saved_log(lean_object* e, lean_object* code, lean_object* names);
lean_object* charter_rl_saved_state(lean_object* e);
uint32_t charter_rl_obs_size(lean_object* e);
uint32_t charter_rl_act_size(uint32_t);
uint32_t charter_rl_base_size(uint32_t);
uint32_t charter_rl_full_size(uint32_t);
lean_object* charter_rl_layout(uint32_t);
lean_object* charter_rl_info_names(uint32_t);

void charter_init(void) {
    static int done = 0;
    if (done) {
        return;
    }
    done = 1;
    lean_initialize_runtime_module();
    lean_set_panic_messages(false);
    lean_object* res = initialize_charter_CharterRL_Capi(1);
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (!lean_io_result_is_ok(res)) {
        fprintf(stderr, "charter: the Lean module failed to start\n");
        lean_io_result_show_error(res);
    }
    lean_dec_ref(res);
}

void charter_thread_init(void) {
    static _Thread_local int done = 0;
    if (!done) {
        done = 1;
        lean_initialize_thread();
    }
}

#define G(x) ((lean_object*)(x))
#define READ(x) (lean_inc(G(x)), G(x))

static int copy_string(lean_object* s, char* out, int cap) {
    const char* c = lean_string_cstr(s);
    int n = (int)strlen(c);
    if (out && cap > 0) {
        int k = n < cap - 1 ? n : cap - 1;
        memcpy(out, c, k);
        out[k] = 0;
    }
    lean_dec_ref(s);
    return n;
}

static int copy_floats(lean_object* a, float* out, int cap) {
    int n = (int)lean_sarray_size(a);
    const double* d = lean_float_array_cptr(a);
    int k = n < cap ? n : cap;
    for (int i = 0; i < k; i++) {
        out[i] = (float)d[i];
    }
    lean_dec_ref(a);
    return n;
}

void* charter_make(const char* cfg) { return charter_rl_make(lean_mk_string(cfg)); }
int charter_error(const char* cfg, char* out, int cap) { return copy_string(charter_rl_error(lean_mk_string(cfg)), out, cap); }
void* charter_restart(void* e, const char* lineup, uint64_t seed) { return charter_rl_restart(G(e), lean_mk_string(lineup), seed); }
void* charter_step(void* e, uint32_t a) { return charter_rl_step(G(e), a); }
void* charter_copy(void* e) { lean_inc(G(e)); return e; }
void charter_free(void* e) { lean_dec(G(e)); }

int charter_seat(void* e) { return (int)(int32_t)charter_rl_seat(READ(e)); }
int charter_over(void* e) { return charter_rl_over(READ(e)); }
int charter_refused(void* e) { return charter_rl_refused(READ(e)); }
int charter_voting(void* e) { return charter_rl_voting(READ(e)); }
int charter_seats(void* e) { return (int)charter_rl_seats(READ(e)); }
int charter_obs(void* e, float* out, int cap) { return copy_floats(charter_rl_obs(READ(e)), out, cap); }
int charter_rewards(void* e, float* out, int cap) { return copy_floats(charter_rl_rewards(READ(e)), out, cap); }
int charter_info(void* e, float* out, int cap) { return copy_floats(charter_rl_info(READ(e)), out, cap); }
int charter_mask(void* e, uint8_t* out, int cap) {
    lean_object* a = charter_rl_mask(READ(e));
    int n = (int)lean_sarray_size(a);
    memcpy(out, lean_sarray_cptr(a), n < cap ? n : cap);
    lean_dec_ref(a);
    return n;
}
int charter_suggest(void* e, const char* name) { return (int)(int32_t)charter_rl_suggest(READ(e), lean_mk_string(name)); }
int charter_saved_log(void* e, const char* code, const char* names, char* out, int cap) {
    return copy_string(charter_rl_saved_log(READ(e), lean_mk_string(code), lean_mk_string(names)), out, cap);
}
int charter_saved_state(void* e, char* out, int cap) { return copy_string(charter_rl_saved_state(READ(e)), out, cap); }
int charter_obs_size(void* e) { return (int)charter_rl_obs_size(READ(e)); }
int charter_act_size(void) { return (int)charter_rl_act_size(0); }
int charter_base_size(void) { return (int)charter_rl_base_size(0); }
int charter_full_size(void) { return (int)charter_rl_full_size(0); }
int charter_layout(char* out, int cap) { return copy_string(charter_rl_layout(0), out, cap); }
int charter_info_names(char* out, int cap) { return copy_string(charter_rl_info_names(0), out, cap); }
