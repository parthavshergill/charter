// Thin C layer between PufferLib and the Lean runtime. The env header never
// includes lean.h, so nvcc does not parse it.
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object* initialize_SmokeGame(uint8_t builtin);
lean_object* smoke_obs_all(b_lean_obj_arg s);

void smoke_runtime_init(void) {
    static int done = 0;
    if (done) {
        return;
    }
    done = 1;
    lean_initialize_runtime_module();
    lean_set_panic_messages(false);
    lean_object* res = initialize_SmokeGame(1);
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (!lean_io_result_is_ok(res)) {
        fprintf(stderr, "initialize_SmokeGame failed\n");
        lean_io_result_show_error(res);
    }
    lean_dec_ref(res);
}

// Called once per thread before that thread uses Lean objects.
void smoke_thread_init(void) {
    static _Thread_local int done = 0;
    if (!done) {
        done = 1;
        lean_initialize_thread();
    }
}

void smoke_thread_finish(void) {
    lean_finalize_thread();
}

void smoke_release(void* s) {
    lean_dec((lean_object*)s);
}

void smoke_read_obs(void* s, uint8_t* out) {
    lean_object* a = smoke_obs_all((lean_object*)s);
    memcpy(out, lean_sarray_cptr(a), lean_sarray_size(a));
    lean_dec_ref(a);
}
