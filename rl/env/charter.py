"""Python binding for rl/build/libcharter_rl.so, over ctypes. One `Game` is one game in progress.

    from charter import Game, init
    g = Game({"game": "island", "lineup": ["caller", "hand", "hand", "hand"], "seed": 7})
    while not g.over:
        a = g.legal()[0]
        g.step(a)

The library holds a Lean runtime. Call `init()` once (Game does it), and `thread_init()` on each extra thread."""
import ctypes
import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LIB_PATH = os.environ.get("CHARTER_RL_LIB", os.path.join(HERE, "..", "build", "libcharter_rl.so"))
_lib = None


def lib():
    global _lib
    if _lib is None:
        L = ctypes.CDLL(LIB_PATH)
        vp, cp, i, u64, u32 = ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int, ctypes.c_uint64, ctypes.c_uint32
        fp, bp = ctypes.POINTER(ctypes.c_float), ctypes.POINTER(ctypes.c_uint8)
        sig = {
            "charter_make": (vp, [cp]), "charter_error": (i, [cp, cp, i]),
            "charter_restart": (vp, [vp, cp, u64]), "charter_step": (vp, [vp, u32]),
            "charter_copy": (vp, [vp]), "charter_free": (None, [vp]),
            "charter_seat": (i, [vp]), "charter_over": (i, [vp]), "charter_refused": (i, [vp]),
            "charter_voting": (i, [vp]), "charter_seats": (i, [vp]),
            "charter_obs": (i, [vp, fp, i]), "charter_mask": (i, [vp, bp, i]),
            "charter_rewards": (i, [vp, fp, i]), "charter_info": (i, [vp, fp, i]),
            "charter_suggest": (i, [vp, cp]), "charter_saved_log": (i, [vp, cp, cp, cp, i]),
            "charter_saved_state": (i, [vp, cp, i]), "charter_obs_size": (i, [vp]),
            "charter_act_size": (i, []), "charter_base_size": (i, []), "charter_full_size": (i, []),
            "charter_layout": (i, [cp, i]), "charter_info_names": (i, [cp, i]),
            "charter_init": (None, []), "charter_thread_init": (None, []),
        }
        for name, (res, args) in sig.items():
            f = getattr(L, name)
            f.restype, f.argtypes = res, args
        L.charter_init()
        L.charter_thread_init()
        _lib = L
    return _lib


def init():
    lib()


def thread_init():
    lib().charter_thread_init()


def _text(fn, *args):
    n = fn(*args, None, 0)
    buf = ctypes.create_string_buffer(n + 1)
    fn(*args, buf, n + 1)
    return buf.value.decode()


def layout():
    return json.loads(_text(lib().charter_layout))


def info_names():
    return _text(lib().charter_info_names).split(",")


ACT_SIZE = None
MAX_SEATS = 6


class Game:
    """One game. `cfg` is a dict as rl/README.md describes, or its JSON text."""

    def __init__(self, cfg):
        L = lib()
        text = cfg if isinstance(cfg, str) else json.dumps(cfg)
        err = _text(L.charter_error, text.encode())
        if err:
            raise ValueError(err)
        self._h = L.charter_make(text.encode())
        self.act_size = L.charter_act_size()
        self.obs_size = L.charter_obs_size(self._h)
        self._mask = np.zeros(self.act_size, np.uint8)
        self._obs = np.zeros(self.obs_size, np.float32)

    def __del__(self):
        if getattr(self, "_h", None) and _lib is not None:
            _lib.charter_free(self._h)
            self._h = None

    def restart(self, lineup, seed):
        self._h = lib().charter_restart(self._h, ",".join(lineup).encode(), seed)
        if self.refused:
            raise ValueError(f"cannot restart with lineup {lineup}")

    def step(self, action):
        self._h = lib().charter_step(self._h, int(action))
        return not self.refused

    def copy(self):
        g = object.__new__(Game)
        g.__dict__.update(self.__dict__)
        g._h = lib().charter_copy(self._h)
        g._mask, g._obs = self._mask.copy(), self._obs.copy()
        return g

    @property
    def seat(self):
        return lib().charter_seat(self._h)

    @property
    def over(self):
        return bool(lib().charter_over(self._h))

    @property
    def refused(self):
        return bool(lib().charter_refused(self._h))

    @property
    def voting(self):
        return bool(lib().charter_voting(self._h))

    @property
    def seats(self):
        return lib().charter_seats(self._h)

    def obs(self, out=None):
        out = self._obs if out is None else out
        lib().charter_obs(self._h, out.ctypes.data_as(ctypes.POINTER(ctypes.c_float)), out.size)
        return out

    def mask(self, out=None):
        out = self._mask if out is None else out
        lib().charter_mask(self._h, out.ctypes.data_as(ctypes.POINTER(ctypes.c_uint8)), out.size)
        return out

    def legal(self):
        return np.flatnonzero(self.mask())

    def rewards(self):
        out = np.zeros(MAX_SEATS, np.float32)
        lib().charter_rewards(self._h, out.ctypes.data_as(ctypes.POINTER(ctypes.c_float)), out.size)
        return out

    def info(self):
        names = info_names()
        out = np.zeros(len(names), np.float32)
        lib().charter_info(self._h, out.ctypes.data_as(ctypes.POINTER(ctypes.c_float)), out.size)
        return dict(zip(names, out.tolist()))

    def suggest(self, name="hand"):
        return lib().charter_suggest(self._h, name.encode())

    def saved_log(self, code, names):
        """The game so far as a server log, one JSON event per line. Needs "record": True in the configuration."""
        text = _text(lib().charter_saved_log, self._h, code.encode(), ",".join(names).encode())
        if text.startswith("error: "):
            raise ValueError(text[len("error: "):])
        return text

    def saved_state(self):
        """After each event of the saved log: [round, 1 if in setup, laws in force, points of each seat]."""
        return [json.loads(l) for l in _text(lib().charter_saved_state, self._h).splitlines() if l]
