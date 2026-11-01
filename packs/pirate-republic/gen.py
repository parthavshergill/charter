#!/usr/bin/env python3
"""Makes The Pirate Republic's meshes. Unlike Slime Parliament's soft shapes, these are hard-edged: hulls,
planks and sails are built from explicit faces, and the player's flat shading gives them facets. Run it from
anywhere. It writes meshes/<sha256>.mesh here and the id table for Lean. It uses no packages. The same code
always makes the same bytes. Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, math, os, struct
from math import sin, cos, sqrt, pi, atan2

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/PirateRepublic/Meshes.lean"


def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def mix(a, b, t):
    t = max(0., min(1., t))
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)
def sstep(a, b, x):
    t = max(0., min(1., (x - a) / (b - a)))
    return t * t * (3 - 2 * t)
def wave(x, z, f, s=0.):
    return (sin(f * x + 1.7 * sin(f * .63 * z + s)) * cos(f * z + 1.3 * sin(f * .71 * x + s)) + sin(f * .5 * (x + z) + 2.1 * s) * .5) / 1.5


WHITE = (1., 1., 1.)
SHADE = (.72, .72, .72)
WOOD, WOOD2, DARK, TAR = C(0x8A5A2E), C(0xB98449), C(0x4A2E18), C(0x1B1512)
PLANK, PLANK2 = C(0xC49A60), C(0x9C7240)
BONE, STONE, STONE2, IRON = C(0xF0E8D2), C(0x9A9486), C(0x6E695F), C(0x2B2D31)
GOLD, GOLD2, COPPER, BRASS = C(0xF6C22C), C(0xFFE27A), C(0xC8703A), C(0xC99A2E)
BLACK, RED, NAVYBLUE = C(0x101014), C(0xC8232A), C(0x1B2C5C)
LANTERN = C(0xFFC24A)


class M:
    """A mesh made of faces. Points pass through a place, a turn and a size set by `at`."""
    def __init__(self):
        self.vs, self.cs, self.ts, self.xf = [], [], [], (0, 0, 0, 0, 1)

    def at(self, x=0, y=0, z=0, rot=0, k=1):
        self.xf = (x, y, z, rot, k)
        return self

    def p(self, q):
        x, y, z, r, k = self.xf
        a, b, c = q[0] * k, q[1] * k, q[2] * k
        return (x + a * cos(r) + c * sin(r), y + b, z + c * cos(r) - a * sin(r))

    def v(self, q, c):
        self.vs.append(self.p(q))
        self.cs.append(c)
        return len(self.vs) - 1

    def poly(self, pts, col, out=None, two=False):
        """One flat face, as a fan. `out` is a point the face looks away from. `col` can be one colour per point."""
        cols = col if isinstance(col, list) else [col] * len(pts)
        ids = [self.v(q, c) for q, c in zip(pts, cols)]
        if out is not None:
            a, b, c = pts[0], pts[1], pts[2]
            u = (b[0] - a[0], b[1] - a[1], b[2] - a[2])
            w = (c[0] - a[0], c[1] - a[1], c[2] - a[2])
            n = (u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0])
            m = [sum(q[i] for q in pts) / len(pts) for i in range(3)]
            if n[0] * (m[0] - out[0]) + n[1] * (m[1] - out[1]) + n[2] * (m[2] - out[2]) < 0:
                ids.reverse()
        for i in range(1, len(ids) - 1):
            self.ts.append((ids[0], ids[i], ids[i + 1]))
            if two: self.ts.append((ids[0], ids[i + 1], ids[i]))

    def box(self, x, y, z, w, h, d, col, rot=0, top=None):
        """A box standing on y. `top` colours its top face."""
        c, s = cos(rot), sin(rot)
        pt = lambda a, b, e: (x + a * c + e * s, y + b, z + e * c - a * s)
        hw, hd = w / 2, d / 2
        ref = (x, y + h / 2, z)
        for a in (-hw, hw):
            self.poly([pt(a, 0, -hd), pt(a, 0, hd), pt(a, h, hd), pt(a, h, -hd)], col, ref)
        for e in (-hd, hd):
            self.poly([pt(-hw, 0, e), pt(hw, 0, e), pt(hw, h, e), pt(-hw, h, e)], col, ref)
        self.poly([pt(-hw, h, -hd), pt(hw, h, -hd), pt(hw, h, hd), pt(-hw, h, hd)], top or col, ref)

    def rod(self, a, b, ra, rb, col, n=5, caps=True):
        """A tapered round rod between two points."""
        d = (b[0] - a[0], b[1] - a[1], b[2] - a[2])
        L = sqrt(sum(x * x for x in d)) or 1
        d = (d[0] / L, d[1] / L, d[2] / L)
        h = (1, 0, 0) if abs(d[0]) < .8 else (0, 1, 0)
        u = (d[1] * h[2] - d[2] * h[1], d[2] * h[0] - d[0] * h[2], d[0] * h[1] - d[1] * h[0])
        ul = sqrt(sum(x * x for x in u))
        u = (u[0] / ul, u[1] / ul, u[2] / ul)
        w = (d[1] * u[2] - d[2] * u[1], d[2] * u[0] - d[0] * u[2], d[0] * u[1] - d[1] * u[0])
        ring = lambda c, r, i: tuple(c[j] + r * (cos(2 * pi * i / n) * u[j] + sin(2 * pi * i / n) * w[j]) for j in range(3))
        ref = tuple((a[j] + b[j]) / 2 for j in range(3))
        for i in range(n):
            self.poly([ring(a, ra, i), ring(a, ra, i + 1), ring(b, rb, i + 1), ring(b, rb, i)], col, ref)
        if caps:
            self.poly([ring(b, rb, i) for i in range(n)], col, ref)
            if ra > 0: self.poly([ring(a, ra, i) for i in range(n)], col, ref)

    def post(self, x, y, z, r, h, col, r2=None, n=5):
        self.rod((x, y, z), (x, y + h, z), r, r if r2 is None else r2, col, n)

    def ball(self, x, y, z, r, col, sy=1., n=7, m=4, base=None):
        """A faceted ball. `base` colours its lower half."""
        pt = lambda i, j: (x + r * cos(2 * pi * i / n) * sin(pi * j / m), y + r * sy * cos(pi * j / m), z + r * sin(2 * pi * i / n) * sin(pi * j / m))
        for i in range(n):
            for j in range(m):
                c = (base if base and j >= m / 2 else col)
                q = [pt(i, j), pt(i + 1, j), pt(i + 1, j + 1), pt(i, j + 1)]
                if j == 0: q = [q[0], q[2], q[3]]
                elif j == m - 1: q = q[:3]
                self.poly(q, c, (x, y, z))

    def barrel(self, x, y, z, r, h, col=WOOD, band=IRON, lying=False, rot=0):
        n = 7
        c, s = cos(rot), sin(rot)
        def pt(a, b, e):
            if lying: a, b, e = b - h / 2, a + r, e
            return (x + a * c + e * s, y + b, z + e * c - a * s)
        prof = [(0, .78, band), (.12, .96, col), (.5, 1.05, col), (.88, .96, col), (1, .78, band)]
        ref = pt(0, h / 2, 0)
        for (t0, w0, c0), (t1, w1, c1) in zip(prof, prof[1:]):
            for i in range(n):
                a, b = 2 * pi * i / n, 2 * pi * (i + 1) / n
                self.poly([pt(r * w0 * cos(a), t0 * h, r * w0 * sin(a)), pt(r * w0 * cos(b), t0 * h, r * w0 * sin(b)),
                           pt(r * w1 * cos(b), t1 * h, r * w1 * sin(b)), pt(r * w1 * cos(a), t1 * h, r * w1 * sin(a))], c0, ref)
        self.poly([pt(r * .78 * cos(2 * pi * i / n), h, r * .78 * sin(2 * pi * i / n)) for i in range(n)], WOOD2, ref)

    def sheet(self, f, nu, nv, two=True):
        """A cloth: f(u, v) gives a point and a colour, for u and v from 0 to 1."""
        ids = {}
        for i in range(nu + 1):
            for j in range(nv + 1):
                q, c = f(i / nu, j / nv)
                ids[(i, j)] = self.v(q, c)
        for i in range(nu):
            for j in range(nv):
                a, b, c, d = ids[(i, j)], ids[(i + 1, j)], ids[(i + 1, j + 1)], ids[(i, j + 1)]
                self.ts.extend([(a, b, c), (a, c, d)])
                if two: self.ts.extend([(a, c, b), (a, d, c)])


# ---- writing a mesh file

TABLE = []
MAX_TRIS = 12000


def write(name, m, motion=(0, 0, 0), stand=None):
    vs, cs, ts = m.vs, m.cs, m.ts
    assert len(ts) <= MAX_TRIS, f"{name} has {len(ts)} triangles"
    assert len(vs) < 65535, f"{name} has {len(vs)} vertices"
    # Points with the same place and colour are one point, which keeps the file small.
    seen, new, vs2, cs2 = {}, [], [], []
    for q, c in zip(vs, cs):
        k = (round(q[0], 4), round(q[1], 4), round(q[2], 4), round(c[0], 3), round(c[1], 3), round(c[2], 3))
        if k not in seen:
            seen[k] = len(vs2)
            vs2.append(q)
            cs2.append(c)
        new.append(seen[k])
    ts2 = [(new[a], new[b], new[c]) for a, b, c in ts]
    mn = [min(v[a] for v in vs2) for a in range(3)]
    mx = [max(v[a] for v in vs2) for a in range(3)]
    body = struct.pack("<4sII6f", b"GPM1", len(vs2), len(ts2), *mn, *mx)
    for v in vs2:
        body += struct.pack("<3H", *[round(65535 * (v[a] - mn[a]) / ((mx[a] - mn[a]) or 1)) for a in range(3)])
    for c in cs2:
        body += bytes(max(0, min(255, round(255 * x))) for x in c)
    for t in ts2:
        body += struct.pack("<3H", *t)
    sha = hashlib.sha256(body).hexdigest()
    with open(f"{OUT}/{sha}.mesh", "wb") as out: out.write(body)
    mean = tuple(sum(c[a] for c in cs2) / len(cs2) for a in range(3))
    tint = sum(round(255 * mean[a]) << (16 - 8 * a) for a in range(3))
    r = max(mx[0], -mn[0], mx[2], -mn[2])
    TABLE.append((name, sha, tint, motion, stand or f".cylinder {r * .9:.3f} {max(mx[1], .01):.3f}", len(ts2), len(body)))
    print(f"{name:16} {len(ts2):6} triangles {len(body):7} bytes", flush=True)


BARE = ".sphere 0.001"  # a part that is only detail has no stand-in worth seeing

# ---- ships. The bow points along +x. y = 0 is the wharf deck's plane, and the water lies at about -0.02.


def hull(m, L, B, deck, keel=-.05, sheer=.02, stern=.05, col=DARK, trim=WOOD2, n=10, band=None):
    """A hull, from sections along x. The stern is square and raised, and the bow comes to a point."""
    secs = []
    for i in range(n + 1):
        t = -1 + 2 * i / n
        w = B * (1 - t * t) if t > 0 else B * (1 - .45 * t * t)
        w = max(w, .002)
        h = deck + sheer * t * t + (stern * sstep(-.35, -.8, t))
        k = keel * (1 - .25 * t * t)
        secs.append((t * L, w, h, k))
    ref = (0, (deck + keel) / 2, 0)
    for (x0, w0, h0, k0), (x1, w1, h1, k1) in zip(secs, secs[1:]):
        for s in (-1, 1):
            m.poly([(x0, h0, s * w0), (x1, h1, s * w1), (x1, h1 - .35 * (h1 - k1), s * w1 * 1.02), (x0, h0 - .35 * (h0 - k0), s * w0 * 1.02)], [trim, trim, band or col, band or col], ref)
            m.poly([(x0, h0 - .35 * (h0 - k0), s * w0 * 1.02), (x1, h1 - .35 * (h1 - k1), s * w1 * 1.02), (x1, k1, s * w1 * .35), (x0, k0, s * w0 * .35)], col, ref)
        # The deck.
        m.poly([(x0, h0 - .012, -w0 * .88), (x1, h1 - .012, -w1 * .88), (x1, h1 - .012, w1 * .88), (x0, h0 - .012, w0 * .88)], PLANK, (0, -1, 0))
    x0, w0, h0, k0 = secs[0]
    m.poly([(x0, h0, -w0), (x0, h0, w0), (x0, k0, w0 * .35), (x0, k0, -w0 * .35)], trim, ref)
    return secs


def square_sail(x, y0, y1, w0, w1, belly, col):
    """A square sail across the ship, bellied toward the bow."""
    def f(u, v):
        hw = w0 + (w1 - w0) * v
        return (x + belly * sin(pi * u) * sin(pi * v), y0 + (y1 - y0) * v, (u - .5) * 2 * hw), col(u, v) if callable(col) else col
    return f


def tri_sail(a, b, c, belly, col):
    """A three-cornered sail."""
    def f(u, v):
        p = (a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u, a[2] + (b[2] - a[2]) * u)
        q = (p[0] + (c[0] - p[0]) * v, p[1] + (c[1] - p[1]) * v, p[2] + (c[2] - p[2]) * v)
        return (q[0], q[1], q[2] + belly * sin(pi * u) * sin(pi * min(1, v * 1.2))), col
    return f


def pennant(m, x, y, z, w, h, col, n=3):
    m.sheet(lambda u, v: ((x - w * u, y + h * (v - .5) * (1 - .85 * u), z + .012 * sin(u * 5)), col), n, 1)


def sloop():
    h = M()
    hull(h, .31, .082, .036, col=C(0x3A2413), trim=C(0xA87438), n=6)
    h.post(.03, .03, 0, .009, .38, TAR, .006, n=4)
    h.rod((.03, .10, 0), (-.2, .13, 0), .005, .004, TAR, n=3)
    h.rod((.03, .36, 0), (.37, .05, 0), .002, .002, TAR, n=3, caps=False)
    h.box(-.2, .03, 0, .1, .045, .1, WOOD)
    write("sloop_hull", h, (0, .022, 0), ".box 0.55 0.06 0.13")
    s = M()
    s.sheet(square_sail(.03, .15, .37, .165, .12, .06, WHITE), 5, 3)
    s.sheet(tri_sail((.05, .075, 0), (.045, .34, 0), (.33, .06, 0), .02, WHITE), 3, 2)
    s.sheet(tri_sail((.02, .095, 0), (.015, .34, 0), (-.26, .105, 0), -.02, WHITE), 3, 2)
    pennant(s, .03, .4, 0, .09, .04, WHITE)
    # A strake along each side, so the owner shows from above as well.
    for side in (-1, 1):
        s.sheet(lambda u, v, side=side: ((-.27 + .52 * u, .012 + .018 * v, side * .0845 * (1 - ((u * .52 - .27) / .31) ** 2 * (1 if u * .52 - .27 > 0 else .45))), WHITE), 5, 1)
    write("sloop_sail", s, (0, .022, 0), BARE)
    for k, bands in ((1, [.5]), (2, [.32, .68]), (3, [.2, .5, .8])):
        b = M()
        for t in bands:
            y0, y1 = .15 + .22 * (t - .085), .15 + .22 * (t + .085)
            def strip(u, v, y0=y0, y1=y1):
                vv = (y0 - .15 + (y1 - y0) * v) / .22
                hw = .165 - .045 * vv
                return (.03 + .064 * sin(pi * u) * sin(pi * vv), y0 + (y1 - y0) * v, (u - .5) * 2 * hw * 1.015), TAR
            b.sheet(strip, 5, 1)
        write(f"sloop_marks{k}", b, (0, .022, 0), BARE)


def boom():
    """A link piece that a law made: a chain of floating logs across a channel."""
    m = M()
    for i in range(5):
        x = -.36 + i * .18
        m.rod((x - .08, .0, .015 * (-1) ** i), (x + .08, .0, -.015 * (-1) ** i), .03, .03, WOOD, n=5)
    m.post(-.4, -.03, 0, .025, .1, TAR, n=4)
    m.post(.4, -.03, 0, .025, .1, TAR, n=4)
    write("boom", m, (0, .012, 0), ".box 0.8 0.05 0.06")
    t = M()
    for i in range(5):
        t.box(-.36 + i * .18, .028, 0, .03, .012, .07, WHITE)
    write("boom_mark", t, (0, .012, 0), BARE)


def deck(m, r=.2, y=.05, n=6):
    """A wharf's platform of planks on stilts."""
    for i in range(n):
        a = 2 * pi * (i + .5) / n
        m.post(r * .86 * cos(a), -.05, r * .86 * sin(a), .012, y + .07, DARK, n=4)
    pts = [(r * cos(2 * pi * i / n), y, r * sin(2 * pi * i / n)) for i in range(n)]
    low = [(q[0], y - .016, q[2]) for q in pts]
    ref = (0, y - .01, 0)
    cols = [PLANK if i % 2 else PLANK2 for i in range(n)]
    m.poly(pts, cols, ref)
    for i in range(n):
        m.poly([pts[i], pts[(i + 1) % n], low[(i + 1) % n], low[i]], DARK, ref)


def wharf():
    m = M()
    deck(m)
    # A gangway out to sea, a shack, barrels and mooring posts.
    m.box(.2, .048, .09, .2, .008, .06, PLANK2, rot=-.45)
    m.box(-.05, .05, -.05, .17, .1, .14, C(0x7C5A34), top=C(0x7C5A34))
    m.box(-.05, .05, .018, .035, .065, .008, TAR)
    m.barrel(.11, .05, -.06, .03, .06)
    m.barrel(.1, .05, .03, .025, .05, col=C(0xB0612C))
    m.post(.0, .05, .14, .01, .19, TAR, n=4)
    m.post(.16, .03, -.14, .012, .06, DARK, n=4)
    m.post(-.17, .05, .09, .008, .14, TAR, n=4)
    m.box(-.17, .19, .09, .03, .01, .03, TAR)
    write("wharf_body", m, stand=".cylinder 0.2 0.15")
    t = M()
    # The roof and the flag take the seat's colour.
    x, z, w, d, y, h = -.05, -.05, .2, .17, .15, .07
    for s in (-1, 1):
        t.poly([(x - w / 2, y, z + s * d / 2), (x + w / 2, y, z + s * d / 2), (x + w / 2, y + h, z), (x - w / 2, y + h, z)], [SHADE, SHADE, WHITE, WHITE], (x, y, z))
    for s in (-1, 1):
        t.poly([(x + s * w / 2, y, z - d / 2), (x + s * w / 2, y, z + d / 2), (x + s * w / 2, y + h, z)], SHADE, (x, y, z))
    t.sheet(lambda u, v: ((.0 + .15 * u, .15 + .09 * v * (1 - .4 * u), .14 + .012 * sin(u * 7)), WHITE), 4, 1)
    write("wharf_tint", t, stand=BARE)
    g = M()
    g.ball(-.17, .165, .09, .026, LANTERN, n=5, m=3)
    write("wharf_light", g, (0, 0, .75), BARE)


def fort():
    m = M()
    n, R = 8, .27
    wall = lambda r, y: [(r * cos(2 * pi * i / n + .3), y, r * sin(2 * pi * i / n + .3)) for i in range(n)]
    ref = (0, .1, 0)
    a, b = wall(R, -.04), wall(R * .9, .15)
    dark, mid = C(0x4A4A52), C(0x77777F)
    for i in range(n):
        j = (i + 1) % n
        m.poly([a[i], a[j], b[j], b[i]], [dark, dark, mid, mid], ref)
    m.poly(b, C(0x8E8A7E), (0, 0, 0))
    for i in range(n * 2):
        ang = 2 * pi * i / (n * 2) + .3
        if i % 2 == 0:
            m.box(R * .84 * cos(ang), .15, R * .84 * sin(ang), .05, .04, .05, mid, rot=-ang)
    for ang in (.5, 1.1, -.2, 1.9):
        cx, cz = (R + .02) * cos(ang), (R + .02) * sin(ang)
        m.rod((cx * .72, .18, cz * .72), (cx * 1.12, .2, cz * 1.12), .017, .012, IRON, n=5)
    m.post(-.04, .15, -.04, .095, .13, mid, .08, n=7)
    m.post(-.04, .28, -.04, .09, .022, dark, n=7)
    for i in range(7):
        ang = 2 * pi * i / 7
        m.box(-.04 + .08 * cos(ang), .3, -.04 + .08 * sin(ang), .026, .024, .026, mid)
    m.post(-.04, .28, -.04, .011, .36, TAR, n=4)
    m.barrel(.13, .15, -.04, .024, .045)
    write("fort_body", m, stand=".cylinder 0.26 0.3")
    t = M()
    t.sheet(lambda u, v: ((-.04 + .27 * u, .46 + .17 * v * (1 - .35 * u) + .08 * u, -.04 + .02 * sin(u * 7)), WHITE), 5, 2)
    a2, b2 = wall(R * .97, .02), wall(R * .925, .1)
    for i in range(n):
        j = (i + 1) % n
        t.poly([a2[i], a2[j], b2[j], b2[i]], [SHADE, SHADE, WHITE, WHITE], ref)
    write("fort_tint", t, stand=BARE)


def flagship():
    m = M()
    hull(m, .42, .105, .07, keel=-.05, stern=.11, col=C(0x17120E), trim=GOLD, n=8, band=C(0x2A2018))
    for x in (.16, -.01, -.2):
        h = .55 if x == -.01 else .46
        m.post(x, .05, 0, .011, h, TAR, .006, n=4)
    m.rod((.2, .09, 0), (.52, .17, 0), .007, .003, TAR, n=3)
    for i in range(4):
        m.ball(.25 - i * .13, .09, .096 - i * .001, .012, IRON, n=4, m=2)
        m.ball(.25 - i * .13, .09, -.096 + i * .001, .012, IRON, n=4, m=2)
    m.box(-.34, .13, 0, .1, .05, .13, C(0x2A2018), top=GOLD)
    for x, y0, y1, w0, w1 in ((.16, .17, .33, .13, .105), (.16, .35, .46, .09, .07), (-.01, .2, .39, .15, .12), (-.01, .41, .54, .1, .08), (-.2, .2, .33, .11, .09)):
        m.sheet(square_sail(x, y0, y1, w0, w1, .035, C(0x18181C)), 4, 2)
    write("flagship_body", m, (0, .016, 0), ".box 0.75 0.3 0.2")
    t = M()
    t.sheet(lambda u, v: ((-.01 + (.058 * sin(pi * u)) * .6, .275 + .03 * v, (u - .5) * 2 * .15), WHITE), 4, 1)
    t.sheet(lambda u, v: ((.16 + (.058 * sin(pi * u)) * .6, .24 + .03 * v, (u - .5) * 2 * .13), WHITE), 4, 1)
    pennant(t, -.01, .585, 0, .16, .07, WHITE, n=4)
    pennant(t, -.2, .49, 0, .1, .045, WHITE)
    write("flagship_tint", t, (0, .016, 0), BARE)


def privateer():
    m = M()
    hull(m, .34, .085, .05, keel=-.05, stern=.07, col=C(0xE4DAC0), trim=C(0x2A2018), n=7, band=C(0x24344E))
    for x in (.1, -.1):
        m.post(x, .04, 0, .009, .4, DARK, .005, n=4)
    m.rod((.15, .07, 0), (.44, .13, 0), .006, .003, DARK, n=3)
    for x, y0, y1, w0, w1 in ((.1, .15, .29, .11, .085), (.1, .3, .4, .075, .055), (-.1, .15, .29, .1, .08), (-.1, .3, .38, .065, .05)):
        m.sheet(square_sail(x, y0, y1, w0, w1, .03, C(0xF4EFE0)), 4, 2)
    write("privateer_body", m, (0, .018, 0), ".box 0.6 0.25 0.17")
    t = M()
    pennant(t, -.1, .43, 0, .13, .06, WHITE, n=4)
    pennant(t, .1, .43, 0, .1, .04, WHITE, n=3)
    def stripe(u, v):
        return (-.3 + .55 * u, .028 + .012 * v + .01 * (u - .5) ** 2, .083 * (1 - (2 * u - .9) ** 2 * .45)), WHITE
    t.sheet(stripe, 4, 1)
    t.sheet(lambda u, v: (lambda q: ((q[0][0], q[0][1], -q[0][2]), q[1]))(stripe(u, v)), 4, 1)
    write("privateer_tint", t, (0, .018, 0), BARE)


def made():
    """Pieces a law makes: a careened hull, a lighthouse and a powder magazine. The seat's colour is the body."""
    a = M()
    a.at(0, .06, 0, 0, 1)
    for i in range(7):
        t = -1 + 2 * i / 6
        w = .13 * (1 - t * t) + .01
        pts = [(t * .24, .06 * (1 - t * t * .3), -w), (t * .24, -.03, -w * .6), (t * .24, -.05, 0), (t * .24, -.03, w * .6), (t * .24, .06 * (1 - t * t * .3), w)]
        if i < 6:
            t2 = t + 2 / 6
            w2 = .13 * (1 - t2 * t2) + .01
            q = [(t2 * .24, .06 * (1 - t2 * t2 * .3), -w2), (t2 * .24, -.03, -w2 * .6), (t2 * .24, -.05, 0), (t2 * .24, -.03, w2 * .6), (t2 * .24, .06 * (1 - t2 * t2 * .3), w2)]
            for k in range(4):
                a.poly([pts[k], q[k], q[k + 1], pts[k + 1]], WHITE if k % 2 else SHADE, (0, .2, 0))
    a.at()
    write("made_hull", a, stand=".cylinder 0.15 0.14")
    b = M()
    b.post(0, 0, 0, .085, .28, WHITE, .055, n=7)
    b.ball(0, .3, 0, .05, WHITE, n=6, m=3)
    write("made_tower", b, (0, 0, 0), ".cone 0.08 0.3")
    c = M()
    c.box(0, 0, 0, .22, .11, .18, SHADE)
    for s in (-1, 1):
        c.poly([(-.12, .11, s * .1), (.12, .11, s * .1), (.12, .18, 0), (-.12, .18, 0)], WHITE, (0, .1, 0))
    for s in (-1, 1):
        c.poly([(s * .12, .11, -.1), (s * .12, .11, .1), (s * .12, .18, 0)], SHADE, (0, .1, 0))
    write("made_magazine", c, stand=".box 0.22 0.18 0.18")


# ---- tiles: an exact hexagon of water, with one island in it. y = 0.14 is the water, y = 0.16 is the deck plane.

N = 15
WATER = .14
RIM = C(0x0E8BA8)


def hexd(x, z):
    ax, az = abs(x), abs(z)
    return max(ax, ax * .5 + az * .866)


def lattice(n=N):
    """The points of a hexagon, n steps to a side, pointy along z. Its edges are exact, so tiles meet."""
    ids, pts = {}, []
    for q in range(-n, n + 1):
        for s in range(-n, n + 1):
            if abs(q + s) > n: continue
            ids[(q, s)] = len(pts)
            pts.append((.866 * q / n, (.5 * q + s) / n))
    return ids, pts


def water_col(x, z, shore, tone=(C(0x35E0CF), C(0x12AEBE))):
    """Water by how far it is from the shore. The rim has one colour, so neighbouring tiles match."""
    c = mix(C(0xBFF5E4), tone[0], sstep(.0, .07, shore))
    c = mix(c, tone[1], sstep(.06, .3, shore))
    c = mix(c, mix(c, C(0x7CF0E0), .35), sstep(.25, .8, wave(x, z, 15., 1.)) * (1 - sstep(.2, .5, shore)))
    return mix(c, RIM, sstep(.7, .86, hexd(x, z)))


def tile(name, land, hgt, col, seed=1., extra=None, tone=None, motion=(0, 0, 0)):
    """land(x, z) is above 0 on land. hgt gives the land's height over the water, col its colour."""
    m = M()
    ids, pts = lattice()
    vert = []
    for (x, z) in pts:
        L = land(x, z)
        r = sqrt(x * x + z * z)
        if L > 0:
            y = WATER + .018 * sstep(0, .05, L) + hgt(x, z, L) * sstep(.26, .4, r) * sstep(.02, .15, L)
            c = mix(C(0xF1DFA8), col(x, z, L), sstep(.05, .13, L))
        else:
            y = WATER - .012 * sstep(0, .07, -L) + .002 * wave(x, z, 12., seed)
            c = water_col(x, z, -L, tone) if tone else water_col(x, z, -L)
        if r < .27:  # the number token sits here
            y = min(y, .162) if L > 0 else y
        vert.append(((x, y, z), c))
    for (q, s), i in ids.items():
        for a, b in (((q + 1, s), (q, s + 1)), ((q + 1, s), (q + 1, s - 1))):
            if a in ids and b in ids:
                A, B, D = vert[i], vert[ids[a]], vert[ids[b]]
                m.poly([A[0], B[0], D[0]], [A[1], B[1], D[1]], (A[0][0], -9, A[0][2]))
    # A skirt down to the base, in deep water's colour.
    corners = [(0, 1), (.866, .5), (.866, -.5), (0, -1), (-.866, -.5), (-.866, .5)]
    for i in range(6):
        a, b = corners[i], corners[(i + 1) % 6]
        m.poly([(a[0], WATER, a[1]), (b[0], WATER, b[1]), (b[0], 0, b[1]), (a[0], 0, a[1])], [RIM, RIM, C(0x0B5A73), C(0x0B5A73)], (0, .1, 0))
    if extra: extra(m)
    write(name, m, motion, ".hexPrism 0.96 0.15")


def shore(s, base=.6, a=.09, b=.05):
    def f(x, z):
        t = atan2(z, x)
        return base + a * sin(2 * t + s) + b * sin(5 * t + 2.3 * s) - sqrt(x * x + z * z)
    return f


def jungle(x, z, L):
    return mix(mix(C(0x1E6B34), C(0x3E9A3E), sstep(-.3, .5, wave(x, z, 11., 1.))), C(0x15502E), sstep(.2, .7, wave(x, z, 7., 2.)))


def tiles():
    tile("tile_timber", shore(1.2, .63), lambda x, z, L: .012 + .05 * sstep(.04, .3, L) * (.6 + .4 * wave(x, z, 9., 1.)), jungle, 1.)

    def cane(x, z, L):
        rows = sstep(-.4, .4, sin(34 * (x * .8 + z * .6)))
        return mix(mix(C(0x9BC93A), C(0xE1D65A), rows), C(0xC9A74A), sstep(.35, .75, wave(x, z, 6., 4.)))

    def still(m):
        # A rum still behind the token: a thatched shed, a copper pot and barrels.
        m.at(-.47, .165, -.3)
        m.box(0, 0, 0, .2, .11, .16, C(0x6A4726))
        for s in (-1, 1):
            m.poly([(-.12, .11, s * .1), (.12, .11, s * .1), (.12, .19, 0), (-.12, .19, 0)], C(0xD8B45A), (0, .1, 0))
        m.at(-.2, .165, -.52)
        m.post(0, 0, 0, .06, .09, COPPER, .03, n=7)
        m.post(0, .09, 0, .012, .07, COPPER, n=4)
        m.rod((0, .16, 0), (.12, .11, 0), .009, .009, COPPER, n=3)
        m.at()

    tile("tile_rum", shore(3.1, .62, .07, .06), lambda x, z, L: .01 + .012 * sin(34 * (x * .8 + z * .6)), cane, 2., still)

    def basalt(x, z, L):
        c = mix(C(0x1C1C22), C(0x3B3A40), sstep(-.4, .5, wave(x, z, 13., 3.)))
        c = mix(c, C(0xF2D22A), .95 * sstep(.5, .72, wave(x, z, 8.5, 5.)))
        return mix(c, C(0xF0531A), .95 * sstep(.45, .7, wave(x + .3, z, 17., 6.)))

    def crag(x, z, L):
        a = sqrt((x + .36) ** 2 + (z + .36) ** 2)
        b = sqrt((x + .58) ** 2 + (z - .05) ** 2)
        c = sqrt((x - .05) ** 2 + (z + .58) ** 2)
        return .012 + .03 * wave(x, z, 15., 2.) * .5 + .3 * max(0, 1 - a / .28) + .13 * max(0, 1 - b / .2) + .13 * max(0, 1 - c / .2)

    tile("tile_powder", shore(5.3, .64, .06, .07), crag, basalt, 3.)

    def prize_land(x, z):
        # A thin crescent of sand behind the token, and nothing more.
        d = sqrt((x + .48) ** 2 + (z + .48) ** 2)
        return .16 - abs(d - .34) * 1.6 - max(0, .22 - sqrt(x * x + z * z))

    def wreck(m):
        # A broken galleon, half under the water, and a mast that still stands.
        m.at(-.33, .1, -.58, -.5)
        hull(m, .3, .1, .09, keel=-.04, stern=.09, col=C(0x2A1A10), trim=C(0x7A5228), n=6)
        m.rod((.06, .08, 0), (.16, .44, .02), .014, .009, DARK, n=4)
        m.rod((.11, .28, -.1), (.13, .29, .12), .007, .006, DARK, n=3)
        m.sheet(lambda u, v: ((.12 + .02 * v, .2 + .08 * v - .02 * sin(u * 9) * (1 - v), (u - .5) * .2), C(0xD8CDAE) if (u * 3) % 1 < .8 else C(0xB9AC8A)), 4, 1)
        m.at()

    tile("tile_plunder", prize_land, lambda x, z, L: .004, lambda x, z, L: C(0xF4D98A), 4., wreck, (C(0x2A6FD8), C(0x153C9C)))

    def nassau(x, z):
        return .84 - hexd(x, z)

    def boards(x, z, L):
        r = hexd(x, z)
        c = mix(C(0xD9BC82), C(0xC9A566), sstep(-.3, .4, wave(x, z, 18., 5.)))
        if .34 < r < .62:
            c = mix(C(0x96683A), C(0xB98449), .5 + .5 * sin(40 * (x + z)))
        return c

    tile("tile_nassau", nassau, lambda x, z, L: .004, boards, 5.)


def bits():
    q = M()
    for i in range(6):
        a, b = pi / 6 + i * pi / 3, pi / 6 + (i + 1) * pi / 3
        co = lambda r, t: (r * cos(t), .012, r * sin(t))
        q.poly([co(.8, a), co(.8, b), co(.96, b), co(.96, a)], C(0xFFD84A), (0, -9, 0))
    write("hot_ring", q, (0, 0, .7), BARE)

    # Palms sway. The trunk leans a little, and the fronds droop.
    p = M()
    p.rod((0, 0, 0), (.02, .1, .005), .014, .011, C(0x7A5A36), n=4)
    p.rod((.02, .1, .005), (.05, .2, .01), .011, .008, C(0x8A6A42), n=4)
    for i in range(6):
        a = 2 * pi * i / 6 + .4
        tx, tz = .05 + .13 * cos(a), .01 + .13 * sin(a)
        mx, mz = .05 + .07 * cos(a), .01 + .07 * sin(a)
        wx, wz = -sin(a) * .022, cos(a) * .022
        col = C(0x2E8F3C) if i % 2 else C(0x4BAF46)
        p.poly([(.05, .2, .01), (mx + wx, .235, mz + wz), (mx - wx, .235, mz - wz)], col, two=True)
        p.poly([(mx + wx, .235, mz + wz), (tx, .15, tz), (mx - wx, .235, mz - wz)], col, two=True)
    write("palm", p, (0, .03, 0), ".cone 0.08 0.2")

    k = M()
    k.barrel(0, 0, 0, .032, .065, col=C(0x8A5A2E))
    k.barrel(.07, 0, .025, .028, .055, col=C(0xB03A24))
    k.barrel(.03, .0, -.06, .025, .05, col=C(0x8A5A2E), band=C(0xE8DAAA))
    write("kegs", k, stand=".cylinder 0.05 0.07")

    c = M()
    for dx, dz, h in ((0, 0, .1), (.03, .02, .085), (-.03, .015, .09), (.01, -.03, .08), (-.02, -.02, .07)):
        c.rod((dx, 0, dz), (dx * 1.3, h, dz * 1.3), .006, .004, C(0xB4D45A), n=3)
        c.poly([(dx * 1.3, h, dz * 1.3), (dx * 1.3 + .035, h - .035, dz * 1.3 + .012), (dx * 1.3 + .01, h - .012, dz * 1.3 - .012)], C(0x7FB23A), two=True)
    write("cane", c, (0, .025, 0), ".cone 0.03 0.1")

    r = M()
    r.poly([(-.04, 0, -.03), (.05, 0, -.02), (.0, .07, 0)], C(0x34343A), (0, 0, .2))
    r.poly([(.05, 0, -.02), (.03, 0, .05), (.0, .07, 0)], C(0xF2D22A), (-.1, 0, -.1))
    r.poly([(.03, 0, .05), (-.04, 0, -.03), (.0, .07, 0)], C(0x24242A), (.2, 0, -.1))
    write("rock", r, stand=".cone 0.04 0.07")

    h = M()
    h.at(0, 0, 0)
    h.box(0, 0, 0, .12, .05, .08, C(0x6A3F1C))
    h.box(0, .05, -.03, .12, .03, .02, C(0x4A2A12))
    h.box(0, .046, .008, .105, .012, .062, GOLD, top=GOLD2)
    h.ball(.02, .056, .01, .02, GOLD2, n=5, m=3)
    h.ball(-.025, .056, .0, .018, GOLD, n=5, m=3)
    write("chest", h, (0, 0, .28), ".box 0.12 0.08 0.08")

    o = M()
    o.post(0, 0, 0, .03, .007, GOLD, n=7)
    o.post(.012, .006, .008, .027, .007, GOLD2, n=7)
    write("coin", o, (0, 0, .4), ".cylinder 0.03 0.01")

    s = M()
    s.poly([(-.05, 0, 0), (.05, 0, 0), (0, .08, -.018)], C(0x4A5560), (0, 0, .2), two=True)
    write("fin", s, (0, .08, 0), BARE)

    g = M()
    n = 5
    for i in range(n):
        a, b = -.6 + 1.2 * i / n, -.6 + 1.2 * (i + 1) / n
        for r0, r1, col in ((.14, .158, C(0x9FDCDC)),):
            g.poly([(r0 * sin(a), .004, r0 * cos(a) - .15), (r1 * sin(a), .004, r1 * cos(a) - .15), (r1 * sin(b), .004, r1 * cos(b) - .15), (r0 * sin(b), .004, r0 * cos(b) - .15)], col, (0, -9, 0))
    write("glint", g, (.12, 0, .5), BARE)


# ---- the square, and what a law raises


def skull_flag(u, v):
    """Black cloth, with a skull and crossed bones. u runs from the pole, and v runs up."""
    x, y = (u - .5) * 1.4, (v - .5) * 1.0
    col = C(0x0E0E12)
    # Crossed bones.
    for s in (-1, 1):
        d = abs(y - .0 - s * x * .62 + .19) / 1.17
        if d < .035 and abs(x) < .36: col = BONE
    sk = sqrt((x * .92) ** 2 + (y - .09) ** 2)
    if sk < .19: col = BONE
    if abs(x) < .1 and -.14 < y < -.02: col = BONE
    if sqrt((x - .075) ** 2 + (y - .1) ** 2) < .05 or sqrt((x + .075) ** 2 + (y - .1) ** 2) < .05: col = C(0x0E0E12)
    if abs(x) < .018 and -.03 < y < .03: col = C(0x0E0E12)
    return col


def square():
    m = M()
    m.post(0, 0, 0, .13, .02, DARK, n=8)
    for i in range(6):
        a = 2 * pi * i / 6
        m.barrel(.1 * cos(a), .02, .1 * sin(a), .036, .075, col=WOOD if i % 2 else C(0x6A3F1C))
    m.post(0, .02, 0, .026, 1.12, TAR, .012, n=5)
    m.rod((-.09, .86, 0), (.09, .86, 0), .008, .008, TAR, n=3)
    m.ball(0, 1.14, 0, .025, GOLD, n=5, m=3)
    write("square_mast", m, stand=".cone 0.13 1.1")
    f = M()
    W, H = .64, .44
    def cloth(u, v):
        ripple = .035 * sin(u * 7.5 + v * 1.2) * sstep(0, .25, u)
        return (.015 + W * u, .66 + H * v - .03 * u, ripple), skull_flag(u, v)
    f.sheet(cloth, 34, 24)
    write("square_flag", f, (0, .018, 0), BARE)


def base(m, w=.1):
    m.box(0, 0, 0, w * 1.5, .022, w * 1.5, PLANK2, top=PLANK)


def monuments():
    # A cost: a balance with a coin in each pan.
    m = M()
    base(m)
    m.post(0, .02, 0, .014, .2, DARK, n=4)
    m.box(0, .22, 0, .19, .012, .016, BRASS)
    for s in (-1, 1):
        m.rod((s * .09, .22, 0), (s * .09, .15, 0), .003, .003, IRON, n=3)
        m.post(s * .09, .135, 0, .045, .012, BRASS, n=7)
        m.post(s * .09, .147, 0, .025, .012, GOLD, n=6)
    write("mon_cost", m, stand=".cone 0.08 0.25")
    # Points: an open chest of gold.
    m = M()
    base(m)
    m.box(0, .02, 0, .15, .075, .1, C(0x6A3F1C))
    m.box(0, .095, -.05, .15, .05, .02, C(0x4A2A12))
    m.box(0, .09, .008, .135, .012, .078, GOLD, top=GOLD2)
    m.ball(.02, .1, .0, .03, GOLD2, n=5, m=3)
    m.ball(-.035, .1, .015, .024, GOLD, n=5, m=3)
    m.ball(0, .135, -.01, .017, GOLD2, n=5, m=3)
    write("mon_points", m, (0, 0, .18), ".box 0.15 0.14 0.1")
    # The bank: coins stacked on a barrel.
    m = M()
    base(m)
    m.barrel(0, .02, 0, .06, .1)
    for i in range(5):
        m.post(.004 * (i % 2), .12 + .017 * i, .003 * ((i + 1) % 2), .04, .016, GOLD if i % 2 else GOLD2, n=7)
    write("mon_bank", m, (0, 0, .15), ".cylinder 0.07 0.2")
    # A harvest: a stack of rum barrels.
    m = M()
    base(m)
    for s in (-1, 1):
        m.barrel(s * .048, .022, .012, .044, .09, col=C(0xA0642C), lying=False)
    m.barrel(0, .11, .012, .04, .085, col=C(0xB57733), band=C(0xE8DAAA))
    write("mon_harvest", m, stand=".cylinder 0.09 0.2")
    # A build: the ribs of a ship on the stocks.
    m = M()
    base(m)
    for i in range(5):
        x = -.08 + i * .04
        h = .13 + .05 * (1 - abs(i - 2) / 2)
        for s in (-1, 1):
            m.rod((x, .022, 0), (x, h, s * .058), .008, .006, WOOD2, n=3)
    m.rod((-.1, .024, 0), (.1, .024, 0), .012, .01, DARK, n=4)
    write("mon_build", m, stand=".box 0.2 0.18 0.14")
    # A round's end: a ship's bell in a frame.
    m = M()
    base(m)
    for s in (-1, 1):
        m.rod((s * .07, .02, 0), (s * .06, .24, 0), .012, .009, DARK, n=4)
    m.rod((-.075, .24, 0), (.075, .24, 0), .012, .012, DARK, n=4)
    m.rod((0, .225, 0), (0, .165, 0), .022, .032, GOLD, n=7)
    m.rod((0, .165, 0), (0, .115, 0), .032, .058, GOLD2, n=7)
    m.ball(0, .1, 0, .013, IRON, n=4, m=2)
    write("mon_round", m, (0, 0, .12), ".cone 0.08 0.25")
    # A roll: two dice on a keg.
    m = M()
    base(m)
    m.barrel(0, .022, 0, .058, .08)
    m.box(-.022, .104, .012, .068, .068, .068, BONE, rot=.3)
    m.box(.02, .172, -.008, .056, .056, .056, BONE, rot=-.5)
    for dx, dz in ((-.012, -.012), (.012, .012)):
        m.box(.02 + dx, .228, -.008 + dz, .012, .003, .012, TAR)
    m.box(-.022, .173, .012, .012, .003, .012, RED)
    write("mon_roll", m, stand=".cylinder 0.07 0.25")
    # A new piece: a gilded model ship on a stand.
    m = M()
    base(m)
    m.post(0, .02, 0, .012, .05, DARK, n=4)
    hull(m.at(0, .1, 0, 0, .5), .31, .082, .036, col=GOLD, trim=GOLD2, n=4)
    m.at()
    m.post(.015, .11, 0, .005, .17, DARK, n=3)
    m.sheet(square_sail(.015, .14, .265, .07, .05, .018, BONE), 3, 2)
    write("mon_piece", m, stand=".box 0.3 0.15 0.14")
    # A repeal, or any other change to a rule: a broken mast with a torn flag.
    m = M()
    base(m)
    m.post(0, .02, 0, .024, .16, DARK, .017, n=5)
    m.poly([(-.018, .18, 0), (.018, .18, 0), (.006, .225, .006)], C(0xD9B47A), two=True)
    m.rod((.04, .022, .05), (.14, .05, .1), .014, .012, DARK, n=4)
    m.sheet(lambda u, v: ((.01 + .09 * u, .1 + .055 * v - .03 * u, .02 * sin(u * 8)), BLACK if (u * 2.3 + v) % 1 < .75 else RED), 3, 1)
    write("mon_repeal", m, stand=".cylinder 0.05 0.2")


# ---- the world: a deep sea, islets, the Navy on the horizon and a sandbar for the treasury.


def sea():
    m = M()
    R, n = 30., 42
    step = 2 * R / n
    pt = lambda i, j: (-R + i * step, -R + j * step)
    def col(x, z):
        r = sqrt(x * x + z * z)
        c = mix(C(0x07506E), C(0x042238), sstep(5.2, 10., r))
        c = mix(c, C(0x0A6585), .5 * sstep(.2, .8, wave(x, z, .9, 1.)) * (1 - sstep(5, 12, r)))
        return mix(c, C(0x021626), .6 * sstep(.2, .9, wave(x, z, .55, 3.)))
    for i in range(n):
        for j in range(n):
            q = [pt(i, j), pt(i + 1, j), pt(i + 1, j + 1), pt(i, j + 1)]
            ps = [(a, .012, b) for a, b in q]
            cs = [col(a, b) for a, b in q]
            m.poly(ps[:3], cs[:3], (0, -9, 0))
            m.poly([ps[0], ps[2], ps[3]], [cs[0], cs[2], cs[3]], (0, -9, 0))
    write("sea", m, stand=".box 60 0.01 60")


def islet():
    m = M()
    n = 9
    pts = [(.5 * (1 + .25 * sin(3 * i)) * cos(2 * pi * i / n), .08, .4 * (1 + .25 * sin(3 * i)) * sin(2 * pi * i / n)) for i in range(n)]
    foam = [(q[0] * 1.35, .012, q[2] * 1.35) for q in pts]
    for i in range(n):
        j = (i + 1) % n
        m.poly([foam[i], foam[j], pts[j], pts[i]], [C(0xBFF5E4), C(0xBFF5E4), C(0xF1DFA8), C(0xF1DFA8)], (0, -9, 0))
    top = [(q[0] * .6, .15, q[2] * .6) for q in pts]
    for i in range(n):
        j = (i + 1) % n
        m.poly([pts[i], pts[j], top[j], top[i]], [C(0xF1DFA8), C(0xF1DFA8), C(0x2C8A3C), C(0x2C8A3C)], (0, -9, 0))
    m.poly(top, C(0x1E6B34), (0, 0, 0))
    write("islet", m, stand=".cylinder 0.45 0.15")


def man_of_war():
    """The Royal Navy: a tall ship on the horizon, from the first round of the game."""
    m = M()
    hull(m, 1.25, .28, .34, keel=-.2, stern=.3, sheer=.1, col=C(0x1E1A16), trim=C(0xE8C14A), n=12, band=C(0xE8DFC4))
    # Two rows of gun ports.
    for row, y in enumerate((.22, .13)):
        for i in range(9):
            t = -.82 + i * .2
            w = .28 * (1 - t * t) if t > 0 else .28 * (1 - .45 * t * t)
            for s in (-1, 1):
                m.box(t * 1.25, y + .02 * t * t, s * (w + .004), .05, .04, .012, TAR)
    m.box(-.98, .5, 0, .34, .2, .36, C(0x1E1A16), top=C(0xE8C14A))
    masts = [(.55, 1.45), (-.05, 1.8), (-.68, 1.35)]
    for x, h in masts:
        m.post(x, .25, 0, .03, h, DARK, .012, n=5)
        ys = [(.55, .95, .34, .28), (1.0, 1.3, .25, .19), (1.34, 1.56, .17, .13)]
        for y0, y1, w0, w1 in ys:
            if y1 > h + .15: continue
            def col(u, v):
                cross = abs(u - .5) < .07 or abs(v - .5) < .1
                return RED if (x == -.05 and y0 == .55 and cross) else BONE
            m.sheet(square_sail(x, y0, y1, w0 * 1.25, w1 * 1.25, .08, col), 7, 5, two=True)
            m.rod((x, y1, -w1 * 1.3), (x, y1, w1 * 1.3), .009, .009, DARK, n=3, caps=False)
    m.rod((1.0, .45, 0), (1.72, .8, 0), .018, .008, DARK, n=4)
    m.sheet(lambda u, v: ((-.05 - .3 * u, 2.0 + .1 * (v - .5) * (1 - .7 * u), .02 * sin(u * 6)), RED), 3, 1)
    write("navy", m, (0, .008, 0), ".box 2.5 1.8 0.5")


def sandbar():
    m = M()
    n = 10
    ring = lambda r, y: [(r * 1.25 * cos(2 * pi * i / n), y, r * sin(2 * pi * i / n)) for i in range(n)]
    a, b, c = ring(.92, .012), ring(.72, .055), ring(.55, .085)
    for i in range(n):
        j = (i + 1) % n
        m.poly([a[i], a[j], b[j], b[i]], [C(0xBFF5E4), C(0xBFF5E4), C(0xF1DFA8), C(0xF1DFA8)], (0, -9, 0))
        m.poly([b[i], b[j], c[j], c[i]], C(0xF1DFA8), (0, -9, 0))
    m.poly(c, C(0xE9D49A), (0, 0, 0))
    m.at(-.05, .085, -.12)
    m.box(0, 0, 0, .44, .22, .3, C(0x6A3F1C))
    for s in (-.18, .0, .18):
        m.box(s, 0, 0, .04, .225, .31, IRON)
    m.box(0, .19, 0, .46, .09, .32, C(0x4A2A12), top=C(0x5C3618))
    m.box(0, .13, .153, .07, .07, .012, GOLD)
    m.at(.28, .085, -.2)
    m.post(0, 0, 0, .02, .7, DARK, .012, n=4)
    m.at()
    write("sandbar", m, stand=".cylinder 0.8 0.1")
    f = M()
    f.sheet(lambda u, v: ((.29 + .3 * u, .6 + .14 * v, -.2 + .018 * sin(u * 7)), C(0x101014) if not (abs(u - .5) < .1 and abs(v - .5) < .22) else BONE), 6, 3)
    write("sandbar_flag", f, (0, .012, 0), BARE)


def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/pirate-republic/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.PirateRepublic.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\nend Charter.Games.PirateRepublic.Meshes\n")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    sloop(); boom(); wharf(); fort(); flagship(); privateer(); made()
    tiles(); bits(); square(); monuments()
    sea(); islet(); man_of_war(); sandbar()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
