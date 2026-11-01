#!/usr/bin/env python3
"""Makes Omertà's meshes: a 1950s city at night. Each tile is a city block with streets on its sides, a kerb
and a sidewalk, and a yard in the middle. Buildings, barrels and boats are built from flat faces, and the
player's flat shading gives them facets. Run it from anywhere. It writes meshes/<sha256>.mesh here and the
table of ids for Lean. It uses no packages. The same code always makes the same bytes.
Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, os, struct
from math import sin, cos, sqrt, pi

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/Omerta/Meshes.lean"


def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def G(v): return (v, v, v)
def mix(a, b, t):
    t = max(0., min(1., t))
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)
def sstep(a, b, x):
    t = max(0., min(1., (x - a) / (b - a)))
    return t * t * (3 - 2 * t)
def wave(x, z, f, s=0.):
    return (sin(f * x + 1.7 * sin(f * .63 * z + s)) * cos(f * z + 1.3 * sin(f * .71 * x + s)) + sin(f * .5 * (x + z) + 2.1 * s) * .5) / 1.5
def noise(i, s=0):
    """A number in [0, 1) fixed by i and s."""
    return (sin(i * 12.9898 + s * 78.233) * 43758.5453) % 1.


WHITE, SHADE, SHADE2 = (1., 1., 1.), G(.72), G(.84)
ASPH, ASPH2, LINE = C(0x2B2B31), C(0x34343B), C(0x9A8448)
KERB, KERB2, WALK, WALK2, BASE = C(0x9A9488), C(0x6E6A62), C(0x5E5A55), C(0x6C665E), C(0x1E1E22)
STUCCO, STUCCO2, ROOF, BRICK, BRICK2 = C(0xD2BE98), C(0xB59F78), C(0x34302E), C(0x8A3B2C), C(0x5A2A24)
CLUBWALL, CLUBWALL2 = C(0x3E2430), C(0x2C1A24)
LIT, LIT2, GLASS, DOOR, DOOR2 = C(0xFFD27A), C(0xFFB54A), C(0x1A2230), C(0x3A2418), C(0x8E1C24)
WOOD, WOOD2, DARK, IRON, CHROME = C(0x7A5230), C(0xA8784A), C(0x2A1C12), C(0x24262B), C(0xC8CCD2)
CREAM, RED, GOLD, GOLD2, MARBLE = C(0xF0E6CC), C(0xB8232F), C(0xE5B43C), C(0xFFDA7A), C(0xE6E0D2)
STONE, STONE2 = C(0x9A8E7C), C(0x7A6F60)
BILL, BILL2, BAND = C(0x4F9A48), C(0x86CC70), C(0xF2E6C4)
LAMP = C(0xFFE6A8)


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
        """A box standing on y, with no bottom. `top` colours its top face."""
        c, s = cos(rot), sin(rot)
        pt = lambda a, b, e: (x + a * c + e * s, y + b, z + e * c - a * s)
        hw, hd = w / 2, d / 2
        ref = (x, y + h / 2, z)
        for a in (-hw, hw):
            self.poly([pt(a, 0, -hd), pt(a, 0, hd), pt(a, h, hd), pt(a, h, -hd)], col, ref)
        for e in (-hd, hd):
            self.poly([pt(-hw, 0, e), pt(hw, 0, e), pt(hw, h, e), pt(-hw, h, e)], col, ref)
        self.poly([pt(-hw, h, -hd), pt(hw, h, -hd), pt(hw, h, hd), pt(-hw, h, hd)], top or col, ref)

    def flat(self, x, y, z, w, d, col, rot=0):
        """A flat rectangle facing up."""
        c, s = cos(rot), sin(rot)
        pt = lambda a, e: (x + a * c + e * s, y, z + e * c - a * s)
        self.poly([pt(-w / 2, -d / 2), pt(w / 2, -d / 2), pt(w / 2, d / 2), pt(-w / 2, d / 2)], col, (x, y - 1, z))

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
            if rb > 0: self.poly([ring(b, rb, i) for i in range(n)], col, ref)
            if ra > 0: self.poly([ring(a, ra, i) for i in range(n)], col, ref)

    def post(self, x, y, z, r, h, col, r2=None, n=5):
        self.rod((x, y, z), (x, y + h, z), r, r if r2 is None else r2, col, n)

    def ball(self, x, y, z, r, col, sy=1., n=6, m=3):
        pt = lambda i, j: (x + r * cos(2 * pi * i / n) * sin(pi * j / m), y + r * sy * cos(pi * j / m), z + r * sin(2 * pi * i / n) * sin(pi * j / m))
        for i in range(n):
            for j in range(m):
                q = [pt(i, j), pt(i + 1, j), pt(i + 1, j + 1), pt(i, j + 1)]
                if j == 0: q = [q[0], q[2], q[3]]
                elif j == m - 1: q = q[:3]
                self.poly(q, col, (x, y, z))

    def barrel(self, x, y, z, r, h, col=WOOD, band=IRON, lying=False, rot=0, n=6):
        c, s = cos(rot), sin(rot)
        def pt(a, b, e):
            if lying: a, b, e = b - h / 2, a + r, e
            return (x + a * c + e * s, y + b, z + e * c - a * s)
        prof = [(0, .8, band), (.15, .97, col), (.5, 1.05, col), (.85, .97, band), (1, .8, band)]
        ref = pt(0, h / 2, 0)
        for (t0, w0, c0), (t1, w1, c1) in zip(prof, prof[1:]):
            for i in range(n):
                a, b = 2 * pi * i / n, 2 * pi * (i + 1) / n
                self.poly([pt(r * w0 * cos(a), t0 * h, r * w0 * sin(a)), pt(r * w0 * cos(b), t0 * h, r * w0 * sin(b)),
                           pt(r * w1 * cos(b), t1 * h, r * w1 * sin(b)), pt(r * w1 * cos(a), t1 * h, r * w1 * sin(a))], c0, ref)
        self.poly([pt(r * .8 * cos(2 * pi * i / n), h, r * .8 * sin(2 * pi * i / n)) for i in range(n)], WOOD2, ref)
        if lying:
            self.poly([pt(r * .8 * cos(2 * pi * i / n), 0, r * .8 * sin(2 * pi * i / n)) for i in range(n)], WOOD2, ref)

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

    def face(self, k, hw, u, y, w, h, col, out=.003):
        """A rectangle on side k of a box (0 is +z, then turning a quarter each), `hw` out from the middle.
        `u` is its middle along the side, `y` its foot."""
        r = k * pi / 2
        c, s = cos(r), sin(r)
        pt = lambda a, b: (a * c + (hw + out) * s, b, (hw + out) * c - a * s)
        self.poly([pt(u - w / 2, y), pt(u + w / 2, y), pt(u + w / 2, y + h), pt(u - w / 2, y + h)], col, (0, y + h / 2, 0))


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


# ---- pieces. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour.

def street():
    """A cobbled strip along a block's side. The cobbles take the seat's colour, and kerb stones line it."""
    t = M()
    L, W, n = .62, .13, 8
    for i in range(n):
        for j in range(2):
            x0, z0 = -L / 2 + L * i / n, -W / 2 + W * j / 2
            col = WHITE if (i + j) % 2 == 0 else SHADE2
            t.poly([(x0 + .004, .014, z0 + .004), (x0 + L / n - .004, .014, z0 + .004), (x0 + L / n - .004, .014, z0 + W / 2 - .004), (x0 + .004, .014, z0 + W / 2 - .004)], col, (0, -9, 0))
    write("street_tint", t, stand=".box 0.62 0.014 0.13")
    b = M()
    b.box(0, 0, 0, L, .012, W, C(0x3A3632))
    for s in (-1, 1):
        b.box(0, 0, s * (W / 2 + .01), L + .02, .022, .02, KERB, top=C(0xB8B2A4))
    write("street_body", b, stand=BARE)


def sedan(name, body=WHITE, roof=None):
    """A rounded 1950s sedan, nose along +x. The body takes the draw's colour."""
    m = M()
    L, W = .2, .085
    roof = roof or body
    # The lower body, with a waist that narrows at the ends.
    m.box(0, .016, 0, L, .032, W, body)
    m.box(.075, .016, 0, .05, .036, W * .92, body)  # hood
    m.box(-.078, .016, 0, .044, .034, W * .92, body)  # trunk
    # The cabin, as a sloped prism.
    pts = [(-.05, .048, -W * .42), (.04, .048, -W * .42), (.02, .078, -W * .36), (-.035, .078, -W * .36)]
    for s in (-1, 1):
        m.poly([(p[0], p[1], p[2] * s) for p in pts], GLASS, (0, .06, 0))
    m.poly([(.04, .048, -W * .42), (.04, .048, W * .42), (.02, .078, W * .36), (.02, .078, -W * .36)], GLASS, (0, .06, 0))
    m.poly([(-.05, .048, -W * .42), (-.05, .048, W * .42), (-.035, .078, W * .36), (-.035, .078, -W * .36)], GLASS, (0, .06, 0))
    m.poly([(-.035, .078, -W * .36), (.02, .078, -W * .36), (.02, .078, W * .36), (-.035, .078, W * .36)], roof, (0, 0, 0))
    for x in (-.06, .06):
        for s in (-1, 1):
            m.face(0 if s > 0 else 2, W / 2 + .001, x * s, .0, .036, .03, IRON, out=0)
    m.box(L / 2 + .002, .022, 0, .006, .012, W * .9, CHROME)
    m.box(-L / 2 - .002, .022, 0, .006, .012, W * .9, CHROME)
    for s in (-1, 1):
        m.face(1, L / 2 + .004, s * .03, .03, .016, .012, LAMP)
        m.face(3, L / 2 + .004, s * .03, .03, .014, .01, RED)
    write(name, m, stand=".box 0.2 0.07 0.085")


def front():
    """A corner shop with a lit window and a striped awning on each side, and a water tank on the roof."""
    b = M()
    W, H = .17, .2
    hw = W / 2
    b.box(0, 0, 0, W, H, W, STUCCO, top=ROOF)
    for k in range(4):
        b.face(k, hw, -.022, .022, .075, .06, LIT)
        b.face(k, hw, .052, 0, .03, .085, DOOR)
        for i, u in enumerate((-.04, .03)):
            b.face(k, hw, u, .142, .035, .036, LIT2 if (i + k) % 3 == 0 else GLASS)
    b.box(-.035, H, -.035, .03, .03, .03, ROOF)
    b.post(-.035, H + .03, -.035, .022, .035, WOOD, n=6)
    b.rod((-.035, H + .065, -.035), (-.035, H + .085, -.035), .024, .0, DARK, n=6)
    write("front_body", b, stand=".box 0.17 0.2 0.17")
    t = M()
    stripes = 6
    for k in range(4):
        t.at(0, 0, 0, k * pi / 2)
        for i in range(stripes):
            x0, x1 = -.078 + .156 * i / stripes, -.078 + .156 * (i + 1) / stripes
            col = WHITE if i % 2 == 0 else SHADE
            t.poly([(x0, .1, hw), (x1, .1, hw), (x1, .078, hw + .05), (x0, .078, hw + .05)], col, (0, -1, hw))
            t.poly([(x0, .078, hw + .05), (x1, .078, hw + .05), (x1, .063, hw + .05), (x0, .063, hw + .05)], col, (0, .07, 0))
        t.face(0, hw, 0, .102, .15, .026, WHITE)
        t.box(0, H, hw - .006, W + .002, .022, .012, WHITE, top=SHADE2)
    t.at()
    write("front_tint", t, stand=BARE)


def club():
    """A nightclub: dark brick, rows of lit windows, a marquee round the ground floor and a neon tower."""
    b = M()
    W, D, H = .28, .22, .25
    b.box(0, 0, 0, W, H, D, CLUBWALL, top=ROOF)
    for k in range(4):
        side, out = (W, D) if k % 2 == 0 else (D, W)
        b.face(k, out / 2, 0, 0, .05, .085, DOOR2)
        for u in (-side * .3, side * .3):
            b.face(k, out / 2, u, .02, side * .22, .05, C(0xFF9A5A))
        cols = 4 if k % 2 == 0 else 3
        for row, y in enumerate((.135, .19)):
            for i in range(cols):
                u = -side / 2 + side * (i + .5) / cols
                b.face(k, out / 2, u, y, .03, .035, LIT if (i + row + k) % 3 else GLASS)
        # Bulbs along the marquee's edge.
        for i in range(7):
            u = -side * .38 + side * .76 * i / 6
            b.face(k, out / 2 + .062, u, .1, .008, .008, LAMP, out=.002)
    b.box(-.08, H, -.05, .05, .02, .05, ROOF)
    b.post(-.08, H + .02, -.05, .03, .04, WOOD, n=6)
    b.rod((-.08, H + .06, -.05), (-.08, H + .085, -.05), .032, 0, DARK, n=6)
    b.box(.1, H, .07, .055, .01, .055, IRON)
    write("club_body", b, stand=".box 0.28 0.25 0.22")
    t = M()
    for k in range(4):
        side, out = (W, D) if k % 2 == 0 else (D, W)
        t.at(0, 0, 0, k * pi / 2)
        t.box(0, .09, out / 2 + .03, side * .86, .024, .06, WHITE, top=SHADE)
        t.box(0, H, out / 2 - .006, side + .002, .02, .012, WHITE, top=SHADE2)
    t.at()
    write("club_tint", t, stand=BARE)
    g = M()
    x, z, s = .1, .07, .046
    for i in range(4):
        y0 = H + .01 + i * .028
        g.box(x, y0, z, s, .024, s, WHITE if i % 2 == 0 else SHADE)
    g.ball(x, H + .135, z, .022, WHITE, n=5, m=3)
    write("club_neon", g, (0, 0, .55), BARE)


def racket():
    """A back room: a card table under a hanging lamp, chairs, chips and a slot machine, on a rug."""
    b = M()
    b.post(0, 0, 0, .014, .05, DARK, n=5)
    b.post(0, .046, 0, .07, .01, WOOD, n=8)
    for i in range(3):
        a = 2 * pi * i / 3 + .4
        x, z = .095 * cos(a), .095 * sin(a)
        b.box(x, 0, z, .032, .03, .032, WOOD2, rot=-a)
        b.box(x + .018 * cos(a), .03, z + .018 * sin(a), .006, .04, .032, WOOD2, rot=-a)
    for i, (dx, dz, col) in enumerate(((.025, .01, RED), (-.02, .025, CREAM), (-.01, -.03, C(0x2A55B0)))):
        b.post(dx, .059, dz, .009, .012 + .006 * i, col, n=5)
    for i in range(3):
        b.flat(.02 * i - .02, .0595, -.005, .016, .022, CREAM, rot=.4 * i)
    b.box(-.085, 0, -.08, .05, .1, .045, RED, top=CHROME)
    b.at(-.085, 0, -.08)
    b.face(0, .0225, 0, .05, .034, .028, LIT)
    b.face(1, .025, 0, .05, .03, .028, LIT)
    b.at()
    b.rod((-.058, .07, -.08), (-.05, .11, -.08), .004, .004, CHROME, n=3)
    b.ball(-.05, .112, -.08, .008, RED, n=4, m=2)
    b.post(.1, 0, -.06, .006, .19, IRON, n=4)
    b.rod((.1, .19, -.06), (0, .19, 0), .004, .004, IRON, n=3)
    b.rod((0, .19, 0), (0, .16, 0), .002, .002, IRON, n=3, caps=False)
    b.ball(0, .14, 0, .012, LAMP, n=5, m=2)
    write("racket_body", b, stand=".cylinder 0.12 0.12")
    t = M()
    t.flat(0, .012, 0, .26, .23, SHADE)
    t.flat(0, .0135, 0, .21, .18, WHITE)
    t.post(0, .052, 0, .062, .007, WHITE, n=8)
    t.rod((0, .163, 0), (0, .135, 0), .012, .042, WHITE, n=7, caps=False)
    write("racket_tint", t, stand=BARE)


def made():
    """Pieces a law makes: a phone booth, a newsstand and a delivery truck. The seat's colour is the body."""
    a = M()
    a.box(0, 0, 0, .08, .2, .08, WHITE, top=SHADE)
    for k in range(4):
        a.face(k, .04, 0, .03, .056, .13, G(.2))
    a.box(0, .2, 0, .09, .02, .09, SHADE)
    a.ball(0, .225, 0, .016, LAMP, n=5, m=2)
    write("made_booth", a, stand=".box 0.08 0.22 0.08")
    b = M()
    b.box(0, 0, 0, .18, .11, .12, WHITE)
    for s in (-1, 1):
        b.poly([(-.1, .11, s * .07), (.1, .11, s * .07), (.1, .15, 0), (-.1, .15, 0)], SHADE, (0, .1, 0))
    for s in (-1, 1):
        b.poly([(s * .1, .11, -.07), (s * .1, .11, .07), (s * .1, .15, 0)], WHITE, (0, .1, 0))
    b.face(0, .06, 0, .05, .14, .045, G(.2))
    for i in range(3):
        b.box(-.05 + .05 * i, .0, .085, .04, .02 + .008 * i, .03, CREAM)
    write("made_kiosk", b, stand=".box 0.18 0.15 0.12")
    c = M()
    c.box(-.03, .02, 0, .16, .12, .1, WHITE, top=SHADE)
    c.box(.09, .02, 0, .07, .08, .095, SHADE)
    c.face(1, .125, 0, .03, .07, .03, G(.2))
    for x in (-.08, .07):
        for s in (-1, 1):
            c.face(0 if s > 0 else 2, .051, x * s, 0, .04, .035, IRON, out=0)
    write("made_truck", c, stand=".box 0.24 0.14 0.1")
    d = M()
    # A police barricade: a striped board on two trestles.
    for i in range(6):
        x0 = -.28 + .56 * i / 6
        col = WHITE if i % 2 == 0 else G(.18)
        d.box(x0 + .0467, .07, 0, .0934, .04, .015, col)
    for x in (-.22, .22):
        for s in (-1, 1):
            d.rod((x, 0, s * .04), (x, .1, 0), .008, .008, G(.2), n=3)
    write("barricade", d, stand=".box 0.56 0.11 0.08")


# ---- tiles: a hexagon of corner radius 1. Streets run along the sides, then a kerb, a sidewalk and the yard.
# y = 0.16 is where pieces stand.

APO = sqrt(3) / 2
TOP = .16


def hexd(x, z):
    ax, az = abs(x), abs(z)
    return max(ax, ax * .5 + az * APO)


def corner(i, a):
    """Corner i of the hexagon whose sides are `a` from the middle."""
    R = a / APO
    t = pi / 2 - i * pi / 3
    return (R * cos(t), R * sin(t))


def ring(m, a0, a1, y, c0, c1):
    for i in range(6):
        p0, p1, q0, q1 = corner(i, a0), corner(i + 1, a0), corner(i, a1), corner(i + 1, a1)
        m.poly([(p0[0], y, p0[1]), (q0[0], y, q0[1]), (q1[0], y, q1[1]), (p1[0], y, p1[1])], [c0, c1, c1, c0], (0, -9, 0))


def wall(m, a, y0, y1, c0, c1, outward=True):
    for i in range(6):
        p0, p1 = corner(i, a), corner(i + 1, a)
        mx, mz = (p0[0] + p1[0]) / 2, (p0[1] + p1[1]) / 2
        ref = (0, (y0 + y1) / 2, 0) if outward else (mx * 3, (y0 + y1) / 2, mz * 3)
        m.poly([(p0[0], y0, p0[1]), (p1[0], y0, p1[1]), (p1[0], y1, p1[1]), (p0[0], y1, p0[1])], [c0, c0, c1, c1], ref)


def lattice(n):
    ids, pts = {}, []
    for q in range(-n, n + 1):
        for s in range(-n, n + 1):
            if abs(q + s) > n: continue
            ids[(q, s)] = len(pts)
            pts.append((APO * q / n, (.5 * q + s) / n))
    return ids, pts


YARD = .62


def block(m, hgt, col, n=10):
    """Streets, kerb and sidewalk round the edge, and the yard inside: hgt(x, z) is the yard's height over
    TOP, col(x, z) its colour. The yard's edge and the middle, where the number token sits, stay at TOP."""
    ids, pts = lattice(n)
    k = YARD / APO
    vert = []
    for (x0, z0) in pts:
        x, z = x0 * k, z0 * k
        y = TOP if hexd(x0, z0) > APO - 1e-6 else TOP + hgt(x, z)
        if sqrt(x * x + z * z) < .27: y = min(y, TOP)
        vert.append(((x, y, z), col(x, z)))
    for (q, s), i in ids.items():
        for a, b in (((q + 1, s), (q, s + 1)), ((q + 1, s), (q + 1, s - 1))):
            if a in ids and b in ids:
                A, B, D = vert[i], vert[ids[a]], vert[ids[b]]
                m.poly([A[0], B[0], D[0]], [A[1], B[1], D[1]], (A[0][0], -9, A[0][2]))
    ring(m, YARD, .70, TOP, WALK, WALK2)
    wall(m, .70, TOP, .17, KERB2, KERB2, outward=False)
    ring(m, .70, .735, .17, KERB, KERB)
    wall(m, .735, .148, .17, KERB2, KERB2)
    ring(m, .735, .80, .148, ASPH, ASPH)
    ring(m, .80, APO, .148, ASPH, ASPH2)
    wall(m, APO, 0, .148, BASE, ASPH)
    # Half of a dashed centre line on each side. The tile next door draws the other half.
    for i in range(6):
        p0, p1 = corner(i, APO), corner(i + 1, APO)
        q0, q1 = corner(i, APO - .012), corner(i + 1, APO - .012)
        for t0 in (.22, .44, .66):
            t1 = t0 + .12
            L = lambda p, q, t: (p[0] + (q[0] - p[0]) * t, .1495, p[1] + (q[1] - p[1]) * t)
            m.poly([L(p0, p1, t0), L(p0, p1, t1), L(q0, q1, t1), L(q0, q1, t0)], LINE, (0, -9, 0))


def along(x, z): return (x + z) * .7071
def across(x, z): return (x - z) * .7071
def spot(a, c):
    """The point `a` toward the viewer and `c` to the right."""
    return ((a + c) * .7071, (a - c) * .7071)


def lamp_post(m, x, z, h=.25):
    m.post(x, TOP, z, .008, h, IRON, .006, n=4)
    m.box(x, TOP + h, z, .02, .012, .02, IRON)


def tile(name, hgt, col, props, n=10):
    m = M()
    block(m, hgt, col, n)
    props(m)
    write(name, m, stand=".hexPrism 0.96 0.16")


def tile_wine():
    def col(x, z):
        c = mix(C(0x4A3424), C(0x5A3E2A), sstep(-.4, .5, wave(x, z, 13., 1.)))
        a, cc = along(x, z), across(x, z)
        if a < -.2 and -.42 < cc < .3: c = mix(C(0x8E806C), C(0x7A6E5E), sstep(-.5, .5, wave(x, z, 30., 2.)))
        return c

    def props(m):
        # Rows of vines, cut round the token and the cellar.
        for r in range(-5, 6):
            a = r * .1
            seg = []
            for i in range(14):
                c0 = -.62 + i * .09
                c1 = c0 + .09
                ok = True
                for cc in (c0, c1):
                    x, z = spot(a, cc)
                    if hexd(x, z) > .57 or sqrt(x * x + z * z) < .3 or (a < -.15 and -.46 < cc < .34): ok = False
                if ok: seg.append((c0, c1))
            # Join neighbours, then draw each run as one hedge, its top spotted with grapes.
            runs = []
            for s in seg:
                if runs and abs(runs[-1][1] - s[0]) < 1e-6: runs[-1] = (runs[-1][0], s[1])
                else: runs.append(s)
            for c0, c1 in runs:
                x, z = spot(a, (c0 + c1) / 2)
                m.box(x, TOP, z, c1 - c0, .045, .032, C(0x2F5A2A), rot=pi / 4, top=C(0x5A2A50) if r % 2 else C(0x4E7A32))
        # The cellar: stone walls, a tiled roof, an arched door and a lit window.
        x, z = spot(-.43, -.08)
        m.at(x, TOP, z, pi / 4)
        m.box(0, 0, 0, .3, .15, .19, C(0x9A8A72), top=C(0x9A8A72))
        for s in (-1, 1):
            m.poly([(-.165, .15, s * .11), (.165, .15, s * .11), (.165, .22, 0), (-.165, .22, 0)], C(0xA04A2E), (0, .1, 0))
        for s in (-1, 1):
            m.poly([(s * .15, .15, -.095), (s * .15, .15, .095), (s * .15, .22, 0)], C(0x8A7A62), (0, .1, 0))
        m.face(0, .095, -.03, 0, .06, .1, DOOR)
        m.face(0, .095, .085, .06, .045, .04, LIT)
        m.face(1, .15, 0, .06, .04, .035, LIT2)
        # Barrels before the door, two lying with one on top, and one standing.
        for dx, dy in ((-.075, 0), (-.005, 0), (-.04, .052)):
            m.barrel(dx, dy, .15, .026, .085, col=C(0x6E4426), lying=True, rot=pi / 2)
        m.barrel(.06, 0, .14, .03, .07, col=C(0x7A4A2A))
        m.at()
        # Crates of bottles by the street.
        x, z = spot(-.1, .48)
        for i in range(2):
            m.box(x + .05 * i, TOP, z - .02 * i, .06, .035, .045, WOOD2, rot=pi / 4 + .2 * i, top=C(0x1E3A22))
    tile("tile_wine", lambda x, z: .004 * wave(x, z, 9.), col, props)


def tile_cement():
    def col(x, z):
        c = mix(C(0x8E8A82), C(0x7A766E), sstep(-.3, .6, wave(x, z, 11., 3.)))
        tr = abs(sin(9 * across(x, z) + .5)) < .12 and along(x, z) > -.1
        return mix(c, C(0x5E5A54), .55) if tr else c

    def props(m):
        # A tower crane at the back, its jib across the yard.
        x, z = spot(-.42, .18)
        Y = C(0xE8B020)
        h = .4
        for dx, dz in ((-.018, -.018), (.018, -.018), (.018, .018), (-.018, .018)):
            m.rod((x + dx, TOP, z + dz), (x + dx, TOP + h, z + dz), .004, .004, Y, n=3, caps=False)
        for i in range(5):
            y = TOP + .03 + i * .08
            m.rod((x - .018, y, z - .018), (x + .018, y + .07, z + .018), .003, .003, Y, n=3, caps=False)
        m.box(x, TOP, z, .07, .015, .07, G(.35))
        jx, jz = spot(-.42 + .0, .18 - .42)
        bx, bz = spot(-.42, .18 + .14)
        m.rod((bx, TOP + h, bz), (jx, TOP + h, jz), .008, .006, Y, n=4)
        m.box(bx, TOP + h - .03, bz, .05, .035, .05, G(.3), rot=pi / 4)
        m.box(x, TOP + h, z, .04, .04, .04, Y, rot=pi / 4, top=C(0xC8901A))
        hx, hz = spot(-.42, .18 - .3)
        m.rod((hx, TOP + h, hz), (hx, TOP + .2, hz), .0015, .0015, IRON, n=3, caps=False)
        m.box(hx, TOP + .17, hz, .09, .012, .016, C(0xA0461E), rot=pi / 4)
        # A cement mixer: an orange drum on a frame with two wheels.
        x, z = spot(-.4, -.27)
        m.at(x, TOP, z, pi / 4 + .6)
        m.box(0, .025, 0, .1, .012, .05, IRON)
        for s in (-1, 1):
            m.rod((-.02, .02, s * .03), (-.02, .02, s * .036), .02, .02, G(.15), n=6)
        m.rod((-.05, .06, 0), (.03, .085, 0), .045, .045, C(0xD8692A), n=7)
        m.rod((.03, .085, 0), (.07, .095, 0), .045, .018, C(0xD8692A), n=7)
        m.rod((-.05, .06, 0), (-.07, .055, 0), .045, .02, C(0xB04E1C), n=7)
        m.at()
        # A pallet of cement bags.
        x, z = spot(-.12, .43)
        m.at(x, TOP, z, pi / 4)
        m.box(0, 0, 0, .17, .02, .12, WOOD)
        for lvl, (nx, nz) in enumerate(((3, 2), (2, 2), (2, 1))):
            for i in range(nx):
                for j in range(nz):
                    m.box((i - (nx - 1) / 2) * .052, .02 + lvl * .028, -.028 * (nz - 1) + .056 * j, .048, .028, .05, C(0xD9CFB4), top=C(0xE6DCC4))
        m.at()
        # Rebar in a bundle, and a heap of sand.
        x, z = spot(-.22, -.52)
        for i in range(5):
            m.rod((x - .12 + .006 * i, TOP + .006 + .006 * (i % 2), z + .1), (x + .12 + .006 * i, TOP + .006 + .006 * (i % 2), z - .1), .004, .004, C(0x8A3E22), n=3)
        x, z = spot(.2, -.5)
        m.ball(x, TOP, z, .085, C(0xC9A86A), sy=.45, n=7, m=3)
    tile("tile_cement", lambda x, z: .003 * wave(x, z, 13.), col, props)


def tile_fish():
    WATER_EDGE = -.08

    def hgt(x, z):
        return -.03 if along(x, z) < WATER_EDGE - .04 else 0

    def col(x, z):
        if along(x, z) < WATER_EDGE - .02:
            c = mix(C(0x173E4E), C(0x0F2C3A), sstep(-.4, .5, wave(x, z, 14., 2.)))
            return mix(c, C(0x3A6A70), .5 * sstep(.4, .8, wave(x, z, 22., 5.)))
        return mix(C(0x6A4E36), C(0x7E5E40), .5 + .5 * sin(60 * across(x, z)))

    def props(m):
        # The quay's edge: a timber beam with bollards.
        for i in range(9):
            c0, c1 = -.62 + i * .14, -.62 + (i + 1) * .14
            x0, z0 = spot(WATER_EDGE - .02, c0)
            x1, z1 = spot(WATER_EDGE - .02, c1)
            if hexd(x0, z0) < .6 and hexd(x1, z1) < .6:
                m.box((x0 + x1) / 2, TOP - .01, (z0 + z1) / 2, .14, .022, .025, C(0x4A3422), rot=-pi / 4)
        for c in (-.3, .05, .35):
            x, z = spot(WATER_EDGE, c)
            if hexd(x, z) < .58: m.post(x, TOP, z, .012, .03, IRON, n=5)
        # A small fishing boat in the basin.
        x, z = spot(-.34, -.3)
        m.at(x, TOP - .04, z, -pi / 4 - .5)
        n, L, B = 6, .2, .055
        secs = []
        for i in range(n + 1):
            t = -1 + 2 * i / n
            w = B * (1 - t * t) if t > 0 else B * (1 - .4 * t * t)
            secs.append((t * L, max(w, .003), .04 + .015 * t * t))
        for (x0, w0, h0), (x1, w1, h1) in zip(secs, secs[1:]):
            for s in (-1, 1):
                m.poly([(x0, h0, s * w0), (x1, h1, s * w1), (x1, .0, s * w1 * .6), (x0, .0, s * w0 * .6)], [CREAM, CREAM, C(0x2A55B0), C(0x2A55B0)], (0, .02, 0))
            m.poly([(x0, h0 - .006, -w0 * .9), (x1, h1 - .006, -w1 * .9), (x1, h1 - .006, w1 * .9), (x0, h0 - .006, w0 * .9)], WOOD2, (0, -1, 0))
        m.box(-.06, .034, 0, .07, .05, .06, CREAM, top=RED)
        m.box(-.024, .052, 0, .003, .014, .04, LIT)
        m.post(.04, .034, 0, .004, .14, DARK, n=3)
        m.rod((.04, .15, 0), (.17, .05, 0), .0015, .0015, DARK, n=3, caps=False)
        m.at()
        # Crates of fish on ice along the quay.
        for a, c in ((.12, -.46), (.04, -.36), (.3, -.34), (.2, .5)):
            x, z = spot(a, c)
            if hexd(x, z) < .56:
                m.box(x, TOP, z, .06, .03, .045, C(0x8A6A44), rot=pi / 4 + c, top=C(0xD8ECF2))
                for k in range(2):
                    m.box(x + .01 * (k - .5), TOP + .031, z - .01 * (k - .5), .035, .006, .01, C(0x9FB2BC), rot=pi / 4 + c + .5 * k)
        # A market stall: a striped awning on posts over a counter.
        x, z = spot(.02, .40)
        m.at(x, TOP, z, pi / 4)
        m.box(0, 0, 0, .16, .05, .06, C(0x5A3E28), top=C(0xD8ECF2))
        for dx in (-.075, .075):
            for dz in (-.035, .035):
                m.post(dx, 0, dz, .004, .12, DARK, n=3)
        for i in range(6):
            x0, x1 = -.085 + .17 * i / 6, -.085 + .17 * (i + 1) / 6
            m.poly([(x0, .135, -.045), (x1, .135, -.045), (x1, .11, .05), (x0, .11, .05)], RED if i % 2 == 0 else CREAM, (0, 0, -.2), two=True)
        m.at()
    tile("tile_fish", hgt, col, props)


def tile_piazza():
    def col(x, z):
        r = sqrt(x * x + z * z)
        c = mix(C(0xB8A88A), C(0x9C8C70), sstep(-.6, .6, sin(46 * r) * .5 + .5 * wave(x, z, 20., 4.)))
        if .44 < r < .48: c = C(0xD8CBB0)
        return c
    tile("tile_piazza", lambda x, z: 0, col, lambda m: None, n=12)


def bits():
    q = M()
    ring(q, YARD - .02, .72, .014, LAMP, C(0xFFC04A))
    write("hot_ring", q, (0, 0, .7), BARE)

    p = M()
    p.post(0, 0, 0, .009, .26, IRON, .006, n=4)
    p.rod((0, .25, 0), (.035, .27, 0), .004, .004, IRON, n=3)
    p.box(0, .0, 0, .022, .02, .022, IRON)
    write("lamp_post", p, stand=".cylinder 0.01 0.26")
    g = M()
    g.post(.035, .222, 0, .006, .034, WHITE, .017, n=5)
    write("lamp_glow", g, (0, 0, .45), BARE)

    d = M()
    for i in range(2):
        d.box(.032 * i, .03 * 0, .025 * i, .05, .022, .04, C(0xD9CFB4), rot=.4 * i, top=C(0xE6DCC4))
    d.box(.015, .022, .012, .05, .022, .04, C(0xD0C6AA), rot=.2, top=C(0xE6DCC4))
    write("deco_bags", d, stand=".box 0.07 0.045 0.06")
    f = M()
    f.box(0, 0, 0, .06, .03, .045, C(0x8A6A44), top=C(0xD8ECF2))
    f.box(.02, .03, -.005, .055, .028, .042, C(0x7A5A3A), rot=.3, top=C(0xD8ECF2))
    f.box(.02, .059, -.005, .03, .005, .01, C(0x9FB2BC), rot=.7)
    write("deco_crates", f, stand=".box 0.06 0.06 0.045")

    # The pile in the treasury is made of these.
    c = M()
    c.box(0, 0, 0, .062, .03, .12, BILL, top=BILL2)
    c.box(0, -.001, 0, .064, .032, .024, BAND)
    write("cash_bundle", c, stand=".box 0.062 0.03 0.12")


# ---- the piazza, and what a law raises

def square():
    m = M()
    n = 8
    out = [(.2 * cos(2 * pi * i / n + pi / 8), .2 * sin(2 * pi * i / n + pi / 8)) for i in range(n)]
    inn = [(.17 * x / .2, .17 * z / .2) for x, z in out]
    for i in range(n):
        j = (i + 1) % n
        m.poly([(out[i][0], 0, out[i][1]), (out[j][0], 0, out[j][1]), (out[j][0], .05, out[j][1]), (out[i][0], .05, out[i][1])], STONE2, (0, .02, 0))
        m.poly([(out[i][0], .05, out[i][1]), (out[j][0], .05, out[j][1]), (inn[j][0], .05, inn[j][1]), (inn[i][0], .05, inn[i][1])], MARBLE, (0, -9, 0))
    m.poly([(x, .035, z) for x, z in inn], C(0x2A5E78), (0, -9, 0))
    m.post(0, .03, 0, .05, .05, MARBLE, .035, n=8)
    m.post(0, .08, 0, .06, .012, STONE, n=8)
    m.post(0, .09, 0, .02, .07, MARBLE, n=6)
    # A statue: a robed figure with a raised hand.
    m.rod((0, .16, 0), (0, .25, 0), .022, .014, C(0x6E7E70), n=6)
    m.ball(0, .262, 0, .013, C(0x6E7E70), n=5, m=3)
    m.rod((0, .235, .01), (.03, .285, .02), .005, .004, C(0x6E7E70), n=3)
    write("square_fountain", m, stand=".cylinder 0.2 0.28")
    w = M()
    for i in range(6):
        a = 2 * pi * i / 6
        w.rod((.05 * cos(a), .1, .05 * sin(a)), (.12 * cos(a), .04, .12 * sin(a)), .004, .002, C(0xB8E0F0), n=3)
    write("square_water", w, (.08, 0, .3), BARE)


def plinth(m, w=.13):
    m.box(0, 0, 0, w, .022, w, STONE2, top=MARBLE)
    m.box(0, .022, 0, w * .82, .014, w * .82, MARBLE)
    return .036


def monuments():
    # A cost: a cash register.
    m = M()
    y = plinth(m)
    m.box(0, y, 0, .1, .04, .08, C(0x7A6A52), top=C(0x5A4E3E))
    m.poly([(-.05, y + .04, .04), (.05, y + .04, .04), (.05, y + .07, -.01), (-.05, y + .07, -.01)], C(0xC9B27A), (0, 0, -.3))
    for i in range(3):
        for j in range(2):
            m.box(-.03 + .03 * i, y + .045 + .012 * j, .02 - .02 * j, .018, .008, .012, CREAM)
    m.box(0, y + .07, -.025, .1, .045, .03, C(0xC9B27A), top=GOLD)
    m.box(0, y + .085, -.0085, .05, .02, .002, C(0x1E1E22))
    write("mon_cost", m, stand=".box 0.1 0.15 0.08")
    # Points: a gold trophy.
    m = M()
    y = plinth(m)
    m.post(0, y, 0, .035, .02, C(0x2A2A2E), .03, n=6)
    m.post(0, y + .02, 0, .008, .05, GOLD, n=5)
    m.rod((0, y + .07, 0), (0, y + .13, 0), .012, .045, GOLD2, n=8)
    for s in (-1, 1):
        m.rod((s * .03, y + .12, 0), (s * .055, y + .1, 0), .005, .005, GOLD, n=3)
        m.rod((s * .055, y + .1, 0), (s * .03, y + .08, 0), .005, .005, GOLD, n=3)
    write("mon_points", m, stand=".cone 0.06 0.17")
    # The bank: an iron safe with a gold dial.
    m = M()
    y = plinth(m)
    m.box(0, y, 0, .1, .11, .09, C(0x2C3034), top=C(0x3A3E44))
    m.face(0, .045, 0, y + .01, .08, .09, C(0x40464C))
    m.at(0, y + .065, .048)
    m.rod((0, 0, 0), (0, 0, .01), .016, .016, GOLD, n=7)
    m.rod((.025, -.02, 0), (.025, -.02, .012), .005, .005, GOLD, n=4)
    m.at()
    write("mon_bank", m, stand=".box 0.1 0.15 0.09")
    # A harvest: a pushcart of wine, fish and a bag of cement.
    m = M()
    y = plinth(m)
    m.box(0, y + .03, 0, .12, .035, .08, WOOD, top=WOOD2)
    for s in (-1, 1):
        m.rod((-.03, y + .025, s * .045), (-.03, y + .025, s * .052), .025, .025, DARK, n=6)
    m.rod((.06, y + .06, 0), (.09, y + .09, 0), .004, .004, DARK, n=3)
    m.barrel(-.03, y + .065, 0, .018, .04, col=C(0x6E4426))
    m.box(.025, y + .065, .015, .04, .02, .03, C(0x8A6A44), top=C(0xD8ECF2))
    m.box(.025, y + .065, -.02, .04, .022, .03, C(0xD9CFB4))
    write("mon_harvest", m, stand=".box 0.12 0.12 0.08")
    # A build: a steel girder on end, with a hard hat on it.
    m = M()
    y = plinth(m)
    m.box(0, y, 0, .06, .16, .012, C(0xA0461E))
    for s in (-1, 1):
        m.box(0, y, s * .025, .06, .16, .008, C(0xB8562A))
    m.rod((0, y + .16, 0), (0, y + .185, 0), .035, .03, C(0xE8B020), n=7)
    m.post(0, y + .16, 0, .045, .005, C(0xE8B020), n=7)
    write("mon_build", m, stand=".box 0.06 0.2 0.06")
    # A round's end: a street clock on a post.
    m = M()
    y = plinth(m)
    m.post(0, y, 0, .012, .17, IRON, .009, n=5)
    m.at(0, y + .2, 0)
    m.rod((0, 0, -.012), (0, 0, .012), .04, .04, IRON, n=10)
    for s in (-1, 1):
        m.rod((0, 0, s * .0125), (0, 0, s * .0135), .034, .034, CREAM, n=10)
        m.poly([(-.002, 0, s * .014), (.002, 0, s * .014), (.002, .026, s * .014), (-.002, .026, s * .014)], IRON, (0, 0, 0), two=True)
        m.poly([(0, -.002, s * .014), (0, .002, s * .014), (.02, .002, s * .014), (.02, -.002, s * .014)], IRON, (0, 0, 0), two=True)
    m.at()
    write("mon_round", m, stand=".cylinder 0.04 0.25")
    # A roll: two dice on a felt pad.
    m = M()
    y = plinth(m)
    m.box(0, y, 0, .1, .008, .1, C(0x1E6A3A))
    m.box(-.018, y + .008, .012, .04, .04, .04, CREAM, rot=.3)
    m.box(.026, y + .008, -.016, .036, .036, .036, CREAM, rot=-.5)
    for dx, dz in ((-.008, -.008), (.008, .008), (0, 0)):
        m.flat(-.018 + dx, y + .0485, .012 + dz, .007, .007, RED, rot=.3)
    for dx, dz in ((-.008, -.008), (.008, .008)):
        m.flat(.026 + dx, y + .0445, -.016 + dz, .006, .006, DARK, rot=-.5)
    write("mon_roll", m, stand=".box 0.1 0.06 0.1")
    # A new piece: a scale model of a shop on a stand.
    m = M()
    y = plinth(m)
    m.post(0, y, 0, .01, .04, DARK, n=4)
    m.box(0, y + .04, 0, .08, .008, .08, WOOD)
    m.box(0, y + .048, 0, .06, .07, .06, STUCCO, top=ROOF)
    for k in range(4):
        m.at(0, y + .048, 0)
        m.face(k, .03, 0, .01, .03, .02, LIT)
        m.at(0, y + .048, 0, k * pi / 2)
        m.poly([(-.03, .045, .03), (.03, .045, .03), (.03, .035, .05), (-.03, .035, .05)], RED, (0, -1, .03))
    m.at()
    write("mon_piece", m, stand=".box 0.08 0.15 0.08")
    # A repeal: a broken column, its top fallen beside it.
    m = M()
    y = plinth(m)
    m.post(0, y, 0, .025, .1, MARBLE, .022, n=7)
    m.poly([(-.026, y + .1, -.02), (.026, y + .1, -.02), (.02, y + .12, .02), (-.02, y + .085, .02)], STONE, (0, 0, 0), two=True)
    m.rod((.03, y + .022, .04), (.1, y + .03, .02), .022, .022, MARBLE, n=7)
    m.box(-.045, y, .045, .025, .02, .02, STONE, rot=.4)
    write("mon_repeal", m, stand=".cylinder 0.04 0.14")


# ---- the city round the board. u runs to the viewer's right and v away from the viewer.

def world(u, v): return (.7071 * (u - v), -.7071 * (u + v))
def uv(x, z): return (.7071 * (x - z), -.7071 * (x + z))


QUAY = -5.45
LAMPS = [(-5.1, -3.2), (-5.1, 0.2), (-5.1, 3.6), (-2.7, -5.1), (0.4, -5.3), (3.2, -5.0), (5.3, 1.2), (5.3, 4.2),
         (-3.2, 5.3), (0.0, 5.6), (3.0, 5.4), (6.9, -4.6), (7.3, -0.6)]


def city_ground():
    m = M()
    R, n = 13., 34
    step = 2 * R / n
    def col(x, z):
        u, v = uv(x, z)
        if u < QUAY - .1:
            c = mix(C(0x0F2A38), C(0x081A24), sstep(-.3, .6, wave(x, z, .8, 2.)))
            return mix(c, C(0x2A4A50), .35 * sstep(.4, .9, wave(x, z, 2.2, 5.)))
        c = mix(C(0x15161A), C(0x1E1F24), sstep(-.5, .5, wave(x, z, .9, 1.)))
        for lu, lv in LAMPS:
            d = sqrt((u - lu) ** 2 + (v - lv) ** 2)
            c = mix(c, C(0x4A3C26), .85 * max(0, 1 - d / 1.5) ** 2)
        return c
    for i in range(n):
        for j in range(n):
            q = [(-R + i * step, -R + j * step), (-R + (i + 1) * step, -R + j * step), (-R + (i + 1) * step, -R + (j + 1) * step), (-R + i * step, -R + (j + 1) * step)]
            ps = [(a, .012 - (.006 if uv(a, b)[0] < QUAY - .1 else 0), b) for a, b in q]
            cs = [col(a, b) for a, b in q]
            m.poly(ps[:3], cs[:3], (0, -9, 0))
            m.poly([ps[0], ps[2], ps[3]], [cs[0], cs[2], cs[3]], (0, -9, 0))
    # A ring road round the city, with a dashed centre line.
    for i in range(48):
        a0, a1 = 2 * pi * i / 48, 2 * pi * (i + .5) / 48
        r0, r1 = 4.82, 4.89
        x0, z0, x1, z1 = cos(a0), sin(a0), cos(a1), sin(a1)
        if uv(4.85 * x0, 4.85 * z0)[0] < QUAY + .3: continue
        m.poly([(r0 * x0, .016, r0 * z0), (r1 * x0, .016, r1 * z0), (r1 * x1, .016, r1 * z1), (r0 * x1, .016, r0 * z1)], LINE, (0, -9, 0))
    write("city_ground", m, stand=".box 26 0.01 26")


def skyline():
    """Brick tenements and a hotel behind the city, with lit windows and water tanks on the roofs."""
    m = M()
    rows = [(-4.6, 6.7, 1.9, 1.1), (-2.6, 6.4, 1.7, 1.6), (-0.7, 6.8, 2.1, 2.4), (1.4, 6.3, 1.8, 1.3),
            (3.3, 6.6, 1.9, 1.9), (5.3, 6.3, 1.8, 1.2), (7.2, 6.7, 2.0, 1.7), (9.0, 6.3, 1.6, 1.1)]
    walls = [C(0x3A2422), C(0x2E2A30), C(0x332626), C(0x2A2C34)]
    for k, (u, v, w, h) in enumerate(rows):
        x, z = world(u, v)
        m.at(x, 0, z, pi / 4)
        d = 1.2
        m.box(0, 0, 0, w, h, d, walls[k % 4], top=C(0x1A1A1E))
        m.box(0, h, d / 2 - .03, w + .04, .05, .06, C(0x4A3A34))
        cols, rws = int(w / .3), int((h - .2) / .26)
        for i in range(cols):
            for j in range(rws):
                lit = noise(k * 97 + i * 13 + j, 1) < .42
                m.face(0, d / 2, -w / 2 + w * (i + .5) / cols, .2 + j * .26, .12, .14, (LIT if noise(i + j * 7, k) < .6 else LIT2) if lit else C(0x15181F))
        if k % 2 == 0:
            tx, tz = -w * .25, -d * .1
            for dx, dz in ((-.08, -.08), (.08, -.08), (.08, .08), (-.08, .08)):
                m.rod((tx + dx, h, tz + dz), (tx + dx, h + .18, tz + dz), .012, .012, IRON, n=3, caps=False)
            m.post(tx, h + .18, tz, .14, .2, C(0x5A3E28), n=7)
            m.rod((tx, h + .38, tz), (tx, h + .48, tz), .15, 0, C(0x3A2A1E), n=7)
    m.at()
    # The hotel's sign, standing out from the tallest front.
    x, z = world(-0.7 + 1.0, 6.8 - .62)
    m.at(x, 0, z, pi / 4)
    m.box(0, 1.1, 0, .24, .9, .06, C(0x2A1418))
    for i in range(5):
        m.face(0, .03, 0, 1.15 + i * .17, .16, .12, C(0xFF5A7A))
    m.at()
    write("skyline", m, stand=BARE)


def hull(m, L, B, deck, keel, col, trim, n=6):
    secs = []
    for i in range(n + 1):
        t = -1 + 2 * i / n
        w = B * (1 - t * t) if t > 0 else B * (1 - .4 * t * t)
        secs.append((t * L, max(w, .004), deck + .2 * deck * t * t))
    for (x0, w0, h0), (x1, w1, h1) in zip(secs, secs[1:]):
        for s in (-1, 1):
            m.poly([(x0, h0, s * w0), (x1, h1, s * w1), (x1, keel, s * w1 * .5), (x0, keel, s * w0 * .5)], [trim, trim, col, col], (0, (deck + keel) / 2, 0))
        m.poly([(x0, h0 - .01, -w0 * .9), (x1, h1 - .01, -w1 * .9), (x1, h1 - .01, w1 * .9), (x0, h0 - .01, w0 * .9)], WOOD2, (0, -9, 0))
    x0, w0, h0 = secs[0]
    m.poly([(x0, h0, -w0), (x0, h0, w0), (x0, keel, w0 * .5), (x0, keel, -w0 * .5)], trim, (0, (deck + keel) / 2, 0))


def harbour():
    """The quay on the left, with bollards and crates, a trawler, rowboats and old pilings."""
    m = M()
    for v in range(-9, 10):
        x, z = world(QUAY + .1, v + .5)
        m.box(x, 0, z, .4, .045, 1.0, C(0x5E5A52), rot=pi / 4, top=C(0x6E6A60))
    for v in range(-8, 9, 2):
        x, z = world(QUAY - .02, v)
        m.post(x, .045, z, .04, .06, IRON, n=5)
    for v, k in ((-4.6, 0), (2.2, 1), (5.4, 2)):
        x, z = world(QUAY + .25, v)
        m.box(x, .045, z, .18, .1, .14, C(0x6A4E34), rot=pi / 4 + .3 * k, top=C(0x7A5E40))
        m.box(x, .145, z, .12, .08, .1, C(0x7A5A3A), rot=pi / 4 + .3 * k + .4)
    # The trawler: a dark hull, a white wheelhouse with a lit window, and a mast with a boom.
    x, z = world(QUAY - .75, -1.4)
    m.at(x, 0, z, pi / 4 + pi / 2)
    hull(m, .9, .26, .2, -.02, C(0x1E2A36), C(0xB8232F), n=8)
    m.box(-.3, .19, 0, .3, .2, .28, CREAM, top=C(0x8A2228))
    m.box(-.148, .27, 0, .004, .06, .2, LIT)
    m.post(.2, .19, 0, .02, .7, DARK, .012, n=4)
    m.rod((.2, .55, 0), (.75, .25, 0), .01, .008, DARK, n=3)
    m.at()
    for v, rot in ((2.6, .3), (3.4, -.2)):
        x, z = world(QUAY - .55, v)
        m.at(x, 0, z, pi / 4 + pi / 2 + rot)
        hull(m, .3, .1, .07, -.01, C(0x5A3A24), CREAM, n=5)
        m.at()
    for i, v in enumerate((-7.0, -6.2, 6.5, 7.3, 0.9)):
        x, z = world(QUAY - .3 - .25 * (i % 2), v)
        m.post(x, -.05, z, .045, .14 + .05 * (i % 3), C(0x3A2A1E), n=5)
    write("harbour", m, stand=BARE)


def police():
    """A black-and-white patrol car. The light on its roof is a mesh of its own, so it can flash."""
    m = M()
    L, W = .2, .09
    m.box(0, .016, 0, L, .032, W, C(0x16161A))
    m.box(0, .02, 0, .08, .024, W + .002, CREAM)
    m.box(.075, .016, 0, .05, .036, W * .92, C(0x16161A))
    m.box(-.078, .016, 0, .044, .034, W * .92, C(0x16161A))
    m.box(-.008, .048, 0, .085, .028, W * .78, CREAM, top=CREAM)
    for x in (-.03, .015):
        for s in (-1, 1):
            m.face(0 if s > 0 else 2, W * .39, x * s, .052, .03, .02, GLASS)
    m.face(1, .035, 0, .052, W * .7, .02, GLASS)
    for x in (-.06, .06):
        for s in (-1, 1):
            m.face(0 if s > 0 else 2, W / 2 + .001, x * s, .0, .036, .03, IRON, out=0)
    for s in (-1, 1):
        m.face(1, L / 2 + .004, s * .03, .03, .016, .012, LAMP)
    write("police_car", m, stand=".box 0.2 0.07 0.09")
    g = M()
    g.box(-.008, .076, 0, .02, .012, .05, WHITE)
    write("police_light", g, (0, 0, .9), BARE)


def treasury():
    """The district attorney's desk: an open briefcase, an evidence box, a banker's lamp and a flag. The cash
    heaps up on the desk. +x faces the viewer, and the desk's long side runs along z."""
    m = M()
    # A raised floor with a rug.
    m.box(0, 0, 0, 1.1, .03, 1.7, C(0x3A2A20), top=C(0x4A3426))
    m.flat(0, .031, 0, .9, 1.45, C(0x6A1E28))
    m.flat(0, .032, 0, .78, 1.33, C(0x7E2A30))
    y0 = .03
    # The desk: a top on two pedestals of drawers.
    m.box(0, y0 + .26, 0, .52, .035, 1.25, C(0x5A341E), top=C(0x6E4226))
    m.flat(0, y0 + .2955, -.08, .36, .82, C(0x3A1A1C))
    for s in (-1, 1):
        m.box(0, y0, s * .45, .46, .26, .3, C(0x4A2A18))
        for j in range(3):
            m.face(1, .23, s * .45, y0 + .02 + j * .08, .26, .06, C(0x5E3820))
            m.face(1, .232, s * .45, y0 + .045 + j * .08, .05, .01, GOLD)
    # A chair behind the desk.
    m.box(-.42, y0, 0, .22, .16, .24, C(0x2A1A14))
    m.box(-.54, y0 + .16, 0, .05, .3, .26, C(0x3A2218), top=C(0x2A1A14))
    # The open briefcase at the near end, with a few bundles in it.
    m.at(.02, y0 + .295, .46)
    m.box(0, 0, 0, .2, .05, .28, C(0x2A1A12), top=C(0x6A1E24))
    m.box(-.1, .05, 0, .02, .2, .28, C(0x2A1A12), top=C(0x3A2418))
    m.box(-.088, .06, 0, .002, .17, .25, C(0x6A1E24))
    for i in range(3):
        m.box(.0 + .06 * (i - 1), .02 + .006 * i, -.02 * i, .062, .03, .12, BILL, top=BILL2)
    m.box(.12, .02, 0, .02, .015, .06, GOLD)
    m.at()
    # The banker's lamp.
    m.post(-.12, y0 + .295, -.55, .04, .012, GOLD, n=6)
    m.post(-.12, y0 + .307, -.55, .008, .09, GOLD, n=4)
    # The evidence box on the floor, with its lid tipped against it, and files.
    m.at(.4, y0, -.6, .3)
    m.box(0, 0, 0, .24, .16, .18, C(0xB89B6A), top=C(0x8A7048))
    m.face(1, .12, 0, .07, .24, .035, C(0xB8232F))
    m.face(0, .09, 0, .07, .18, .035, C(0xB8232F))
    for i in range(4):
        m.box(.0, .16, -.03 + .02 * i, .2, .012, .012, C(0xE0C890) if i % 2 else C(0xD2B47A))
    m.at()
    # The flag on its pole behind the desk.
    m.post(-.48, y0, .66, .02, .9, GOLD, .012, n=5)
    m.ball(-.48, y0 + .92, .66, .025, GOLD, n=5, m=2)
    def flag(u, v):
        stripe = int(v * 7) % 2 == 0
        col = RED if stripe else CREAM
        if u < .42 and v > .5: col = C(0x1E2E6E)
        return (-.48 + .02 * sin(u * 6), y0 + .58 + .3 * v - .03 * u, .66 - .5 * u), col
    m.sheet(flag, 6, 7)
    write("da_desk", m, stand=".box 0.6 0.35 1.3")
    g = M()
    g.rod((-.12, .43, -.62), (-.12, .43, -.48), .04, .04, WHITE, n=4)
    write("da_lamp", g, (0, 0, .5), BARE)


def cash_slots():
    """Where each bundle in the treasury's heap lies, in the order they arrive: from the middle out and up,
    so the heap grows as a pile and nothing floats."""
    slots = []
    for lvl, (nz, nx) in enumerate(((6, 4), (5, 3), (4, 2), (3, 1))):
        for i in range(nz):
            for j in range(nx):
                z = (i - (nz - 1) / 2) * .125
                x = (j - (nx - 1) / 2) * .066
                key = sqrt(x * x * 3 + z * z) + .13 * lvl + .001 * (i + 3 * j)
                slots.append((key, x, .327 + lvl * .031, z - .08, .06 * (noise(i * 7 + j, lvl) - .5)))
    slots.sort()
    return [(x, y, z, r) for _, x, y, z, r in slots]


def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    f = lambda v: f"{v:.4f}" if v >= 0 else f"({v:.4f})"
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/omerta/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.Omerta.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, mo, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {mo[0]}, sway := {mo[1]}, glow := {mo[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\n")
        out.write("/-- Where each bundle of cash lies on the desk, in order: x, y, z and a turn. -/\ndef cashSlots : List (Float × Float × Float × Float) :=\n  [ ")
        out.write("\n  , ".join(f"({f(x)}, {f(y)}, {f(z)}, {f(r)})" for x, y, z, r in cash_slots()) + " ]\n\n")
        out.write("/-- The street lamps round the city, as (u, v): u to the viewer's right, v away. The ground under each is lit. -/\n")
        out.write("def lamps : List (Float × Float) :=\n  [ " + ", ".join(f"({f(u)}, {f(v)})" for u, v in LAMPS) + " ]\n\n")
        out.write(f"/-- The quay's line, as u. The harbour lies to its left. -/\ndef quay : Float := {f(QUAY)}\n\n")
        out.write("end Charter.Games.Omerta.Meshes\n")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for name in os.listdir(OUT): os.remove(f"{OUT}/{name}")
    street(); sedan("sedan"); front(); club(); racket(); made()
    tile_wine(); tile_cement(); tile_fish(); tile_piazza(); bits()
    square(); monuments()
    city_ground(); skyline(); harbour(); police(); treasury()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
