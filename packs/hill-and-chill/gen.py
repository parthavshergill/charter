#!/usr/bin/env python3
"""Makes Hill and Chill's meshes: a house on a hill at dusk, with places to eat all around it. Shapes are
hard-edged and low, like a toy town, and the windows and signs are bright so they read at night. Run it from
anywhere. It writes meshes/<sha256>.mesh here and the id table for Lean. It uses no packages. The same code
always makes the same bytes. Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, math, os, struct
from math import sin, cos, sqrt, pi, atan2

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/HillAndChill/Meshes.lean"


def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def mix(a, b, t):
    t = max(0., min(1., t))
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)
def sstep(a, b, x):
    t = max(0., min(1., (x - a) / (b - a)))
    return t * t * (3 - 2 * t)
def wave(x, z, f, s=0.):
    return (sin(f * x + 1.7 * sin(f * .63 * z + s)) * cos(f * z + 1.3 * sin(f * .71 * x + s)) + sin(f * .5 * (x + z) + 2.1 * s) * .5) / 1.5
def hrand(i, k=0):
    """A fixed number from 0 to 1 for each i."""
    return (sin(i * 12.9898 + k * 78.233) * 43758.5453) % 1.


WHITE = (1., 1., 1.)
GRASS, GRASS2, GRASS3 = C(0x5E8F45), C(0x7AA84F), C(0x44703A)
ASPHALT, ASPHALT2, CURB = C(0x3A3A44), C(0x4A4A55), C(0xB8B2A6)
STUCCO, STUCCO2, TERRA = C(0xF2E2C4), C(0xE3C9A0), C(0xC8643A)
WOOD, WOOD2, DARK = C(0x8A5A34), C(0xB98449), C(0x3A2618)
WINDOW, WINDOW2 = C(0xFFD27A), C(0xFFB347)
NEON_PINK, NEON_TEAL, NEON_YEL = C(0xFF5FA2), C(0x3EE6D8), C(0xFFE45C)
INK, METAL, CLOTH = C(0x22202A), C(0x9AA0A8), C(0xF6F0E4)
TACO, SALSA, LEAF = C(0xF2B640), C(0xD8402A), C(0x3E8E3A)
BOBA_TEA, PEARL = C(0xD9B48A), C(0x2A1A14)


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

    def box(self, x, y, z, w, h, d, col, rot=0, top=None, front=None):
        """A box standing on y. `top` colours its top face, and `front` its +z face."""
        c, s = cos(rot), sin(rot)
        pt = lambda a, b, e: (x + a * c + e * s, y + b, z + e * c - a * s)
        hw, hd = w / 2, d / 2
        ref = (x, y + h / 2, z)
        for a in (-hw, hw):
            self.poly([pt(a, 0, -hd), pt(a, 0, hd), pt(a, h, hd), pt(a, h, -hd)], col, ref)
        for e in (-hd, hd):
            self.poly([pt(-hw, 0, e), pt(hw, 0, e), pt(hw, h, e), pt(-hw, h, e)], (front or col) if e > 0 else col, ref)
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

    def gable(self, x, y, z, w, h, d, col, roof, rot=0, over=.015):
        """A house: walls of height h, and a pitched roof along x that overhangs a little."""
        self.box(x, y, z, w, h, d, col, rot)
        c, s = cos(rot), sin(rot)
        pt = lambda a, b, e: (x + a * c + e * s, y + b, z + e * c - a * s)
        hw, hd, rh = w / 2 + over, d / 2 + over, d * .42
        ref = (x, y + h, z)
        for e in (-1, 1):
            self.poly([pt(-hw, h, e * hd), pt(hw, h, e * hd), pt(hw, h + rh, 0), pt(-hw, h + rh, 0)], roof, (x, y + h - .2, z))
        for a in (-1, 1):
            self.poly([pt(a * w / 2, h, -d / 2), pt(a * w / 2, h, d / 2), pt(a * w / 2, h + rh * (d / 2) / hd, 0)], col, ref)

    def disc(self, x, y, z, r, col, n=10, out=(0, -9, 0)):
        self.poly([(x + r * cos(2 * pi * i / n), y, z + r * sin(2 * pi * i / n)) for i in range(n)], col, out)


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


# ---- the pieces. A booth and a potluck stand on a corner. A chat lies along a side, along x.


def bench(m, x, z, rot, col, back=True):
    """A booth's bench: a seat and a tall back, in `col`."""
    m.box(x, 0, z, .17, .055, .06, col, rot)
    if back:
        c, s = cos(rot), sin(rot)
        m.box(x + .028 * s, .055, z + .028 * c, .17, .08, .02, col, rot)


def booth():
    """A diner booth: a table between two benches, with a little sign that says it is reserved."""
    b = M()
    b.box(0, 0, 0, .3, .012, .26, C(0x6B4A30))
    b.post(0, .012, 0, .014, .07, METAL, n=5)
    b.box(0, .082, 0, .18, .014, .1, C(0xEDE6D6), top=C(0xF6F1E6))
    # Plates, a sauce bottle and a reserved card.
    for dx in (-.05, .05):
        for dz in (-.025, .025):
            b.post(dx, .096, dz, .018, .004, WHITE, n=7)
    b.post(.0, .096, .0, .007, .03, SALSA, n=5)
    b.poly([(-.025, .096, .03), (.025, .096, .03), (.025, .125, .042), (-.025, .125, .042)], CLOTH, (0, .1, -.2), two=True)
    write("booth_body", b, stand=".box 0.3 0.12 0.26")
    t = M()
    bench(t, 0, -.09, 0, WHITE)
    bench(t, 0, .09, pi, WHITE)
    write("booth_tint", t, stand=BARE)


def potluck():
    """A hosted dinner: a long table in the host's colour, dishes, and string lights on two poles."""
    b = M()
    b.box(0, 0, 0, .44, .012, .3, C(0x6B4A30))
    for x in (-.17, .17):
        for z in (-.05, .05):
            b.post(x, .012, z, .009, .085, DARK, n=4)
    # Dishes down the middle: a pot, a pie, a salad and a cake.
    b.post(-.13, .112, 0, .03, .03, C(0xC8643A), n=7)
    b.post(-.13, .142, 0, .033, .005, C(0x8A3A20), n=7)
    b.post(-.04, .112, 0, .034, .01, TACO, n=8)
    b.ball(.05, .112, 0, .03, LEAF, sy=.6, n=6, m=3, base=WHITE)
    b.post(.14, .112, 0, .026, .04, C(0xF4B6C8), n=7)
    b.post(.14, .152, 0, .027, .008, WHITE, n=7)
    # Chairs.
    for x in (-.12, 0, .12):
        for s in (-1, 1):
            b.box(x, .012, s * .12, .05, .05, .05, WOOD2)
            b.box(x, .062, s * .142, .05, .06, .008, WOOD2)
    # Two poles and lights.
    for x in (-.21, .21):
        b.post(x, .012, -.13, .007, .26, DARK, n=4)
    for i in range(9):
        u = i / 8
        x = -.21 + .42 * u
        y = .27 - .05 * sin(pi * u)
        b.ball(x, y - .012, -.13, .011, WINDOW if i % 2 else C(0xFFF2B0), n=5, m=3)
    write("potluck_body", b, (0, 0, .25), ".box 0.44 0.28 0.3")
    t = M()
    # The tablecloth hangs down over the edges.
    t.box(0, .092, 0, .42, .01, .14, WHITE)
    for s in (-1, 1):
        t.poly([(-.21, .092, s * .07), (.21, .092, s * .07), (.21, .06, s * .075), (-.21, .06, s * .075)], WHITE, (0, .08, 0), two=True)
    for a in (-1, 1):
        t.poly([(a * .21, .092, -.07), (a * .21, .092, .07), (a * .215, .06, .075), (a * .215, .06, -.075)], WHITE, (0, .08, 0), two=True)
    # A banner on the line.
    t.poly([(-.06, .25, -.13), (.06, .25, -.13), (.06, .2, -.13), (-.06, .2, -.13)], WHITE, two=True)
    write("potluck_tint", t, stand=BARE)


def bubble(m, x, y, z, w, h, col, tail=1):
    """A speech bubble standing up, facing +z and -z: a rounded plate with a tail."""
    n = 12
    pts = [(x + w / 2 * cos(2 * pi * i / n), y + h / 2 * sin(2 * pi * i / n)) for i in range(n)]
    for d in (-.012, .012):
        m.poly([(px, py, z + d) for px, py in pts], col, (x, y, z - d * 9))
    for i in range(n):
        a, b = pts[i], pts[(i + 1) % n]
        m.poly([(a[0], a[1], z - .012), (b[0], b[1], z - .012), (b[0], b[1], z + .012), (a[0], a[1], z + .012)], col, (x, y, z))
    tx = x - tail * w * .25
    for d in (-.012, .012):
        m.poly([(tx - .012, y - h * .38, z + d), (tx + .02, y - h * .38, z + d), (tx - tail * .03, y - h * .5 - .035, z + d)], col, two=True)


def chat():
    """The group chat: three bubbles on posts along a side, each with its typing dots."""
    b = M()
    t = M()
    xs = (-.24, 0, .24)
    for i, x in enumerate(xs):
        y = .12 + .03 * (i % 2)
        b.post(x, 0, 0, .008, y - .04, C(0x6A6470), n=4)
        bubble(t, x, y, 0, .17, .1, WHITE, 1 if i % 2 else -1)
        for k in (-1, 0, 1):
            for d in (-.0135, .0135):
                b.ball(x + k * .035, y, d, .01, C(0x2A2A34), n=5, m=2)
    b.box(0, 0, 0, .62, .012, .05, C(0x6A6470))
    write("chat_body", b, (0, .02, 0), ".box 0.6 0.14 0.05")
    write("chat_tint", t, (0, .02, 0), BARE)


def made():
    """Pieces that a law makes, in white so the owner's colour shows: a food cart, a picnic blanket and a mic."""
    m = M()
    m.box(0, .03, 0, .2, .1, .12, WHITE)
    for s in (-1, 1):
        m.post(s * .07, .0, .065, .026, .012, WHITE, n=6)
    m.post(-.06, .13, 0, .006, .1, WHITE, n=4)
    m.poly([(-.06, .25, 0), (.1, .24, -.08), (.1, .24, .08)], WHITE, two=True)
    write("made_cart", m, stand=".box 0.2 0.25 0.12")
    m = M()
    m.box(0, 0, 0, .26, .012, .22, WHITE)
    m.post(-.06, .012, -.04, .045, .06, WHITE, n=7)
    m.box(.06, .012, .04, .08, .05, .06, WHITE)
    write("made_picnic", m, stand=".box 0.26 0.07 0.22")
    m = M()
    m.post(0, 0, 0, .06, .015, WHITE, n=8)
    m.post(0, .015, 0, .008, .2, WHITE, n=4)
    m.ball(0, .23, 0, .028, WHITE, n=6, m=3)
    m.box(.09, 0, 0, .1, .07, .07, WHITE)
    write("made_mic", m, stand=".cylinder 0.08 0.25")


# ---- tiles: an exact hexagon, flat on top at y = 0.16, with its place at the back, away from the token.

N = 14
TOP = .16


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


def tile(name, col, extra=None, hgt=None, edge=GRASS3, motion=(0, 0, 0)):
    """col(x, z) colours the top. A grass verge runs round the rim, so neighbouring tiles match."""
    m = M()
    ids, pts = lattice()
    vert = []
    for (x, z) in pts:
        r = hexd(x, z)
        c = mix(col(x, z), mix(GRASS3, GRASS, .5 + .5 * wave(x, z, 9., 2.)), sstep(.84, .9, r))
        y = TOP + (hgt(x, z) if hgt and r < .84 and sqrt(x * x + z * z) > .27 else 0)
        vert.append(((x, y, z), c))
    for (q, s), i in ids.items():
        for a, b in (((q + 1, s), (q, s + 1)), ((q + 1, s), (q + 1, s - 1))):
            if a in ids and b in ids:
                A, B, D = vert[i], vert[ids[a]], vert[ids[b]]
                m.poly([A[0], B[0], D[0]], [A[1], B[1], D[1]], (A[0][0], -9, A[0][2]))
    corners = [(0, 1), (.866, .5), (.866, -.5), (0, -1), (-.866, -.5), (-.866, .5)]
    for i in range(6):
        a, b = corners[i], corners[(i + 1) % 6]
        m.poly([(a[0], TOP, a[1]), (b[0], TOP, b[1]), (b[0], 0, b[1]), (a[0], 0, a[1])], [edge, edge, C(0x2E3A28), C(0x2E3A28)], (0, .1, 0))
    if extra:
        extra(m)
        m.at()
    write(name, m, motion, ".hexPrism 0.96 0.16")


def back(m, rot=0):
    """Puts a building at the back of a tile, away from the token and the corners."""
    m.at(-.36, TOP, -.36, pi / 4 + rot)


def windows(m, x, y, z, w, h, cols, rows, col=WINDOW, face=1, rot=0, depth=.0):
    """A grid of lit windows on the +z (face 1) or -z face of a box centred on x, z."""
    for i in range(cols):
        for j in range(rows):
            u = x - w / 2 + w * (i + .5) / cols
            v = y + h * (j + .5) / rows
            m.box(u, v - .012, z + face * depth, w / cols * .55, .024, .006, col)


def tiles():
    def lot(x, z):
        c = mix(ASPHALT, ASPHALT2, .5 + .5 * wave(x, z, 14., 1.))
        if abs((x + z) * .7071 % .2 - .1) < .006 and .3 < sqrt(x * x + z * z) < .7: c = C(0xE8E0C0)
        return c

    def station(m):
        back(m)
        m.box(0, 0, 0, .52, .012, .3, CURB)
        for x in (-.18, .18):
            m.post(x, 0, .0, .015, .2, C(0xE6E6EA), n=4)
        m.box(0, .2, 0, .56, .035, .3, C(0xE84A3A), top=C(0xF2F2F2))
        m.box(0, .2, .151, .56, .035, .004, NEON_YEL)
        for x in (-.09, .09):
            m.box(x, .012, .0, .05, .09, .05, C(0xF2F2F2), front=C(0x3A3A44))
            m.box(x, .07, .026, .03, .02, .004, NEON_TEAL)
        # A shop at the back and a tall sign.
        m.box(0, 0, -.25, .46, .14, .12, STUCCO, top=C(0xD8D0C0), front=STUCCO2)
        m.box(0, .03, -.188, .3, .07, .006, WINDOW)
        m.post(.32, 0, -.12, .012, .42, METAL, n=4)
        m.box(.32, .36, -.12, .13, .1, .03, C(0xE84A3A))
        m.box(.32, .375, -.104, .09, .05, .004, NEON_YEL)
    tile("tile_gas", lot, station, edge=C(0x3A3A44))

    def plaza(x, z):
        c = mix(C(0x8FB86A), C(0x7AA84F), .5 + .5 * wave(x, z, 8., 3.))
        if abs(x * .7071 - z * .7071) < .07: c = C(0xD8CDB8)
        return c

    def office(m):
        back(m)
        m.box(0, 0, -.08, .34, .38, .2, C(0x7C8FA8), top=C(0x5A6A80), front=C(0x8FA2BA))
        windows(m, 0, .05, .02, .3, .3, 4, 4, col=WINDOW, depth=.003)
        m.box(0, 0, .03, .1, .06, .02, C(0x2A3A4A))
        # The ATM, lit green, and a bank sign with a dollar on it.
        m.box(.26, 0, .0, .08, .14, .06, C(0xC8CCD2), front=C(0x3A4048))
        m.box(.26, .08, .031, .05, .03, .004, C(0x6CFFA0))
        m.box(-.05, .38, -.08, .16, .07, .03, C(0x2E7D4A))
        m.box(-.05, .395, -.064, .03, .04, .004, C(0xD8FFE0))
        for x in (-.27, .32):
            m.post(x, 0, .12, .01, .05, DARK, n=4)
            m.ball(x, .1, .12, .055, GRASS2, n=6, m=3)
    tile("tile_cash", plaza, office)

    def pastel(x, z):
        c = mix(C(0xF0C4D4), C(0xE8B0C4), .5 + .5 * sin(30 * x) * sin(30 * z))
        if sqrt(x * x + z * z) > .7: c = mix(c, GRASS2, .6)
        return c

    def shop(m):
        back(m)
        m.box(0, 0, -.1, .34, .16, .18, C(0xFFF4E8), top=C(0xF29BB8), front=C(0xFFE8F0))
        m.box(0, .03, -.009, .24, .08, .006, WINDOW2)
        # A striped awning.
        for i in range(6):
            x0 = -.18 + .06 * i
            m.poly([(x0, .16, -.01), (x0 + .06, .16, -.01), (x0 + .06, .12, .07), (x0, .12, .07)], NEON_PINK if i % 2 else WHITE, (0, 0, -.3), two=True)
        # A giant cup on the roof, with pearls at the bottom and a straw.
        m.post(0, .16, -.1, .05, .18, C(0xE9F4FF), .07, n=10)
        m.post(0, .165, -.1, .052, .05, PEARL, .056, n=10)
        m.post(0, .215, -.1, .056, .11, BOBA_TEA, .068, n=10)
        m.post(0, .34, -.1, .074, .012, C(0xF6F0FF), n=10)
        m.rod((.02, .34, -.1), (.04, .44, -.1), .01, .01, NEON_PINK, n=4)
        for x in (-.26, .27):
            m.post(x, 0, .05, .05, .006, WHITE, n=7)
            m.post(x, 0, .05, .006, .07, METAL, n=3)
            m.post(x, .07, .05, .05, .006, C(0x7AD8D0), n=7)
    tile("tile_boba", pastel, shop, edge=GRASS3)

    def dirt(x, z):
        c = mix(C(0xC9A26A), C(0xB88A52), .5 + .5 * wave(x, z, 12., 5.))
        if sqrt(x * x + z * z) > .72: c = mix(c, GRASS2, .7)
        return c

    def truck(m):
        back(m)
        # A taco truck with a hatch, an awning and a menu board.
        m.box(0, .035, -.08, .4, .17, .17, C(0xF6E9D0), top=C(0xE8D8B8))
        m.box(.16, .035, -.08, .1, .1, .172, C(0x2A3E5A))
        m.box(-.04, .1, .006, .2, .08, .004, C(0x3A2A20))
        m.poly([(-.15, .19, .005), (.07, .19, .005), (.07, .175, .07), (-.15, .175, .07)], SALSA, (0, 0, -.3), two=True)
        for x in (-.13, .1):
            for z in (-.17, .0):
                m.post(x, 0, z, .032, .035, INK, n=7)
        m.box(-.04, .2, -.08, .26, .07, .02, TACO)
        m.box(-.04, .215, -.069, .18, .035, .004, SALSA)
        # String lights to a post, and a picnic table.
        m.post(.32, 0, .12, .01, .3, DARK, n=4)
        for i in range(8):
            u = i / 7
            m.ball(-.15 + .47 * u, .28 - .05 * sin(pi * u) - .02 * u, -.0 + .12 * u, .012, WINDOW if i % 2 else NEON_PINK, n=5, m=3)
        m.box(.18, 0, .2, .2, .06, .1, WOOD2, top=WOOD)
    tile("tile_takeout", dirt, truck, edge=GRASS3)

    def hilltop(x, z):
        c = mix(GRASS2, GRASS, .5 + .5 * wave(x, z, 7., 9.))
        r = sqrt(x * x + z * z)
        if abs(r - .3) < .03 or (abs(x * .7071 - z * .7071) < .05 and r > .3): c = C(0xD8CDB8)
        return c
    tile("tile_hill", hilltop)


def bits():
    q = M()
    for i in range(6):
        a, b = pi / 6 + i * pi / 3, pi / 6 + (i + 1) * pi / 3
        co = lambda r, t: (r * cos(t), .012, r * sin(t))
        q.poly([co(.8, a), co(.8, b), co(.96, b), co(.96, a)], NEON_YEL, (0, -9, 0))
    write("hot_ring", q, (0, 0, .7), BARE)

    t = M()
    t.post(0, 0, 0, .012, .08, WOOD, n=4)
    t.ball(0, .11, 0, .055, GRASS2, sy=1.1, n=6, m=3, base=GRASS3)
    write("tree", t, (0, .02, 0), ".cone 0.05 0.16")

    p = M()
    p.rod((0, 0, 0), (.015, .26, .005), .012, .008, C(0x8A6A48), n=4)
    for i in range(6):
        a = 2 * pi * i / 6 + .3
        tx, tz = .015 + .12 * cos(a), .005 + .12 * sin(a)
        mx, mz = .015 + .06 * cos(a), .005 + .06 * sin(a)
        wx, wz = -sin(a) * .02, cos(a) * .02
        col = C(0x3E8E3A) if i % 2 else C(0x5AAE48)
        p.poly([(.015, .26, .005), (mx + wx, .29, mz + wz), (mx - wx, .29, mz - wz)], col, two=True)
        p.poly([(mx + wx, .29, mz + wz), (tx, .2, tz), (mx - wx, .29, mz - wz)], col, two=True)
    write("palm", p, (0, .03, 0), ".cone 0.06 0.28")

    l = M()
    l.post(0, 0, 0, .006, .2, INK, n=4)
    l.rod((0, .2, 0), (.04, .21, 0), .004, .004, INK, n=3)
    l.ball(.045, .2, 0, .014, WINDOW, n=5, m=3)
    write("lamp", l, (0, 0, .2), ".cone 0.02 0.2")

    c = M()
    c.box(0, 0, 0, .04, .006, .04, C(0xE8602A))
    c.post(0, .006, 0, .014, .045, C(0xF07030), .003, n=5)
    c.post(0, .02, 0, .0115, .008, WHITE, n=5)
    write("cone", c, stand=".cone 0.02 0.05")

    k = M()
    k.post(0, 0, 0, .02, .05, C(0xE9F4FF), .026, n=7)
    k.post(0, .002, 0, .021, .03, BOBA_TEA, .024, n=7)
    k.rod((.005, .05, 0), (.01, .075, 0), .004, .004, NEON_PINK, n=3)
    write("cup", k, stand=".cylinder 0.025 0.07")

    b = M()
    b.box(0, 0, 0, .12, .04, .06, WOOD2, top=WOOD)
    for s in (-1, 1):
        b.box(0, 0, s * .055, .12, .022, .025, WOOD)
    write("picnic", b, stand=".box 0.12 0.05 0.12")

    car = M()
    car.box(0, .012, 0, .16, .04, .08, WHITE)
    car.box(-.01, .052, 0, .09, .03, .072, C(0x9ED0F0), top=WHITE)
    for x in (-.05, .05):
        for z in (-.04, .04):
            car.post(x, 0, z, .016, .02, INK, n=5)
    write("car", car, stand=".box 0.16 0.08 0.08")

    o = M()
    o.post(0, 0, 0, .028, .006, C(0xF2C840), n=7)
    o.post(0, .006, 0, .025, .002, C(0xFFE27A), n=7)
    write("coin", o, (0, 0, .3), ".cylinder 0.03 0.01")

    f = M()
    for i in range(5):
        a = 2 * pi * i / 5
        f.ball(.025 * cos(a), .012, .025 * sin(a), .014, [C(0xFF7AA8), C(0xFFD24A), C(0xB07AFF)][i % 3], n=4, m=2)
    f.ball(0, .006, 0, .03, GRASS3, sy=.4, n=6, m=2)
    write("flowers", f, stand=BARE)


# ---- the square: the house on the hill, where everyone lives and nobody can pick a place to eat.


def square():
    m = M()
    m.post(0, 0, 0, .27, .02, C(0xD8CDB8), n=10)
    # The house: two storeys, a porch with a couch, lit windows and a satellite dish.
    m.gable(0, .02, -.03, .34, .2, .24, C(0xF2E2C4), TERRA, over=.02)
    for x in (-.1, 0, .1):
        m.box(x, .13, .09, .045, .04, .006, WINDOW)
        m.box(x, .05, .09, .045, .045, .006, WINDOW2 if x else C(0x6A3A2A))
    for x in (-.1, .1):
        m.box(x, .13, -.15, .045, .04, .006, WINDOW)
    m.box(0, .02, .14, .36, .012, .08, WOOD)
    for x in (-.17, .17):
        m.post(x, .02, .175, .008, .11, WOOD2, n=4)
    m.box(0, .13, .14, .38, .008, .09, TERRA)
    m.box(.06, .032, .15, .13, .03, .045, C(0x5A6ACF))
    m.box(.06, .062, .132, .13, .03, .012, C(0x5A6ACF))
    m.ball(-.22, .26, -.06, .03, C(0xDADAE0), sy=.4, n=6, m=2)
    # The group's cars, all parked badly, and a palm.
    m.rod((.16, .24, -.03), (.16, .3, -.03), .006, .006, INK, n=3)
    write("square_house", m, stand=".box 0.4 0.3 0.4")
    # Lights along the porch, which twinkle.
    s = M()
    for i in range(11):
        u = i / 10
        s.ball(-.19 + .38 * u, .125 - .02 * sin(pi * u), .19, .009, [WINDOW, NEON_PINK, NEON_TEAL][i % 3], n=4, m=2)
    write("square_lights", s, (0, 0, .5), BARE)


def base(m, w=.1):
    m.post(0, 0, 0, w * .9, .02, C(0xD8CDB8), n=8)


def monuments():
    # A cost: a price tag on a stake.
    m = M()
    base(m)
    m.post(0, .02, 0, .008, .14, WOOD, n=4)
    m.poly([(-.06, .26, 0), (.04, .26, 0), (.08, .2, 0), (.04, .14, 0), (-.06, .14, 0)], C(0xFFE45C), two=True)
    m.ball(.045, .2, .003, .008, INK, n=4, m=2)
    m.box(-.03, .19, .002, .05, .02, .004, INK)
    write("mon_cost", m, stand=".cone 0.08 0.26")
    # Points: a trophy cup.
    m = M()
    base(m)
    m.box(0, .02, 0, .08, .04, .08, INK)
    m.post(0, .06, 0, .012, .05, C(0xF2C840), n=5)
    m.post(0, .11, 0, .03, .07, C(0xF2C840), .055, n=8)
    for s in (-1, 1):
        m.rod((s * .045, .17, 0), (s * .07, .14, 0), .007, .007, C(0xF2C840), n=3)
    write("mon_points", m, (0, 0, .2), ".cylinder 0.06 0.2")
    # The bank: an ATM.
    m = M()
    base(m)
    m.box(0, .02, 0, .11, .2, .08, C(0xC8CCD2), front=C(0x3A4048))
    m.box(0, .15, .041, .07, .04, .004, C(0x6CFFA0))
    m.box(0, .08, .041, .05, .008, .004, INK)
    write("mon_bank", m, (0, 0, .2), ".box 0.11 0.22 0.08")
    # A harvest: a takeout bag.
    m = M()
    base(m)
    m.box(0, .02, 0, .1, .13, .07, C(0xC9A26A), top=C(0xB88A52))
    m.rod((-.03, .15, 0), (.03, .15, 0), .006, .006, C(0x8A6A48), n=3)
    m.box(0, .07, .036, .05, .04, .004, SALSA)
    write("mon_harvest", m, stand=".box 0.1 0.16 0.07")
    # A build: a traffic cone and a sawhorse.
    m = M()
    base(m)
    m.post(-.03, .02, 0, .035, .14, C(0xF07030), .004, n=6)
    m.post(-.03, .07, 0, .026, .02, WHITE, .022, n=6)
    m.box(.05, .1, .0, .04, .02, .12, C(0xFFE45C))
    for z in (-.05, .05):
        m.rod((.05, .02, z), (.05, .1, z), .006, .006, WOOD, n=3)
    write("mon_build", m, stand=".cone 0.07 0.16")
    # A round's end: the moon over the hill.
    m = M()
    base(m)
    m.post(0, .02, 0, .006, .14, INK, n=3)
    m.ball(0, .2, 0, .055, C(0xFFF2C0), n=8, m=4)
    m.ball(.03, .21, .03, .045, C(0x2A2440), n=6, m=3)
    write("mon_round", m, (0, 0, .3), ".sphere 0.06")
    # A roll: two dice on a table.
    m = M()
    base(m)
    m.box(-.022, .02, .012, .07, .07, .07, CLOTH, rot=.3)
    m.box(.02, .09, -.008, .056, .056, .056, CLOTH, rot=-.5)
    m.box(.02, .147, -.008, .012, .003, .012, SALSA)
    write("mon_roll", m, stand=".cylinder 0.07 0.16")
    # A new piece: a "now open" sign.
    m = M()
    base(m)
    for x in (-.06, .06):
        m.post(x, .02, 0, .007, .15, INK, n=3)
    m.box(0, .13, 0, .17, .08, .015, NEON_PINK, front=C(0xFFD0E4))
    m.box(0, .155, .009, .12, .02, .004, INK)
    write("mon_piece", m, (0, 0, .4), ".box 0.17 0.2 0.04")
    # A repeal: a sign that says closed, knocked crooked.
    m = M()
    base(m)
    m.post(0, .02, 0, .008, .12, INK, n=3)
    m.at(0, .14, 0, 0, 1)
    m.poly([(-.07, .0, .0), (.07, .03, .0), (.07, .11, .0), (-.07, .08, .0)], SALSA, two=True)
    m.poly([(-.05, .035, .003), (.05, .055, .003), (.05, .065, .003), (-.05, .045, .003)], WHITE, two=True)
    m.at()
    write("mon_repeal", m, stand=".cylinder 0.05 0.25")


# ---- the world: the hill the board stands on, the town lights below, the moon, and the host stand.


def hillside():
    """The ground: a plateau where the board and the host stand sit, falling away to the town below."""
    m = M()
    n, R = 46, 26.
    def h(x, z):
        # The board's table never goes below the app's own table, so the hill reads by colour: green on
        # top, then the dark valley with the town's lights, then low ridges at the back.
        r = sqrt(x * x + z * z)
        back = sstep(0, 1, (-(x + z) * .7071 - 9) / 6)
        return .004 + .02 * sstep(6.2, 7., r) * (1 - sstep(7., 9., r)) + 1.6 * back * sstep(11., 18., r) * (.6 + .4 * wave(x, z, .35, 4.))
    def col(x, z, y):
        r = sqrt(x * x + z * z)
        c = mix(C(0x4E7A3E), C(0x3E6A34), .5 + .5 * wave(x, z, .7, 1.))
        c = mix(c, C(0x1A2236), sstep(6.6, 8.4, r))
        c = mix(c, C(0x14182A), sstep(.2, 1.4, y))
        return c
    step = 2 * R / n
    grid = {}
    for i in range(n + 1):
        for j in range(n + 1):
            x, z = -R + i * step, -R + j * step
            y = h(x, z)
            grid[(i, j)] = ((x, y, z), col(x, z, y))
    for i in range(n):
        for j in range(n):
            a, b, c, d = grid[(i, j)], grid[(i + 1, j)], grid[(i + 1, j + 1)], grid[(i, j + 1)]
            m.poly([a[0], b[0], c[0]], [a[1], b[1], c[1]], (a[0][0], -20, a[0][2]))
            m.poly([a[0], c[0], d[0]], [a[1], c[1], d[1]], (a[0][0], -20, a[0][2]))
    # A road winding down the hill, from the host stand.
    for k in range(40):
        t0, t1 = k / 40, (k + 1) / 40
        def road(t):
            a = -.32 + 2.4 * t
            r = 6.3 + 7. * t
            return (r * cos(a), r * sin(a))
        p0, p1 = road(t0), road(t1)
        dx, dz = p1[0] - p0[0], p1[1] - p0[1]
        L = sqrt(dx * dx + dz * dz)
        nx, nz = -dz / L * .22, dx / L * .22
        q = [(p0[0] + nx, h(*p0) + .03, p0[1] + nz), (p1[0] + nx, h(*p1) + .03, p1[1] + nz),
             (p1[0] - nx, h(*p1) + .03, p1[1] - nz), (p0[0] - nx, h(*p0) + .03, p0[1] - nz)]
        m.poly(q, C(0x4A4A55), (0, -20, 0))
        if k % 2 == 0:
            m.poly([((q[0][0] + q[3][0]) / 2 + dx * .1, q[0][1] + .005, (q[0][2] + q[3][2]) / 2 + dz * .1),
                    ((q[1][0] + q[2][0]) / 2 - dx * .1, q[1][1] + .005, (q[1][2] + q[2][2]) / 2 - dz * .1),
                    ((q[1][0] + q[2][0]) / 2 - dx * .1 + nx * .12, q[1][1] + .005, (q[1][2] + q[2][2]) / 2 - dz * .1 + nz * .12),
                    ((q[0][0] + q[3][0]) / 2 + dx * .1 + nx * .12, q[0][1] + .005, (q[0][2] + q[3][2]) / 2 + dz * .1 + nz * .12)], C(0xE8D890), (0, -20, 0))
    write("hillside", m, stand=".box 40 0.01 40")
    # The town below: rows of small lit windows along streets in the valley. They twinkle.
    t = M()
    k = 0
    for st in range(16):
        a0 = 2 * pi * hrand(st, 1)
        r0 = 7.6 + 5.5 * hrand(st, 2)
        bend = (hrand(st, 3) - .5) * .5
        for j in range(16):
            a = a0 + j * (.05 + .03 * hrand(st, 4)) + bend * j * .02
            r = r0 + j * .12 * (hrand(st, 5) - .5)
            for side in (-.13, .13):
                k += 1
                if hrand(k, 6) < .35: continue
                x, z = (r + side) * cos(a), (r + side) * sin(a)
                w = .045 + .03 * hrand(k, 7)
                col = [WINDOW, WINDOW2, C(0xFFF2C0), WINDOW, NEON_PINK, WINDOW2, NEON_TEAL][k % 7]
                t.box(x, h(x, z), z, w, .012, w, col, rot=a)
    write("town_lights", t, (0, 0, .35), BARE)


def host_stand():
    """The treasury: the restaurant's host stand, with a tip jar. No-show fees end up here."""
    m = M()
    m.box(0, 0, 0, 1.2, .03, .9, C(0xD8CDB8))
    m.box(0, .03, 0, .32, .42, .24, C(0x3A2618), top=C(0x5A3A24), front=C(0x4A3020))
    m.box(0, .45, .02, .36, .02, .28, C(0x6B4A30))
    m.box(.0, .47, .04, .14, .01, .1, CLOTH)
    m.post(-.1, .47, -.04, .045, .1, C(0xE0F0F8), .05, n=10)
    m.post(-.1, .47, -.04, .042, .03, C(0x6CB86A), .044, n=10)
    # A sign on a stand: "please wait to be seated".
    m.post(.38, .03, .1, .012, .42, C(0xC8A040), n=4)
    m.box(.38, .3, .1, .22, .16, .02, INK, front=C(0x2A2A34))
    m.box(.38, .36, .112, .16, .02, .004, CLOTH)
    m.box(.38, .32, .112, .12, .015, .004, CLOTH)
    m.box(.38, .285, .112, .14, .015, .004, CLOTH)
    m.post(.38, .03, .1, .08, .012, C(0xC8A040), n=7)
    # Velvet rope.
    for x in (-.45, -.25):
        m.post(x, .03, .3, .015, .22, C(0xC8A040), n=5)
        m.ball(x, .26, .3, .022, C(0xC8A040), n=5, m=3)
    for i in range(6):
        u0, u1 = i / 6, (i + 1) / 6
        m.rod((-.45 + .2 * u0, .22 - .06 * sin(pi * u0), .3), (-.45 + .2 * u1, .22 - .06 * sin(pi * u1), .3), .01, .01, C(0xA0203A), n=4, caps=False)
    write("host_stand", m, stand=".box 0.9 0.45 0.6")


def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/hill-and-chill/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.HillAndChill.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\nend Charter.Games.HillAndChill.Meshes\n")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    booth(); potluck(); chat(); made()
    tiles(); bits(); square(); monuments()
    hillside(); host_stand()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
