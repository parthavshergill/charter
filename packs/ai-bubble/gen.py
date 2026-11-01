#!/usr/bin/env python3
"""Makes The AI Bubble's meshes: hard-edged boxes, frusta and panels, with a colour per face. Run it from
anywhere. It writes meshes/<sha256>.mesh here and the id table for Lean. It uses no packages. The same code
always makes the same bytes. Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, math, os, struct
from math import sin, cos, pi, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/AIBubble/Meshes.lean"
TOP = .16  # how high a tile's surface stands


def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def shade(c, k): return (min(1, c[0] * k), min(1, c[1] * k), min(1, c[2] * k))
def mix(a, b, t): return tuple(a[i] + (b[i] - a[i]) * t for i in range(3))


WHITE = (1., 1., 1.)
GRAPHITE, STEEL, PALE = C(0x262E3A), C(0x4A5666), C(0xB9C6D4)
INK, NIGHT, SAND = C(0x0A0E15), C(0x10161F), C(0x1A1E26)
CYAN, ICE, AMBER, RED, GREEN, CONCRETE = C(0x22E3FF), C(0xBDF4FF), C(0xFFB21F), C(0xFF2E3C), C(0x2BFF9E), C(0x8E98A3)


class M:
    """A mesh under construction. Every face has its own vertices, so a face has one colour."""

    def __init__(self):
        self.v, self.c, self.t = [], [], []

    def poly(self, pts, col, inside=None):
        """A flat polygon. `inside` is a point behind it, which fixes which way it faces."""
        n = len(self.v)
        a, b, c = pts[0], pts[1], pts[2]
        ux, uy, uz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        vx, vy, vz = c[0] - a[0], c[1] - a[1], c[2] - a[2]
        nx, ny, nz = uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx
        if inside is None:
            flip = ny < 0
        else:
            flip = (a[0] - inside[0]) * nx + (a[1] - inside[1]) * ny + (a[2] - inside[2]) * nz < 0
        order = list(reversed(pts)) if flip else list(pts)
        cols = col if isinstance(col, list) else [col] * len(pts)
        if flip and isinstance(col, list): cols = list(reversed(col))
        self.v += order
        self.c += cols
        for i in range(1, len(pts) - 1):
            self.t.append((n, n + i, n + i + 1))
        return self

    def box(self, x, y, z, w, h, d, col, top=None, front=None, rot=0.):
        """A box with its base centre at (x, y, z). `w` is along x, `d` along z. `front` colours +z and +x."""
        top = top or col
        front = front or col
        cs, sn = cos(rot), sin(rot)
        def p(a, yy, b): return (x + a * cs + b * sn, yy, z + b * cs - a * sn)
        hw, hd = w / 2, d / 2
        mid = (x, y + h / 2, z)
        y1 = y + h
        self.poly([p(-hw, y1, -hd), p(hw, y1, -hd), p(hw, y1, hd), p(-hw, y1, hd)], top, mid)
        self.poly([p(-hw, y, hd), p(hw, y, hd), p(hw, y1, hd), p(-hw, y1, hd)], front, mid)
        self.poly([p(hw, y, -hd), p(hw, y, hd), p(hw, y1, hd), p(hw, y1, -hd)], front, mid)
        self.poly([p(-hw, y, -hd), p(hw, y, -hd), p(hw, y1, -hd), p(-hw, y1, -hd)], col, mid)
        self.poly([p(-hw, y, -hd), p(-hw, y, hd), p(-hw, y1, hd), p(-hw, y1, -hd)], col, mid)
        return self

    def ring(self, x, z, prof, n=10, a0=0., cap=True):
        """A shape turned about a vertical axis. `prof` lists (radius, height, colour) from the bottom up."""
        def at(r, y, i):
            a = a0 + 2 * pi * i / n
            return (x + r * cos(a), y, z + r * sin(a))
        for j in range(len(prof) - 1):
            r0, y0, c0 = prof[j]
            r1, y1, c1 = prof[j + 1]
            mid = (x, (y0 + y1) / 2, z)
            for i in range(n):
                self.poly([at(r0, y0, i), at(r0, y0, i + 1), at(r1, y1, i + 1), at(r1, y1, i)], c1, mid)
        if cap:
            r, y, c = prof[-1]
            if r > 0:
                self.poly([at(r, y, i) for i in range(n)], c, (x, y - 1, z))
        return self

    def bar(self, a, b, r, col):
        """A thin square bar between two points."""
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        ln = sqrt(dx * dx + dy * dy + dz * dz) or 1
        # two directions across the bar
        ux, uy, uz = (dz, 0., -dx) if abs(dy) < .9 * ln else (1., 0., 0.)
        un = sqrt(ux * ux + uy * uy + uz * uz) or 1
        ux, uy, uz = ux / un * r, uy / un * r, uz / un * r
        wx, wy, wz = (dy * uz - dz * uy) / ln, (dz * ux - dx * uz) / ln, (dx * uy - dy * ux) / ln
        mid = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2, (a[2] + b[2]) / 2)
        cs = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
        def pt(p, c): return (p[0] + c[0] * ux + c[1] * wx, p[1] + c[0] * uy + c[1] * wy, p[2] + c[0] * uz + c[1] * wz)
        for i in range(4):
            self.poly([pt(a, cs[i]), pt(a, cs[(i + 1) % 4]), pt(b, cs[(i + 1) % 4]), pt(b, cs[i])], col, mid)
        return self


TABLE = []
MAX_TRIS = 12000


def write(name, m, motion=(0, 0, 0), stand=None):
    assert len(m.t) <= MAX_TRIS, f"{name} has {len(m.t)} triangles"
    mn = [min(v[a] for v in m.v) for a in range(3)]
    mx = [max(v[a] for v in m.v) for a in range(3)]
    body = struct.pack("<4sII6f", b"GPM1", len(m.v), len(m.t), *mn, *mx)
    for v in m.v:
        body += struct.pack("<3H", *[round(65535 * (v[a] - mn[a]) / ((mx[a] - mn[a]) or 1)) for a in range(3)])
    for c in m.c:
        body += bytes(max(0, min(255, round(255 * x))) for x in c)
    for t in m.t:
        body += struct.pack("<3H", *t)
    sha = hashlib.sha256(body).hexdigest()
    with open(f"{OUT}/{sha}.mesh", "wb") as out: out.write(body)
    mean = tuple(sum(c[a] for c in m.c) / len(m.c) for a in range(3))
    tint = sum(round(255 * mean[a]) << (16 - 8 * a) for a in range(3))
    r = max(mx[0], -mn[0], mx[2], -mn[2])
    TABLE.append((name, sha, tint, motion, stand or f".cylinder {max(r * .8, .01):.3f} {max(mx[1], .01):.3f}", len(m.t), len(body)))
    print(f"{name:16} {len(m.t):6} triangles {len(body):7} bytes", flush=True)


BARE = ".sphere 0.001"  # a part that is only detail has no stand-in worth seeing

# ---- the pieces. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour, and its
# grey is shade. From the game's camera a roof is what you see, so the owner's colour is on the roof.


def datacenter():
    b = M()
    L, W, H = .46, .26, .13
    b.box(0, 0, 0, L + .05, .02, W + .05, NIGHT)
    # the hall, with lit cold-aisle windows along the long sides
    b.box(0, .02, 0, L, H - .02, W, GRAPHITE, top=INK, front=shade(GRAPHITE, 1.25))
    for i in range(7):
        x = -L / 2 + .045 + i * (L - .09) / 6
        b.box(x, .05, W / 2 + .001, .032, .05, .004, ICE)
        b.box(x, .05, -W / 2 - .001, .032, .05, .004, ICE)
    b.box(L / 2 + .001, .05, 0, .004, .05, W - .08, ICE)
    # plant on the roof
    b.box(-.12, H + .004, -.02, .13, .035, .1, STEEL, top=PALE)
    b.ring(-.155, -.02, [(.03, H + .039, STEEL), (.03, H + .05, PALE)], 7)
    b.ring(-.085, -.02, [(.03, H + .039, STEEL), (.03, H + .05, PALE)], 7)
    # a generator block at the end
    b.box(-L / 2 - .05, .0, .07, .06, .07, .09, STEEL, top=PALE)
    write("dc_body", b, stand=".box 0.46 0.14 0.26")
    # the owner's colour: the roof, and a band of lights under the eaves
    k = M()
    k.box(.03, H, 0, L - .06, .006, W - .03, WHITE)
    k.box(0, H - .018, W / 2 + .003, L + .01, .018, .004, WHITE)
    k.box(0, H - .018, -W / 2 - .003, L + .01, .018, .004, WHITE)
    k.box(L / 2 + .003, H - .018, 0, .004, .018, W, WHITE)
    write("dc_led", k, (0, 0, .35), BARE)


def cooling_tower(m, x, z, r, h, col=PALE, lip=None):
    lip = lip or col
    m.ring(x, z, [(r, 0, shade(col, .55)), (r * .72, h * .55, shade(col, .85)), (r * .66, h * .78, col), (r * .74, h, lip), (r * .62, h, INK)], 12)


def campus():
    b = M()
    # the yard
    b.box(0, 0, 0, .86, .014, .72, NIGHT, top=C(0x18202C))
    # two long halls, and a block that joins them
    halls = [(-.1, -.2, .58, .2, .17), (-.1, .08, .58, .2, .22), (.28, -.06, .16, .26, .13)]
    for x, z, l, w, h in halls:
        b.box(x, .014, z, l, h, w, GRAPHITE, top=INK, front=shade(GRAPHITE, 1.25))
        for i in range(10):
            xx = x - l / 2 + .03 + i * (l - .06) / 9
            b.box(xx, .05, z + w / 2 + .001, .026, h - .07, .004, ICE)
            b.box(xx, .05, z - w / 2 - .001, .026, h - .07, .004, ICE)
        for i in range(3):
            b.box(x - l / 3 + i * l / 3, .014 + h + .004, z, .08, .03, .09, STEEL, top=PALE)
    # cooling towers at the back corner, the tallest thing on the board
    cooling_tower(b, -.32, -.34, .11, .44)
    cooling_tower(b, -.08, -.38, .1, .38)
    # a substation in the yard
    for i in range(3):
        b.box(.25 + i * .06, .014, .24, .035, .06, .05, STEEL, top=AMBER)
    b.bar((.22, .09, .24), (.42, .09, .24), .004, AMBER)
    write("campus_body", b, stand=".box 0.8 0.3 0.7")
    k = M()
    for x, z, l, w, h in halls:
        k.box(x, .014 + h, z, l - .03, .006, w - .03, WHITE)
        k.box(x, h - .006, z + w / 2 + .003, l + .01, .02, .004, WHITE)
        k.box(x + l / 2 + .003, h - .006, z, .004, .02, w, WHITE)
    k.ring(-.32, -.34, [(.086, .26, WHITE), (.078, .3, WHITE)], 12, cap=False)
    k.ring(-.08, -.38, [(.078, .22, WHITE), (.07, .26, WHITE)], 12, cap=False)
    write("campus_led", k, (0, 0, .35), BARE)
    # steam, which breathes. It is drawn see-through.
    s = M()
    for tx, tz, h0, rr in ((-.32, -.34, .44, .09), (-.08, -.38, .38, .08)):
        for j, (dx, dy, k2) in enumerate(((0, .02, .8), (.018, .1, .95))):
            s.ring(tx + dx, tz + dx * .5, [(rr * k2 * .4, h0 + dy, WHITE), (rr * k2, h0 + dy + .035, WHITE), (rr * k2 * .75, h0 + dy + .07, WHITE), (0, h0 + dy + .09, WHITE)], 7, a0=j * .4, cap=False)
    write("steam", s, (.09, .05, .05), BARE)


def fibre():
    b = M()
    # a trench, cut along the side of a hex, with a relay box halfway
    b.box(0, 0, 0, .82, .012, .1, INK, top=C(0x121923))
    b.box(0, 0, 0, .1, .05, .1, STEEL, top=PALE)
    write("fibre_bed", b, stand=".box 0.8 0.02 0.1")
    k = M()
    k.box(0, .012, 0, .82, .012, .036, WHITE)
    k.box(0, .05, 0, .06, .004, .06, WHITE)
    write("fibre_core", k, (0, 0, .5), BARE)


def law_made():
    # a radome on legs
    a = M()
    a.ring(0, 0, [(.1, 0, shade(WHITE, .55)), (.06, .08, shade(WHITE, .7)), (.12, .14, WHITE), (.12, .2, WHITE), (.08, .26, WHITE), (0, .29, WHITE)], 10)
    write("made_a", a, (0, 0, .25))
    # a rack pod
    b = M()
    b.box(0, 0, 0, .24, .22, .14, shade(WHITE, .6), top=WHITE, front=shade(WHITE, .8))
    for i in range(4):
        b.box(0, .04 + i * .04, .072, .2, .012, .004, WHITE)
    write("made_b", b, (0, 0, .25))
    # a mast
    c = M()
    c.ring(0, 0, [(.09, 0, shade(WHITE, .6)), (.05, .03, shade(WHITE, .7)), (.012, .36, WHITE)], 6, cap=False)
    c.box(0, .3, 0, .13, .012, .012, WHITE)
    c.box(0, .22, 0, .18, .012, .012, WHITE)
    write("made_c", c, (0, 0, .25))


# ---- tiles: a dark hex with what the good is painted on it, in thin raised strips.
def hex_at(r, i, a0=pi / 2):
    a = a0 + i * pi / 3
    return (r * cos(a), r * sin(a))


def hex_tile(col, side=None, r=.955):
    m = M()
    top = [(hex_at(r, i)[0], TOP, hex_at(r, i)[1]) for i in range(6)]
    m.poly(top, col, (0, 0, 0))
    side = side or shade(col, .55)
    for i in range(6):
        a, b = hex_at(r, i), hex_at(r, i + 1)
        m.poly([(a[0], 0, a[1]), (b[0], 0, b[1]), (b[0], TOP, b[1]), (a[0], TOP, a[1])], side, (0, TOP / 2, 0))
    return m


def inside(x, z, r=.9):
    ax, az = abs(x), abs(z)
    return az <= r and ax * .866 + az * .5 <= r * .866 + 1e-9 or False


def flat(m, x, z, w, d, col, h=.006, rot=0.):
    m.box(x, TOP, z, w, h, d, col, rot=rot)


def tile_silicon():
    # a circuit board: dark green, with traces that run to pads
    m = hex_tile(C(0x07261F), C(0x041712))
    tr = C(0x1EE6A0)
    for k, (a, n) in enumerate(((0., 5), (pi / 3, 5), (-pi / 3, 5))):
        cs, sn = cos(a), sin(a)
        for i in range(n):
            u = -.56 + i * .28
            for s in (-1, 1):
                v0, v1 = .3 + .05 * (i % 2), .72 - .08 * abs(i - 2)
                x0, z0 = u * cs - s * v0 * sn, u * sn + s * v0 * cs
                x1, z1 = u * cs - s * v1 * sn, u * sn + s * v1 * cs
                if not inside(x0, z0, .86) or not inside(x1, z1, .86): continue
                m.bar((x0, TOP + .002, z0), (x1, TOP + .002, z1), .009, tr)
                m.box(x1, TOP, z1, .034, .008, .034, C(0xF6D76B))
    # a square die near each of three corners
    for a in (pi / 2, pi / 2 + 2 * pi / 3, pi / 2 - 2 * pi / 3):
        x, z = .55 * cos(a), .55 * sin(a)
        m.box(x, TOP, z, .13, .022, .13, C(0x0E1317), top=C(0x2B3A3A), rot=pi / 4)
    write("tile_silicon", m, stand=".hexPrism 0.95 0.16")


def tile_power():
    # a solar field: rows of panels, with a lit amber bus
    m = hex_tile(C(0x241A0A), C(0x140E06))
    panel, frame = C(0x0E2A55), C(0xFFC34A)
    for j in range(7):
        z = -.72 + j * .24
        for i in range(-3, 4):
            x = i * .2 + (.1 if j % 2 else 0)
            if not inside(x, z, .84) or x * x + z * z < .27 * .27: continue
            # a tilted panel
            w, d = .085, .075
            m.poly([(x - w, TOP + .01, z + d), (x + w, TOP + .01, z + d), (x + w, TOP + .05, z - d), (x - w, TOP + .05, z - d)], panel, (x, TOP - 1, z))
            m.box(x, TOP, z + d + .004, w * 2, .012, .01, frame)
    write("tile_power", m, stand=".hexPrism 0.95 0.16")


def tile_concrete():
    # poured pads with joints, the palest ground on the board, with a dark cut for footings
    m = hex_tile(C(0x6F7780), C(0x3A4048))
    joint = C(0x454B53)
    for u in (-.5, -.25, 0, .25, .5):
        m.box(u, TOP, 0, .012, .004, 1.5 - abs(u) * .9, joint)
        m.box(0, TOP, u, 1.55 - abs(u) * 1.1, .004, .012, joint)
    for x, z, w, d, c in ((-.42, -.3, .3, .24, C(0xB7C0C9)), (.4, -.36, .26, .3, C(0xA4ADB6)), (.46, .28, .26, .26, C(0xBEC6CE)), (-.36, .4, .28, .2, C(0x9CA5AE))):
        m.box(x, TOP, z, w, .012, d, c)
    # hazard tape around one footing
    y1, b1 = C(0xFFC400), C(0x111111)
    for i in range(6):
        m.box(-.42 - .15 + i * .06, TOP + .012, -.3 - .125, .03, .004, .012, y1 if i % 2 else b1)
    write("tile_concrete", m, stand=".hexPrism 0.95 0.16")


def tile_exchange():
    # the trading floor: black glass and a lit ring
    m = hex_tile(C(0x070A10), C(0x05070B))
    r0, r1 = .83, .79
    for i in range(6):
        a0, a1, b0, b1 = hex_at(r0, i), hex_at(r0, i + 1), hex_at(r1, i), hex_at(r1, i + 1)
        m.poly([(a0[0], TOP + .004, a0[1]), (a1[0], TOP + .004, a1[1]), (b1[0], TOP + .004, b1[1]), (b0[0], TOP + .004, b0[1])], CYAN, (0, 0, 0))
    write("tile_exchange", m, stand=".hexPrism 0.95 0.16")


def seam():
    # a thin plate under each tile, seen in the gap between tiles. It makes the grid of the desert.
    m = M()
    m.poly([(hex_at(1., i)[0], .0, hex_at(1., i)[1]) for i in range(6)], C(0x1BD4F2), (0, -1, 0))
    write("seam", m, (0, 0, .35), ".hexPrism 1 0.01")


def bits():
    # a pallet of GPUs, wrapped, on a wooden skid
    p = M()
    p.box(0, 0, 0, .15, .014, .12, C(0x6C5230))
    p.box(0, .014, 0, .13, .036, .1, C(0x1C2A2A), top=C(0x2EFFA8))
    p.box(0, .05, 0, .13, .036, .1, C(0x1C2A2A), top=C(0x173F35), front=C(0x24403C))
    p.box(0, .086, 0, .08, .03, .1, C(0x1C2A2A), top=C(0x2EFFA8))
    write("pallet", p, stand=".box 0.15 0.11 0.12")
    # an open rack, with lights on it
    r = M()
    r.box(0, 0, 0, .09, .2, .06, C(0x14191F), top=STEEL)
    for i in range(5):
        r.box(0, .025 + i * .035, .031, .07, .012, .002, GREEN if i % 2 else CYAN)
    write("rack", r, (0, 0, .4), ".box 0.09 0.2 0.06")
    # a power pylon, with its arms across
    y = M()
    legs = [(-.05, -.05), (.05, -.05), (.05, .05), (-.05, .05)]
    for lx, lz in legs:
        y.bar((lx, 0, lz), (lx * .15, .44, lz * .15), .005, PALE)
    for h in (.14, .28):
        k = 1 - h / .44 * .85
        for a, b in zip(legs, legs[1:] + legs[:1]):
            y.bar((a[0] * k, h, a[1] * k), (b[0] * k, h, b[1] * k), .003, STEEL)
    for h, l in ((.42, .13), (.34, .17)):
        y.bar((-l, h, 0), (l, h, 0), .006, PALE)
        y.box(-l, h - .03, 0, .012, .03, .012, AMBER)
        y.box(l, h - .03, 0, .012, .03, .012, AMBER)
    write("pylon", y, stand=".cone 0.08 0.44")
    # a transformer, with a warm lit top
    t = M()
    t.box(0, 0, 0, .1, .06, .08, STEEL, top=C(0xFFB21F))
    t.ring(-.025, 0, [(.012, .06, PALE), (.008, .1, PALE)], 5)
    t.ring(.025, 0, [(.012, .06, PALE), (.008, .1, PALE)], 5)
    write("transformer", t, (0, 0, .4), ".box 0.1 0.06 0.08")
    # a tower crane, thin against the dark, with a warning light
    c = M()
    c.box(0, 0, 0, .07, .012, .07, STEEL)
    for lx, lz in ((-.012, -.012), (.012, -.012), (.012, .012), (-.012, .012)):
        c.bar((lx, 0, lz), (lx, .4, lz), .004, C(0xFFC400))
    c.bar((-.09, .4, 0), (.26, .4, 0), .007, C(0xFFC400))
    c.bar((0, .46, 0), (.22, .405, 0), .002, PALE)
    c.bar((0, .46, 0), (-.08, .405, 0), .002, PALE)
    c.box(-.08, .375, 0, .04, .03, .03, STEEL)
    c.bar((.17, .4, 0), (.17, .22, 0), .002, PALE)
    c.box(.17, .19, 0, .05, .03, .03, C(0xB7C0C9))
    write("crane", c, stand=".cone 0.05 0.4")
    # a stack of slabs
    s = M()
    s.box(0, 0, 0, .14, .022, .1, C(0xB7C0C9), top=C(0xD2D9E0))
    s.box(.005, .022, -.004, .14, .022, .1, C(0xA4ADB6), top=C(0xC6CED6), rot=.1)
    write("slabs", s, stand=".box 0.14 0.05 0.1")


def growth():
    # what spreads out from a datacenter: a row of chillers, and a battery row
    c = M()
    for i in range(3):
        c.box(i * .07 - .07, 0, 0, .055, .03, .09, STEEL, top=C(0x26C6E0))
    write("chillers", c, (0, 0, .25), ".box 0.2 0.03 0.09")
    b = M()
    b.box(0, 0, 0, .2, .04, .06, C(0x20262E), top=C(0xFFD76B))
    write("battery", b, (0, 0, .25), ".box 0.2 0.04 0.06")


def relay():
    r = M()
    r.box(0, 0, 0, .06, .05, .05, STEEL, top=PALE)
    r.box(0, .05, 0, .012, .05, .012, PALE)
    r.box(0, .1, 0, .018, .018, .018, RED)
    write("relay", r, (0, 0, .6), ".box 0.06 0.1 0.05")


# ---- the middle of the map, and the laws in force.
def exchange():
    m = M()
    m.box(0, 0, 0, .34, .03, .34, C(0x10161F), top=C(0x1C2632), rot=pi / 4)
    m.box(0, .03, 0, .17, .62, .17, INK, top=STEEL, front=C(0x101826), rot=pi / 4)
    m.box(0, .65, 0, .1, .1, .1, C(0x101826), top=PALE, rot=pi / 4)
    write("exchange", m, stand=".box 0.3 0.7 0.3")
    k = M()
    for h in (.14, .26, .38, .5):
        k.box(0, h, 0, .178, .026, .178, WHITE, rot=pi / 4)
    k.box(0, .75, 0, .02, .1, .02, WHITE)
    write("exchange_lit", k, (0, 0, .5), BARE)


def foot(m):
    m.box(0, 0, 0, .13, .012, .13, C(0x10161F), top=C(0x263240), rot=pi / 4)


def monuments():
    # a price cut: a tag that hangs from a post
    m = M(); foot(m)
    m.box(-.02, .012, 0, .018, .22, .018, STEEL)
    m.box(.04, .12, 0, .1, .09, .012, C(0xFF4FA0), top=C(0xFF8AC0))
    write("law_cost", m, (0, .03, .25), ".cone 0.07 0.25")
    # points: a scoreboard
    m = M(); foot(m)
    m.box(0, .012, 0, .03, .08, .03, STEEL)
    m.box(0, .09, 0, .16, .12, .024, INK, front=C(0x0A3A2A))
    for i in range(3):
        m.box(-.05 + i * .05, .105, .0125, .035, .03 + i * .03, .002, GREEN)
    write("law_points", m, (0, 0, .25), ".cone 0.08 0.2")
    # the bank's rate: a vault door
    m = M(); foot(m)
    m.ring(0, 0, [(.075, .012, C(0x38648F)), (.075, .1, C(0x6FA8DC)), (.055, .12, C(0xBDE0FF)), (.02, .13, WHITE)], 8)
    write("law_bank", m, (0, 0, .2), ".cylinder 0.07 0.13")
    # harvest: a stack of racks that pays
    m = M(); foot(m)
    m.box(0, .012, 0, .08, .2, .08, C(0x14191F), top=STEEL)
    for i in range(5):
        m.box(0, .03 + i * .035, .041, .06, .014, .002, CYAN)
        m.box(.041, .03 + i * .035, 0, .002, .014, .06, CYAN)
    write("law_harvest", m, (0, 0, .35), ".box 0.08 0.2 0.08")
    # build: a small crane
    m = M(); foot(m)
    m.bar((0, .012, 0), (0, .25, 0), .007, C(0xFFC400))
    m.bar((-.05, .25, 0), (.13, .25, 0), .007, C(0xFFC400))
    m.box(.11, .13, 0, .04, .05, .04, C(0xBDF4FF))
    m.bar((.11, .25, 0), (.11, .18, 0), .002, PALE)
    write("law_build", m, stand=".cone 0.07 0.26")
    # a round's end: a small cooling tower that breathes
    m = M(); foot(m)
    cooling_tower(m, 0, 0, .075, .22, PALE)
    write("law_round", m, (.05, 0, .15), ".cone 0.07 0.22")
    # the roll: an alarm with a red lamp
    m = M(); foot(m)
    m.ring(0, 0, [(.03, .012, STEEL), (.022, .15, STEEL)], 8)
    m.ring(0, 0, [(.05, .15, C(0x7A1018)), (.05, .19, RED), (.03, .23, C(0xFF8088)), (0, .25, WHITE)], 8)
    write("law_roll", m, (.05, 0, .9), ".cone 0.06 0.25")
    # a new kind of piece: a prototype under a cage
    m = M(); foot(m)
    m.box(0, .012, 0, .08, .1, .08, C(0x7A4DFF), top=C(0xC2A8FF), rot=pi / 4)
    for a in (0, pi / 2, pi, 3 * pi / 2):
        m.bar((.08 * cos(a), .012, .08 * sin(a)), (0, .2, 0), .003, PALE)
    write("law_piece", m, (0, 0, .25), ".cone 0.07 0.2")
    # a regulator's act: a broken arch with a red seal. Laws that repeal, decree or set worth use it.
    m = M(); foot(m)
    m.box(-.05, .012, 0, .03, .19, .05, C(0xE6ECF2), top=WHITE)
    m.box(.05, .012, 0, .03, .19, .05, C(0xE6ECF2), top=WHITE)
    m.box(0, .2, 0, .15, .03, .06, C(0xE6ECF2), top=WHITE)
    m.ring(0, .032, [(.036, .09, RED), (.036, .12, RED)], 8)
    write("law_repeal", m, (0, 0, .2), ".cone 0.07 0.23")


# ---- the world
def world():
    """The dark desert around the map: a floor, a fine grid, and poured pads, all outside the map's hexagon."""
    m = M()
    floor, line = C(0x0C1016), C(0x12303C)
    R = 22
    m.poly([(-R, .003, -R), (R, .003, -R), (R, .003, R), (-R, .003, R)], floor, (0, -1, 0))
    for i in range(-R, R + 1):
        w = .012 if i % 4 else .03
        c = line if i % 4 else C(0x175066)
        m.poly([(i - w, .005, -R), (i + w, .005, -R), (i + w, .005, R), (i - w, .005, R)], c, (0, -1, 0))
        m.poly([(-R, .005, i - w), (R, .005, i - w), (R, .005, i + w), (-R, .005, i + w)], c, (0, -1, 0))
    # plots already sold: poured pads on the grid, waiting for a hall
    for x, z, w, d in ((-7, 4, 1, 1), (-6, 7, 2, 1), (-4, 8, 1, 1), (2, 7, 2, 1), (7, 3, 1, 2), (8, 6, 1, 1), (6, 8, 1, 1), (-9, 1, 1, 2), (-8, -3, 2, 1), (9, -6, 1, 1)):
        m.box(x + .5, 0, z + .5, w - .08, .018, d - .08, C(0x151B24), top=C(0x202935))
    write("desert", m, stand=".box 44 0.003 44")


HALLS = [(.7071 * u - 4.75, -.7071 * u - 4.75, w, h) for u, w, h in ((-9, 1.7, .3), (-7, 1.2, .24), (-5, 1.5, .34), (-3, 1.2, .28), (-1, 1.7, .36), (1, 1.2, .26), (3, 1.5, .32), (5, 1.2, .28), (7, 1.7, .3), (9, 1.2, .24))]
# rows of halls to the left and to the near right of the map, turned the same way
HALLS += [(-7.6, 1.2, 1.4, .22), (-8.8, 0, 1.2, .26), (-6.6, 2.6, 1.1, .2), (-7.4, 5.6, 1.5, .24), (-5.6, 7.4, 1.2, .2),
          (7.0, 4.0, 1.3, .22), (5.2, 6.6, 1.5, .26), (3.4, 8.2, 1.1, .2), (8.2, 2.2, 1.2, .24)]


def far():
    """What stands around the map: halls, cooling towers, pylons and a line of lights going off."""
    m = M()
    pale = C(0x6E7F93)
    # a hall's long side faces the camera
    for x, z, w, h in HALLS:
        m.box(x, 0, z, w, h, .55, C(0x161D28), top=C(0x0D1219), front=C(0x202B39), rot=pi / 4)
        for i in range(3):
            m.box(x + (i - 1) * w * .3 * cos(pi / 4), h, z - (i - 1) * w * .3 * sin(pi / 4), .16, .05, .2, C(0x20293A), top=C(0x2F3B50), rot=pi / 4)
    for x, z, r, h in ((-8.6, -3.2, .22, .95), (-6.0, -6.0, .26, 1.1), (-3.4, -7.8, .24, 1.0), (-1.2, -8.6, .2, .85), (-8.8, 3.4, .22, .9), (6.6, 6.2, .24, 1.0)):
        m.ring(x, z, [(r, 0, C(0x1B2430)), (r * .7, h * .6, C(0x2A3644)), (r * .76, h, pale), (r * .62, h, INK)], 12)
    write("far_halls", m, stand=".box 2 0.3 2")
    # the lit windows of those halls, which breathe together
    k = M()
    for i, (x, z, w, h) in enumerate(HALLS):
        n = int(w / .13)
        for j in range(n):
            a = -w / 2 + .07 + j * (w - .14) / (n - 1)
            cs, sn = cos(pi / 4), sin(pi / 4)
            px, pz = a * cs + .278 * sn, .278 * cs - a * sn
            k.box(x + px, .06, z + pz, .07, h - .1, .006, CYAN if (i + j) % 7 else AMBER, rot=pi / 4)
    write("far_lights", k, (0, 0, .5), BARE)
    # a power line that comes in from the far corner, pylon by pylon
    p = M()
    span = [(-11 + i * 2.1, -7.2 - i * .45) for i in range(11)]
    for x, z in span:
        for lx, lz in ((-.11, -.11), (.11, -.11), (.11, .11), (-.11, .11)):
            p.bar((x + lx, 0, z + lz), (x + lx * .15, 1.15, z + lz * .15), .012, pale)
        p.bar((x - .4, 1.1, z), (x + .4, 1.1, z), .012, pale)
        p.bar((x - .3, .88, z), (x + .3, .88, z), .012, pale)
    for (a, b) in zip(span, span[1:]):
        for dz, h in ((-.4, 1.08), (.4, 1.08), (-.3, .86), (.3, .86)):
            p.bar((a[0] + dz, h, a[1]), (b[0] + dz, h - .06, b[1]), .004, C(0xFFB21F))
    write("far_line", p, stand=".box 2 1 0.2")


def meter():
    """The hype meter: a plinth, a glass tube, and rings that stack in the tube. Red bands mark where the
    dice can start to pop it."""
    b = M()
    b.ring(0, 0, [(.42, 0, C(0x1A222E)), (.42, .1, C(0x263242)), (.32, .16, C(0x344254)), (.2, .19, C(0x46586E))], 8)
    b.ring(0, 0, [(.17, .19, INK), (.17, .24, STEEL)], 12, cap=False)
    # the cage that holds the tube
    H = 2.38
    for a in (pi / 4, 3 * pi / 4, 5 * pi / 4, 7 * pi / 4):
        b.bar((.19 * cos(a), .19, .19 * sin(a)), (.19 * cos(a), H, .19 * sin(a)), .009, PALE)
    # a mark at each level where a lower roll starts to pop it
    for lvl, col in ((.24 + 8 * .105, AMBER), (.24 + 13 * .105, C(0xFF7A1F)), (.24 + 18 * .105, RED)):
        b.ring(0, 0, [(.2, lvl, col), (.2, lvl + .03, col)], 12, cap=False)
    b.ring(0, 0, [(.24, H, C(0x46586E)), (.24, H + .04, PALE), (.1, H + .08, PALE)], 8)
    write("meter_base", b, stand=".cylinder 0.4 0.2")
    # the glass
    g = M()
    g.ring(0, 0, [(.18, .24, WHITE), (.18, H, WHITE)], 12, cap=False)
    write("meter_glass", g, stand=BARE)
    # one ring of hype
    r = M()
    r.ring(0, 0, [(.16, 0, shade(WHITE, .7)), (.165, .03, WHITE), (.165, .07, WHITE), (.16, .09, WHITE)], 12)
    write("meter_ring", r, (0, 0, .6), ".cylinder 0.16 0.09")


def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/ai-bubble/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.AIBubble.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\nend Charter.Games.AIBubble.Meshes\n")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    datacenter(); campus(); fibre(); law_made()
    tile_silicon(); tile_power(); tile_concrete(); tile_exchange(); seam()
    bits(); growth(); relay(); exchange(); monuments(); world(); far(); meter()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
