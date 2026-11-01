#!/usr/bin/env python3
"""Makes The Pit's meshes: Chicago in 1886, with wheat on the prairie, pine and iron for building, and the
octagonal pit of the Board of Trade in the middle. Run it from anywhere. It writes meshes/<sha256>.mesh here
and the id table for Lean. It uses no packages. The same code always makes the same bytes.
Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, os, struct
from math import sin, cos, pi, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/ThePit/Meshes.lean"
TOP = .16  # how high a tile's surface stands


def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def shade(c, k): return (min(1, c[0] * k), min(1, c[1] * k), min(1, c[2] * k))
def mix(a, b, t): return tuple(a[i] + (b[i] - a[i]) * t for i in range(3))


WHITE = (1., 1., 1.)
# clapboard and paint
CLAP, CLAP2, TRIM = C(0xA89A80), C(0x857862), C(0x3A2A1C)  # weathered grey clapboard, so a cream roof stands out
# wood, brick and stone of the city
WOOD, WOOD2, WOOD3, BOARD = C(0x7A4E2A), C(0xA0703E), C(0x4E3018), C(0xB98A55)
BRICK, BRICK2, GRANITE, GRANITE2 = C(0x8E3B26), C(0x6E2C1C), C(0x9C9688), C(0x6E695F)
# the goods
STRAW, STRAW2, STRAW3, CHAFF = C(0xE8C35A), C(0xC99A2E), C(0x9C7420), C(0xF4DC8A)
PINE, PINE2, BARK, LOG = C(0x1F4A2C), C(0x2E6A3A), C(0x4A3020), C(0xB8834A)
RUST, RUST2, ORE, SOOT = C(0x8A3A1E), C(0x5C2614), C(0x3A2A26), C(0x1E1A18)
STEEL, STEEL2, BRASS, BRASS2 = C(0x5E6670), C(0x8E98A3), C(0xC8962E), C(0xF0C860)
INK, GREEN_BAIZE, CREAM, OXBLOOD = C(0x18120C), C(0x2C5A3A), C(0xF2E6C4), C(0x6E1A1E)
WATER, WATER2 = C(0x2E5A72), C(0x3E7490)


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
        self.v += order
        self.c += [col] * len(pts)
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

    def roof(self, x, y, z, w, h, d, col, end=None, rot=0., over=.01):
        """A gable roof along x on a box `w` by `d`, ridge `h` above `y`. `end` colours the two gable ends."""
        end = end or col
        cs, sn = cos(rot), sin(rot)
        def p(a, yy, b): return (x + a * cs + b * sn, yy, z + b * cs - a * sn)
        hw, hd = w / 2 + over, d / 2 + over
        mid = (x, y + h / 3, z)
        self.poly([p(-hw, y, hd), p(hw, y, hd), p(hw, y + h, 0), p(-hw, y + h, 0)], col, mid)
        self.poly([p(-hw, y, -hd), p(hw, y, -hd), p(hw, y + h, 0), p(-hw, y + h, 0)], col, mid)
        self.poly([p(hw - over, y, -hd + over), p(hw - over, y, hd - over), p(hw - over, y + h, 0)], end, mid)
        self.poly([p(-hw + over, y, -hd + over), p(-hw + over, y, hd - over), p(-hw + over, y + h, 0)], end, mid)
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

# ---- the pieces. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. From the
# game's camera a roof is what you see, so the owner's colour is on the roofs.


def farm():
    b = M()
    # a white clapboard farmhouse with a porch, and a round grain bin beside it
    b.box(0, 0, 0, .3, .012, .24, C(0x6E5A34))
    b.box(-.03, .012, .01, .16, .1, .12, CLAP2, top=CLAP, front=CLAP)
    for i in range(4):
        b.box(-.03, .02 + i * .022, .071, .16, .004, .002, CLAP2)
    b.box(-.07, .03, .072, .028, .055, .004, TRIM)          # the door
    b.box(-.005, .055, .072, .03, .03, .004, C(0x2A3A4A))   # a window
    b.box(.035, .055, .072, .03, .03, .004, C(0x2A3A4A))
    b.box(-.03, .012, .1, .17, .006, .05, WOOD2)             # the porch
    b.box(-.03, .1 + .03, -.02, .022, .06, .022, BRICK)      # the chimney
    b.ring(.1, -.04, [(.055, .012, STEEL2), (.055, .13, STEEL2), (.06, .13, STEEL), (0, .19, STEEL2)], 10)
    for h in (.05, .09):
        b.ring(.1, -.04, [(.056, h, STEEL), (.056, h + .006, STEEL)], 10, cap=False)
    write("farm_body", b, stand=".box 0.3 0.2 0.24")
    k = M()
    k.roof(-.03, .112, .01, .16, .07, .12, WHITE, end=shade(WHITE, .8))
    k.box(-.03, .012, .126, .17, .003, .02, WHITE)           # the porch's painted edge
    write("farm_roof", k, stand=BARE)


def elevator():
    b = M()
    # a prairie grain elevator: a tall wooden crib, a head house on top, and an office shed by the track
    b.box(0, 0, 0, .44, .014, .3, C(0x6E5A34))
    W, D, H = .18, .2, .46
    b.box(-.04, .014, 0, W, H, D, WOOD, top=WOOD3, front=WOOD2)
    for i in range(9):
        b.box(-.04, .04 + i * .05, D / 2 + .001, W, .004, .002, WOOD3)
        b.box(-.04 + W / 2 + .001, .04 + i * .05, 0, .002, .004, D, WOOD3)
    b.box(-.04, .014 + H, 0, .1, .08, .12, WOOD, top=WOOD3, front=WOOD2)   # the head house
    b.box(-.04, .2, D / 2 + .002, .05, .07, .004, INK)                     # the loading door
    # the office shed, and a spout down to a car on the siding
    b.box(.14, .014, .04, .12, .08, .12, CLAP2, top=CLAP, front=CLAP)
    b.bar((.03, .38, .05), (.18, .1, .11), .008, STEEL2)
    b.box(.0, .014, .14, .4, .01, .03, STEEL)
    write("elevator_body", b, stand=".box 0.25 0.62 0.25")
    k = M()
    k.roof(-.04, .014 + H, 0, W, .06, D, WHITE, end=shade(WHITE, .8))
    k.roof(-.04, .014 + H + .08, 0, .1, .05, .12, WHITE, end=shade(WHITE, .8))
    k.box(-.04, .3, D / 2 + .003, W + .004, .05, .003, WHITE)             # the painted band with the firm's name
    k.box(-.04 + W / 2 + .003, .3, 0, .003, .05, D + .004, WHITE)
    k.roof(.14, .094, .04, .12, .04, .12, WHITE, end=shade(WHITE, .8))
    write("elevator_paint", k, stand=BARE)


def rail():
    # a track along the side of a hex: ballast, ties in the owner's colour, and two steel rails
    b = M()
    b.box(0, 0, 0, .84, .012, .13, C(0x5A5048), top=C(0x6E6458))
    for s in (-1, 1):
        b.box(0, .022, s * .035, .84, .012, .01, STEEL, top=STEEL2)
    write("rail_bed", b, stand=".box 0.84 0.03 0.13")
    k = M()
    for i in range(9):
        k.box(-.38 + i * .095, .012, 0, .03, .01, .12, WHITE)
    write("rail_ties", k, stand=BARE)


def law_made():
    # a water tower on legs
    a = M()
    for x, z in ((-.06, -.06), (.06, -.06), (.06, .06), (-.06, .06)):
        a.bar((x, 0, z), (x * .7, .18, z * .7), .008, shade(WHITE, .6))
    a.ring(0, 0, [(.08, .18, shade(WHITE, .8)), (.08, .28, WHITE), (.09, .28, WHITE), (0, .34, WHITE)], 10)
    write("made_a", a)
    # a warehouse
    b = M()
    b.box(0, 0, 0, .26, .14, .16, shade(WHITE, .75), top=WHITE, front=shade(WHITE, .9))
    b.roof(0, .14, 0, .26, .06, .16, WHITE, end=shade(WHITE, .85))
    write("made_b", b)
    # a smokestack with a boiler house
    c = M()
    c.box(0, 0, 0, .18, .1, .14, shade(WHITE, .75), top=WHITE, front=shade(WHITE, .9))
    c.ring(.05, 0, [(.035, .1, shade(WHITE, .7)), (.025, .36, WHITE), (.032, .38, WHITE)], 8)
    write("made_c", c)


# ---- tiles: a hex with its ground built up on top
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
    return az <= r and ax * .866 + az * .5 <= r * .866 + 1e-9


def tile_wheat():
    # ploughed rows of ripe wheat, with a cut strip and a few shocks left standing
    m = hex_tile(C(0x8C6A2A), C(0x5A4418))
    for j in range(15):
        z = -.77 + j * .11
        col = STRAW if j % 2 == 0 else STRAW2
        x = -.9
        while x < .9:
            if inside(x, z, .86) and inside(x + .1, z, .86) and not (abs(x - .05) < .2 and abs(z) < .2):
                m.box(x + .05, TOP, z, .1, .028 + .008 * ((j * 7 + int(x * 10)) % 3), .07, shade(col, .8), top=col)
            x += .1
    write("tile_wheat", m, stand=".hexPrism 0.95 0.16")


def tile_lumber():
    # a pine floor with a skid road of cut logs
    m = hex_tile(C(0x24402A), C(0x14261A))
    for i in range(7):
        u = -.45 + i * .15
        m.box(u, TOP, .55 - .04 * i, .11, .012, .3, C(0x3A5A30), rot=.4)
    for i in range(5):
        m.bar((-.6 + i * .06, TOP + .02, -.5 + i * .02), (-.2 + i * .06, TOP + .02, -.62 + i * .02), .018, LOG)
    write("tile_lumber", m, stand=".hexPrism 0.95 0.16")


def tile_iron():
    # a rust-red ore range: dark ground, red spoil, and a cut face
    m = hex_tile(C(0x5C2E1E), C(0x341810))
    for x, z, w, d, c in ((-.4, -.3, .32, .2, RUST), (.38, -.42, .26, .26, RUST2), (.46, .3, .22, .28, C(0x7A3A22)), (-.32, .44, .3, .2, RUST2), (0, -.62, .3, .12, C(0x7A3A22))):
        m.box(x, TOP, z, w, .016, d, shade(c, .8), top=c, rot=.3)
    for i in range(6):
        m.box(-.62 + i * .04, TOP, .1 + i * .03, .03, .04 + .02 * i, .14, SOOT, top=ORE)
    write("tile_iron", m, stand=".hexPrism 0.95 0.16")


def tile_floor():
    # the trading floor of the Board of Trade: walnut boards and a brass ring
    m = hex_tile(C(0x5A3A20), C(0x2E1E10))
    for i in range(-8, 9):
        z = i * .1
        if inside(0, z, .9):
            m.box(0, TOP, z, 2 * (.88 - abs(z) * .58), .002, .006, C(0x3E2614))
    r0, r1 = .84, .8
    for i in range(6):
        a0, a1, b0, b1 = hex_at(r0, i), hex_at(r0, i + 1), hex_at(r1, i), hex_at(r1, i + 1)
        m.poly([(a0[0], TOP + .004, a0[1]), (a1[0], TOP + .004, a1[1]), (b1[0], TOP + .004, b1[1]), (b0[0], TOP + .004, b0[1])], BRASS, (0, 0, 0))
    write("tile_floor", m, stand=".hexPrism 0.95 0.16")


def bits():
    # a shock of wheat: sheaves stood together
    s = M()
    for k in range(5):
        a = k * 2 * pi / 5
        s.bar((.02 * cos(a), 0, .02 * sin(a)), (.008 * cos(a), .12, .008 * sin(a)), .016, STRAW if k % 2 else STRAW2)
    s.ring(0, 0, [(.03, .1, STRAW3), (0, .14, CHAFF)], 6)
    write("shock", s, stand=".cone 0.04 0.14")
    # a pine
    p = M()
    p.ring(0, 0, [(.012, 0, BARK), (.012, .05, BARK)], 5, cap=False)
    p.ring(0, 0, [(.08, .05, PINE), (0, .2, PINE2)], 7)
    p.ring(0, 0, [(.06, .14, PINE), (0, .3, PINE2)], 7)
    write("pine", p, stand=".cone 0.08 0.3")
    # a stack of logs
    g = M()
    for j, n in ((0, 3), (1, 2), (2, 1)):
        for i in range(n):
            x = (i - (n - 1) / 2) * .045
            g.bar((x, .022 + j * .04, -.08), (x, .022 + j * .04, .08), .02, LOG)
    write("logs", g, stand=".box 0.14 0.12 0.16")
    # a heap of ore
    o = M()
    o.ring(0, 0, [(.09, 0, RUST2), (.06, .04, RUST), (.02, .07, ORE), (0, .075, ORE)], 7)
    write("ore", o, stand=".cone 0.09 0.075")
    # a blast furnace stack, brick, with a glowing mouth
    f = M()
    f.ring(0, 0, [(.06, 0, BRICK2), (.05, .1, BRICK), (.035, .32, BRICK), (.04, .34, SOOT)], 8)
    f.box(0, .01, .05, .04, .04, .012, C(0xFF8A2A))
    write("furnace", f, (0, 0, .4), ".cone 0.06 0.34")


# ---- the middle of the map, the treasury and the laws in force
def pit():
    """The pit itself: an octagon of steps going down to the floor, with the price board on a post."""
    m = M()
    for j, (r, h) in enumerate(((.42, .02), (.36, .045), (.3, .07))):
        col = WOOD if j % 2 == 0 else WOOD2
        m.ring(0, 0, [(r, 0, shade(col, .7)), (r, h, col)], 8, a0=pi / 8)
    m.ring(0, 0, [(.24, .07, C(0x2A1A0E)), (.24, .072, C(0x2A1A0E))], 8, a0=pi / 8)
    # the price board: a blackboard on two posts, facing the camera, with chalked figures
    for s in (-1, 1):
        m.bar((s * .12 - .05, 0, -.05 - s * .12), (s * .12 - .05, .36, -.05 - s * .12), .01, WOOD3)
    cs, sn = .7071, .7071
    def q(u, y): return (-.05 + u * cs - .02 * sn, y, -.05 - u * sn - .02 * cs)
    m.poly([q(-.15, .2), q(.15, .2), q(.15, .36), q(-.15, .36)], INK, (-.2, .28, -.2))
    for row in range(3):
        for col_ in range(4):
            u = -.12 + col_ * .08
            y = .23 + row * .045
            a, b = q(u, y), q(u + .05, y)
            m.poly([(a[0] + .003, a[1], a[2] + .003), (b[0] + .003, b[1], b[2] + .003), (b[0] + .003, b[1] + .012, b[2] + .003), (a[0] + .003, a[1] + .012, a[2] + .003)], CREAM, (-.2, .28, -.2))
    write("pit", m, stand=".cylinder 0.42 0.07")


def treasury():
    """The treasury is the Board's secretary's desk, where unsold memberships wait. A certificate shows
    for each one on it."""
    d = M()
    d.box(0, 0, 0, .34, .14, .2, WOOD, top=GREEN_BAIZE, front=WOOD2)
    d.box(0, .14, -.08, .34, .1, .04, WOOD3, top=WOOD2)
    d.ring(.12, .02, [(.025, .14, BRASS), (.018, .2, BRASS), (.04, .22, BRASS2), (0, .26, BRASS2)], 8)
    write("desk", d, stand=".box 0.34 0.24 0.2")
    c = M()
    c.box(0, 0, 0, .12, .006, .08, CREAM, top=CREAM)
    c.box(.03, .006, .015, .022, .002, .022, OXBLOOD)
    write("certificate", c, stand=".box 0.12 0.006 0.08")


def foot(m):
    m.box(0, 0, 0, .14, .014, .14, GRANITE2, top=GRANITE, rot=pi / 4)


def monuments():
    # a price change: a chalk slate on an easel
    m = M(); foot(m)
    m.bar((-.04, .014, .02), (-.02, .24, 0), .006, WOOD3)
    m.bar((.04, .014, .02), (.02, .24, 0), .006, WOOD3)
    m.box(0, .1, .008, .12, .12, .008, INK)
    for i in range(3):
        m.box(-.02 + .02 * i, .13 + i * .025, .013, .06, .006, .002, CREAM)
    write("law_cost", m, (0, .03, 0), ".cone 0.07 0.24")
    # points: a brass trophy cup
    m = M(); foot(m)
    m.ring(0, 0, [(.04, .014, BRASS), (.015, .05, BRASS), (.015, .1, BRASS), (.06, .14, BRASS2), (.06, .2, BRASS2), (.05, .2, C(0x6A4A10))], 10)
    write("law_points", m, (0, 0, .2), ".cone 0.06 0.2")
    # the bank's rate: a stack of gold coins by a strongbox
    m = M(); foot(m)
    m.box(-.03, .014, 0, .08, .07, .07, STEEL, top=STEEL2)
    for i in range(5):
        m.ring(.05, .02, [(.025, .014 + i * .012, BRASS), (.025, .024 + i * .012, BRASS2)], 8)
    write("law_bank", m, stand=".box 0.12 0.08 0.08")
    # harvest: a tied sheaf of wheat
    m = M(); foot(m)
    for k in range(7):
        a = k * 2 * pi / 7
        m.bar((.03 * cos(a), .014, .03 * sin(a)), (.05 * cos(a), .24, .05 * sin(a)), .008, STRAW if k % 2 else STRAW2)
    m.ring(0, 0, [(.026, .1, OXBLOOD), (.026, .12, OXBLOOD)], 8, cap=False)
    write("law_harvest", m, (0, .02, 0), ".cone 0.05 0.24")
    # build: a crib going up in scaffolding
    m = M(); foot(m)
    m.box(0, .014, 0, .08, .12, .08, WOOD2, top=WOOD)
    for x, z in ((-.05, -.05), (.05, -.05), (.05, .05), (-.05, .05)):
        m.bar((x, .014, z), (x, .24, z), .004, WOOD3)
    m.bar((-.05, .2, .05), (.05, .2, .05), .004, WOOD3)
    m.bar((-.05, .2, -.05), (.05, .2, -.05), .004, WOOD3)
    write("law_build", m, stand=".box 0.1 0.24 0.1")
    # a round's end: the closing bell in its frame
    m = M(); foot(m)
    m.bar((-.06, .014, 0), (-.06, .24, 0), .008, WOOD3)
    m.bar((.06, .014, 0), (.06, .24, 0), .008, WOOD3)
    m.bar((-.07, .24, 0), (.07, .24, 0), .008, WOOD3)
    m.ring(0, 0, [(.05, .1, BRASS), (.045, .12, BRASS2), (.025, .2, BRASS2), (0, .23, BRASS)], 10)
    write("law_round", m, (.05, .02, 0), ".cone 0.07 0.24")
    # the roll: a ticker under its glass dome
    m = M(); foot(m)
    m.ring(0, 0, [(.04, .014, WOOD3), (.04, .06, WOOD2)], 8)
    m.box(0, .06, 0, .04, .03, .03, BRASS, top=BRASS2)
    m.ring(0, 0, [(.045, .06, C(0xCFE4EE)), (.045, .13, C(0xCFE4EE)), (.03, .16, C(0xE6F2F8)), (0, .17, C(0xFFFFFF))], 10, cap=False)
    m.bar((.03, .075, 0), (.12, .02, .04), .004, CREAM)
    write("law_roll", m, (0, 0, .25), ".cone 0.05 0.17")
    # a new kind of piece: a drafting table with a blueprint
    m = M(); foot(m)
    m.bar((0, .014, 0), (0, .12, 0), .008, WOOD3)
    m.poly([(-.08, .12, .05), (.08, .12, .05), (.08, .17, -.05), (-.08, .17, -.05)], C(0x2A4A8A), (0, 0, 0))
    m.poly([(-.06, .125, .04), (.0, .125, .04), (.0, .16, -.03), (-.06, .16, -.03)], C(0xD8E4F4), (0, 0, 0))
    write("law_piece", m, stand=".cone 0.07 0.17")
    # a repeal, a decree, or a law that sets a worth: a gavel on its block
    m = M(); foot(m)
    m.ring(0, 0, [(.05, .014, WOOD3), (.05, .04, WOOD2)], 10)
    m.bar((-.06, .07, .02), (.06, .07, -.02), .008, WOOD3)
    m.ring(-.06, .02, [(.022, .045, WOOD2), (.022, .095, WOOD)], 8)
    write("law_repeal", m, stand=".cone 0.06 0.1")


# ---- the world. The camera looks from +x, +z toward the far corner, so the city stands far off at -x, -z.
def prairie():
    m = M()
    R = 22
    m.poly([(-R, .003, -R), (R, .003, -R), (R, .003, R), (-R, .003, R)], C(0x5E4C26), (0, -1, 0))
    # stubble rows that run off to the horizon, outside the map
    for i in range(-20, 21):
        x = i * 1.0
        for z0, z1 in ((-21, -5.8), (5.8, 21)):
            m.poly([(x - .08, .006, z0), (x + .08, .006, z0), (x + .08, .006, z1), (x - .08, .006, z1)], C(0x6E5A2C) if i % 2 else C(0x7A6432), (0, -1, 0))
    # Lake Michigan on the right of the far side
    m.poly([(5.6, .008, -22), (22, .008, -22), (22, .008, -2), (8, .008, -2), (5.6, .008, -8)], WATER, (0, -1, 0))
    for i in range(14):
        x, z = 9 + (i * 7 % 11), -20 + i * 1.3
        m.poly([(x, .011, z), (x + 1.2, .011, z), (x + 1.2, .011, z + .05), (x, .011, z + .05)], WATER2, (0, -1, 0))
    write("prairie", m, stand=".box 44 0.003 44")


# blocks of the city, far off, as (x, z, width, height)
BLOCKS = [(-13.5 + i * 1.15, -11.2 - (i % 3) * .5, .9, .5 + .25 * ((i * 5) % 4)) for i in range(15)]
BLOCKS += [(-12.4, -7.6, 1.1, .6), (-13.2, -5.6, .9, .45), (-12.0, -9.4, 1.0, .8), (3.4, -12.6, 1.0, .7), (4.8, -12.2, .9, .55)]


def city():
    """Chicago, rebuilt in brick after the fire: blocks, chimneys, and the Board of Trade's tower."""
    m = M()
    for i, (x, z, w, h) in enumerate(BLOCKS):
        col = BRICK if i % 3 else C(0x7A5038)
        m.box(x, 0, z, w, h, .8, shade(col, .75), top=SOOT, front=col, rot=pi / 4)
        cs, sn = cos(pi / 4), sin(pi / 4)
        for j in range(int(w / .18)):
            a = -w / 2 + .1 + j * .18
            for r in range(int(h / .16)):
                m.box(x + a * cs + .401 * sn, .06 + r * .16, z + .401 * cs - a * sn, .06, .08, .006, C(0x2A2018) if (i + j + r) % 5 else C(0xF0C060), rot=pi / 4)
        m.ring(x - .2, z - .2, [(.05, h, BRICK2), (.04, h + .4, BRICK2)], 6)
    # the Board of Trade building, with its clock tower, the tallest thing in the city
    bx, bz = -8.6, -10.2
    m.box(bx, 0, bz, 2.0, 1.1, 1.3, GRANITE2, top=C(0x3A3A40), front=GRANITE, rot=pi / 4)
    m.box(bx, 0, bz, .6, 2.6, .6, GRANITE2, top=GRANITE, front=GRANITE, rot=pi / 4)
    m.ring(bx, bz, [(.34, 2.6, C(0x3A3A40)), (.0, 3.4, C(0x3A3A40))], 4, a0=pi / 4)
    m.box(bx + .2, 2.1, bz + .2, .28, .28, .02, CREAM, rot=pi / 4)
    for r in range(4):
        for j in range(6):
            a = -.8 + j * .32
            m.box(bx + a * .7071 + .656 * .7071, .12 + r * .24, bz + .656 * .7071 - a * .7071, .14, .14, .01, C(0xF0C060) if (r + j) % 3 == 0 else C(0x22201C), rot=pi / 4)
    write("city", m, stand=".box 4 1 4")
    # smoke over the city, which drifts
    s = M()
    for i, (x, z, w, h) in enumerate(BLOCKS[::2]):
        for k in range(3):
            s.ring(x - .2 + .12 * k, z - .2 - .05 * k, [(.06 + .03 * k, h + .45 + .14 * k, WHITE), (.1 + .03 * k, h + .5 + .14 * k, WHITE), (0, h + .58 + .14 * k, WHITE)], 6, cap=False)
    write("smoke", s, (.05, .06, 0), BARE)


def train():
    """A wheat train on the line into the city: an engine and a string of boxcars, on its own track."""
    m = M()
    # the track runs along the near left, from the prairie toward the city
    a, b = (-14, 0, 9), (-6.5, 0, -5)
    dx, dz = b[0] - a[0], b[2] - a[2]
    ln = sqrt(dx * dx + dz * dz)
    ux, uz = dx / ln, dz / ln
    px, pz = -uz, ux
    for i in range(int(ln / .3)):
        cx, cz = a[0] + ux * i * .3, a[2] + uz * i * .3
        m.bar((cx - px * .16, .012, cz - pz * .16), (cx + px * .16, .012, cz + pz * .16), .02, WOOD3)
    for s in (-1, 1):
        m.bar((a[0] + px * .09 * s, .04, a[2] + pz * .09 * s), (b[0] + px * .09 * s, .04, b[2] + pz * .09 * s), .012, STEEL2)
    rot = -__import__("math").atan2(uz, ux)
    t0 = 6.0
    # the engine
    cx, cz = a[0] + ux * t0, a[2] + uz * t0
    m.box(cx, .05, cz, .7, .14, .26, SOOT, rot=rot)
    m.box(cx - ux * .2, .19, cz - uz * .2, .26, .18, .26, C(0x2A2A2A), top=OXBLOOD, rot=rot)
    m.ring(cx + ux * .12, cz + uz * .12, [(.1, .19, SOOT), (.1, .3, SOOT)], 8)
    m.ring(cx + ux * .25, cz + uz * .25, [(.04, .3, SOOT), (.07, .44, SOOT), (.07, .46, BRASS)], 8)
    for k in range(5):
        tx, tz = cx - ux * (.75 + k * .62), cz - uz * (.75 + k * .62)
        m.box(tx, .05, tz, .56, .26, .26, OXBLOOD if k % 2 else C(0x8A5030), top=C(0x4A2A1A), rot=rot)
    write("train", m, stand=".box 4 0.4 0.3")


def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/the-pit/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.ThePit.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\nend Charter.Games.ThePit.Meshes\n")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    farm(); elevator(); rail(); law_made()
    tile_wheat(); tile_lumber(); tile_iron(); tile_floor()
    bits(); pit(); treasury(); monuments(); prairie(); city(); train()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
