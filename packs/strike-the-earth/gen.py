#!/usr/bin/env python3
"""Makes Strike the Earth's meshes. Small shapes come from signed distances, by surface nets. The mountain
itself is a few plain grids, because a grid gives crisp layers of rock for few triangles. Run it from
anywhere. It writes meshes/<sha256>.mesh here and the id table for Lean. It uses no packages. The same
code always makes the same bytes. Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, math, os, struct
from math import sin, cos, sqrt, pi

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/StrikeTheEarth/Meshes.lean"
S2 = .7071

# ---- shapes: a shape takes a point and gives (distance, colour). Inside is negative.
def C(rgb): return ((rgb >> 16 & 255) / 255, (rgb >> 8 & 255) / 255, (rgb & 255) / 255)
def mix(a, b, t): return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)
def sstep(a, b, x):
    t = max(0., min(1., (x - a) / (b - a)))
    return t * t * (3 - 2 * t)
def wave(x, y, z, f, s=0.):
    return (sin(f * x + 1.7 * sin(f * .63 * z + s)) * cos(f * z + 1.3 * sin(f * .71 * y + s)) + sin(f * .5 * (x + z) + 2.1 * s) * .5) / 1.5

def ball(cx, cy, cz, r, col):
    return lambda x, y, z: (sqrt((x - cx) ** 2 + (y - cy) ** 2 + (z - cz) ** 2) - r, col)
def egg(cx, cy, cz, rx, ry, rz, col):
    m = min(rx, ry, rz)
    return lambda x, y, z: ((sqrt(((x - cx) / rx) ** 2 + ((y - cy) / ry) ** 2 + ((z - cz) / rz) ** 2) - 1) * m, col)
def rod(a, b, ra, rb, col):
    dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
    n = dx * dx + dy * dy + dz * dz
    def f(x, y, z):
        t = max(0., min(1., ((x - a[0]) * dx + (y - a[1]) * dy + (z - a[2]) * dz) / n))
        return (sqrt((x - a[0] - t * dx) ** 2 + (y - a[1] - t * dy) ** 2 + (z - a[2] - t * dz) ** 2) - (ra + (rb - ra) * t), col)
    return f
def block(cx, cy, cz, hx, hy, hz, col, r=.012):
    def f(x, y, z):
        qx, qy, qz = abs(x - cx) - hx + r, abs(y - cy) - hy + r, abs(z - cz) - hz + r
        out = sqrt(max(qx, 0) ** 2 + max(qy, 0) ** 2 + max(qz, 0) ** 2)
        return out + min(max(qx, qy, qz), 0) - r, col
    return f
def union(*ss):
    def f(x, y, z):
        best = (1e9, None)
        for s in ss:
            r = s(x, y, z)
            if r[0] < best[0]: best = r
        return best
    return f
def blend(k, *ss):
    def f(x, y, z):
        d, c = ss[0](x, y, z)
        for s in ss[1:]:
            e, c2 = s(x, y, z)
            h = max(0., min(1., .5 + .5 * (e - d) / k))
            d, c = e + (d - e) * h - k * h * (1 - h), mix(c2, c, h)
        return d, c
    return f
def carve(k, a, b):
    def f(x, y, z):
        d, c = a(x, y, z)
        e, c2 = b(x, y, z)
        h = max(0., min(1., .5 - .5 * (e + d) / k))
        return d + (-e - d) * h + k * h * (1 - h), mix(c, c2, h)
    return f
def rough(s, amp, freq, seed=0.):
    def f(x, y, z):
        d, c = s(x, y, z)
        return d + amp * wave(x, y, z, freq, seed), c
    return f
def paint(s, fn):
    def f(x, y, z):
        d, c = s(x, y, z)
        return d, fn(x, y, z, c)
    return f
def faced(s):
    """A shape drawn with its front along +z and its right along +x, turned so its front meets the camera."""
    def f(x, y, z):
        return s(S2 * (x - z), y, S2 * (x + z))
    return f

# ---- surface nets: a vertex in each cell the surface crosses, and a quad across each crossed edge.
def nets(shape, lo, hi, cell, floor):
    nx, ny, nz = [int(math.ceil((hi[a] - lo[a]) / cell)) + 1 for a in range(3)]
    ids = lambda i, j, k: i + nx * (j + ny * k)
    field = [shape(lo[0] + i * cell, lo[1] + j * cell, lo[2] + k * cell)[0]
             for k in range(nz) for j in range(ny) for i in range(nx)]
    corners = [(i, j, k) for k in (0, 1) for j in (0, 1) for i in (0, 1)]
    edges = [(a, b) for a in range(8) for b in range(a + 1, 8) if sum(x != y for x, y in zip(corners[a], corners[b])) == 1]
    cells, verts = {}, []
    for k in range(nz - 1):
        for j in range(ny - 1):
            for i in range(nx - 1):
                v = [field[ids(i + c[0], j + c[1], k + c[2])] for c in corners]
                if min(v) >= 0 or max(v) < 0: continue
                sx = sy = sz = n = 0
                for a, b in edges:
                    if (v[a] < 0) != (v[b] < 0):
                        t = v[a] / (v[a] - v[b])
                        sx += corners[a][0] + t * (corners[b][0] - corners[a][0])
                        sy += corners[a][1] + t * (corners[b][1] - corners[a][1])
                        sz += corners[a][2] + t * (corners[b][2] - corners[a][2])
                        n += 1
                cells[(i, j, k)] = len(verts)
                verts.append((lo[0] + (i + sx / n) * cell, lo[1] + (j + sy / n) * cell, lo[2] + (k + sz / n) * cell))
    tris = []
    def quad(a, b, c, d, flip):
        if flip: b, d = d, b
        ids4 = [cells.get(q) for q in (a, b, c, d)]
        if None in ids4: return
        p, q, r, s = ids4
        tris.extend([(p, q, r), (p, r, s)])
    for k in range(nz):
        for j in range(ny):
            for i in range(nx):
                d0 = field[ids(i, j, k)] < 0
                if i < nx - 1 and j and k and d0 != (field[ids(i + 1, j, k)] < 0):
                    quad((i, j - 1, k - 1), (i, j, k - 1), (i, j, k), (i, j - 1, k), not d0)
                if j < ny - 1 and i and k and d0 != (field[ids(i, j + 1, k)] < 0):
                    quad((i - 1, j, k - 1), (i - 1, j, k), (i, j, k), (i, j, k - 1), not d0)
                if k < nz - 1 and i and j and d0 != (field[ids(i, j, k + 1)] < 0):
                    quad((i - 1, j - 1, k), (i, j - 1, k), (i, j, k), (i - 1, j, k), not d0)
    # What lies under the table is never seen, so it is not kept.
    tris = [t for t in tris if max(verts[v][1] for v in t) > floor]
    used = sorted({v for t in tris for v in t})
    new = {v: n for n, v in enumerate(used)}
    return [verts[v] for v in used], [tuple(new[v] for v in t) for t in tris]

TABLE = []
MAX_TRIS = 12000
def write(name, verts, cols, tris, motion, stand):
    assert len(tris) <= MAX_TRIS, f"{name} has {len(tris)} triangles"
    mn = [min(v[a] for v in verts) for a in range(3)]
    mx = [max(v[a] for v in verts) for a in range(3)]
    body = struct.pack("<4sII6f", b"GPM1", len(verts), len(tris), *mn, *mx)
    for v in verts:
        body += struct.pack("<3H", *[round(65535 * (v[a] - mn[a]) / ((mx[a] - mn[a]) or 1)) for a in range(3)])
    for c in cols:
        body += bytes(max(0, min(255, round(255 * x))) for x in c)
    for t in tris:
        body += struct.pack("<3H", *t)
    sha = hashlib.sha256(body).hexdigest()
    with open(f"{OUT}/{sha}.mesh", "wb") as out: out.write(body)
    mean = tuple(sum(c[a] for c in cols) / len(cols) for a in range(3))
    tint = sum(round(255 * mean[a]) << (16 - 8 * a) for a in range(3))
    r = max(mx[0], -mn[0], mx[2], -mn[2])
    TABLE.append((name, sha, tint, motion, stand or f".cylinder {r * .9:.3f} {max(mx[1], .01):.3f}", len(tris), len(body)))
    print(f"{name:14} {len(tris):6} triangles {len(body):7} bytes", flush=True)

def mesh(name, shape, size, cell, motion=(0, 0, 0), stand=None, floor=-.02, lo=None, hi=None):
    """One mesh file. `size` is half the width and the height of the box it fits in."""
    lo = lo or (-size[0], floor - cell, -size[0])
    hi = hi or (size[0], size[1], size[0])
    verts, tris = nets(shape, lo, hi, cell, floor)
    write(name, verts, [shape(*v)[1] for v in verts], tris, motion, stand)

def grid(name, nu, nv, fn, up, motion=(0, 0, 0), stand=None):
    """A sheet of (nu + 1) by (nv + 1) points. `fn(u, v)` gives a point and a colour, for u and v from 0 to 1.
    `up` is the side to show."""
    verts, cols = [], []
    for j in range(nv + 1):
        for i in range(nu + 1):
            x, y, z, c = fn(i / nu, j / nv)
            verts.append((x, y, z))
            cols.append(c)
    id_ = lambda i, j: i + (nu + 1) * j
    tris = []
    for j in range(nv):
        for i in range(nu):
            a, b, c, d = id_(i, j), id_(i + 1, j), id_(i + 1, j + 1), id_(i, j + 1)
            # Cut each cell along the diagonal with the sharper fold, so ridges stay ridges.
            ya, yb, yc, yd = verts[a][1], verts[b][1], verts[c][1], verts[d][1]
            if abs(ya - yc) < abs(yb - yd): tris += [(a, b, c), (a, c, d)]
            else: tris += [(a, b, d), (b, c, d)]
    def facing(t):
        p, q, r = [verts[k] for k in t]
        ux, uy, uz = q[0] - p[0], q[1] - p[1], q[2] - p[2]
        vx, vy, vz = r[0] - p[0], r[1] - p[1], r[2] - p[2]
        return (uy * vz - uz * vy) * up[0] + (uz * vx - ux * vz) * up[1] + (ux * vy - uy * vx) * up[2]
    if sum(facing(t) for t in tris) < 0:
        tris = [(t[0], t[2], t[1]) for t in tris]
    write(name, verts, cols, tris, motion, stand)

# ---- colours
WHITE = (1., 1., 1.)
BARE = ".sphere 0.001"
PALE, STONE, DARKSTONE = C(0xC4BCAC), C(0x9A9386), C(0x5E5A54)
TIMBER, TIMBER2 = C(0x6E4A2A), C(0x4A3019)
FLAME, FLAME2, LAVA, LAVA2 = C(0xFFD27A), C(0xFF8A24), C(0xFF5A14), C(0xFFC23A)
GOLD, COPPER = C(0xF2C94C), C(0xD9823A)
DARK = C(0x1B1A1F)

def coursed(c):
    """Rows of cut stone."""
    return lambda x, y, z, k: mix(k, mix(k, DARKSTONE, .55), sstep(.75, 1., abs(sin(y * 74))))

# ---- the pieces. A white mesh takes the seat's colour from the draw. Grey in it is shade.
def hall():
    walls = block(0, .058, 0, .118, .06, .105, STONE, .018)
    door = block(0, .042, .1, .036, .05, .035, C(0x7A3A10), .012)
    mesh("hall_stone", faced(paint(carve(.008, walls, door), lambda x, y, z, c: c if z > .07 and abs(x) < .05 and y < .1 else coursed(STONE)(x, y, z, c))), (.2, .13), .034)
    def roof(x, y, z):
        return max(y - (.235 - 1.05 * max(abs(x), abs(z) * 1.12)), .1 - y, abs(x) - .136, abs(z) - .122), WHITE
    mesh("hall_roof", faced(paint(roof, lambda x, y, z, c: mix(c, (.7, .7, .7), sstep(.75, 1., abs(sin(y * 62)))))), (.2, .25), .03, floor=.095)
    mesh("hall_fire", faced(union(egg(-.088, .098, .118, .014, .026, .014, FLAME), egg(.088, .098, .118, .014, .026, .014, FLAME),
                                  block(0, .045, .098, .026, .038, .012, FLAME2, .006))), (.16, .14), .017, (.0, 0, .55), BARE, floor=.0)

def workshop():
    walls = union(block(0, .08, 0, .21, .085, .155, STONE, .02), block(.135, .2, -.085, .05, .2, .05, DARKSTONE, .01),
                  block(-.21, .05, .09, .03, .055, .03, STONE), block(.21, .05, .09, .03, .055, .03, STONE))
    mouth = block(0, .055, .15, .07, .06, .035, C(0x7A3A10), .012)
    mesh("shop_stone", faced(paint(carve(.008, walls, mouth), coursed(STONE))), (.33, .42), .044)
    def gable(x, y, z):
        return max(y - (.27 - .62 * abs(z)), abs(x) - .225, .15 - y), WHITE
    mesh("shop_roof", faced(paint(gable, lambda x, y, z, c: mix(c, (.68, .68, .68), sstep(.7, 1., abs(sin(x * 30)))))), (.32, .3), .044, floor=.14)
    mesh("shop_fire", faced(union(block(0, .058, .126, .056, .05, .012, FLAME, .008), egg(.135, .41, -.085, .036, .045, .036, FLAME2))),
         (.24, .47), .024, (.0, 0, .7), BARE, floor=.0)

def tunnel():
    ribs = lambda x, y, z, c: mix(c, (.55, .55, .55), sstep(.72, .96, abs(sin(x * 15))))
    body = blend(.02, rod((-.56, -.01, 0), (.56, -.01, 0), .068, .068, WHITE), *[egg(u, 0, 0, .025, .082, .082, WHITE) for u in (-.42, -.21, 0, .21, .42)])
    mesh("tunnel", paint(body, ribs), None, .052, (0, 0, 0), ".box 0.95 0.05 0.11", floor=.002, lo=(-.6, -.04, -.12), hi=(.6, .1, .12))

def farm():
    stalks = union(rod((0, 0, 0), (0, .13, 0), .02, .015, PALE), rod((.075, 0, .045), (.075, .08, .045), .015, .012, PALE), rod((-.068, 0, .05), (-.068, .075, .05), .014, .011, PALE))
    mesh("farm_stalks", stalks, (.12, .15), .024, floor=-.002)
    caps = union(egg(0, .145, 0, .074, .046, .074, WHITE), egg(.075, .09, .045, .05, .032, .05, WHITE), egg(-.068, .083, .05, .046, .03, .046, WHITE))
    mesh("farm_caps", paint(caps, lambda x, y, z, c: mix(c, (.62, .62, .62), sstep(.35, .7, wave(x, y, z, 62.)))), (.14, .2), .024, (0, .02, .22), ".sphere 0.07", floor=.05)

def gate():
    posts = union(block(-.088, .105, 0, .03, .105, .036, PALE), block(.088, .105, 0, .03, .105, .036, PALE), block(0, .225, 0, .135, .03, .046, STONE), block(0, .275, 0, .05, .022, .03, PALE))
    mesh("gate_stone", paint(posts, coursed(PALE)), (.17, .31), .03, floor=-.002)
    mesh("gate_door", paint(block(0, .095, 0, .06, .095, .016, WHITE, .006), lambda x, y, z, c: mix(c, (.6, .6, .6), sstep(.7, .95, abs(sin(x * 52))))), (.08, .2), .022, floor=-.002)

def shaft():
    legs = [rod((sx * .105, 0, sz * .085), (sx * .018, .35, 0), .024, .018, TIMBER) for sx in (-1, 1) for sz in (-1, 1)]
    braces = [rod((-.07, .13, .055), (.07, .13, .055), .013, .013, TIMBER2), rod((-.07, .13, -.055), (.07, .13, -.055), .013, .013, TIMBER2),
              ]
    wheel = egg(0, .37, 0, .044, .044, .012, C(0x2E2A28))
    rim = carve(.01, block(0, .012, 0, .105, .014, .09, DARKSTONE, .008), block(0, .03, 0, .072, .03, .06, C(0x20100A), .006))
    mesh("shaft_frame", union(*legs, *braces, wheel, rim), (.14, .43), .026, floor=-.002)
    mesh("shaft_pit", paint(block(0, .01, 0, .08, .026, .068, LAVA, .006), lambda x, y, z, c: mix(LAVA2, c, sstep(.0, .06, sqrt(x * x + z * z)))), (.11, .05), .024, (0, 0, .75), BARE, floor=-.002)
    mesh("shaft_flag", union(block(.062, .335, 0, .058, .036, .007, WHITE, .004), block(.09, .275, 0, .03, .03, .007, (.8, .8, .8), .004)), (.16, .39), .018, floor=.2, stand=BARE)

def epitaph():
    def stone(x, y, z):
        w = .056 - .082 * y
        qx, qz = abs(x) - w, abs(z) - w
        d = max(qx, qz, y - .39, -y)
        return d, PALE
    grooves = lambda x, y, z, c: mix(c, C(0x4C463E), sstep(.68, .95, abs(sin(y * 58))) * sstep(.024, .04, abs(x) + abs(z)) * .9)
    mesh("epitaph_stone", paint(union(stone, block(0, .014, 0, .085, .016, .085, STONE)), grooves), (.11, .42), .024, floor=-.002)
    def cap(x, y, z):
        w = max(0., .034 - .17 * (y - .36))
        return max(abs(x) - w - .002, abs(z) - w - .002, y - .46, .36 - y), WHITE
    mesh("epitaph_cap", cap, (.06, .48), .016, (0, 0, .25), BARE, floor=.34)

def pieces():
    hall(); workshop(); tunnel(); farm(); gate(); shaft(); epitaph()

# ---- tile tops: a low hex with a chipped edge. The middle stays flat under the number token.
def patch(surface, colour, seed, edge=.965, wob=.02):
    def hexd(x, z):
        ax, az = abs(x), abs(z)
        return max(ax, ax * .5 + az * .866) - .866 * edge
    def f(x, y, z):
        r = sqrt(x * x + z * z)
        side = hexd(x, z) + wob * wave(x, 0, z, 9., seed)
        rim = .012 * sstep(-.1, -.03, side)
        h = .15 + surface(x, z) * sstep(.26, .4, r) + rim
        a, b, k = y - h, side, .022
        t = max(0., min(1., .5 + .5 * (b - a) / k))
        return a + (b - a) * t + k * t * (1 - t), colour(x, y, z, r, side)
    return f
def tile(name, surface, colour, seed, stand=".hexPrism 0.96 0.15"):
    mesh(name, patch(surface, colour, seed), (1.0, .23), .078, stand=stand, floor=-.03)

def lit(c, side):
    """A dark, chipped edge, so that each tile reads on its own."""
    return mix(c, mix(c, (0., 0., 0.), .55), sstep(-.06, -.015, side))

def tiles():
    def rock(x, y, z, r, side):
        band = sstep(-.15, .15, sin((x * .6 + z) * 9 + 1.1 * wave(x, 0, z, 2.2)))
        c = mix(C(0x3E4356), C(0x6B7188), band)
        return lit(mix(c, C(0x24252E), sstep(.82, .97, abs(wave(x, 0, z, 9., 4.)))), side)
    tile("tile_stone", lambda x, z: .012 + .03 * wave(x, 0, z, 7., 1.), rock, 1.)
    def vein(x, y, z, r, side):
        c = mix(C(0x3B2B22), C(0x5C4331), sstep(-.3, .5, wave(x, y, z, 8., 2.)))
        v = 1 - sstep(.0, .13, abs(wave(x, 0, z, 3.6, 5.)))
        v2 = 1 - sstep(.0, .09, abs(wave(x, 0, z, 6.3, 9.)))
        c = mix(c, C(0xF0A83A), max(v, v2 * .75))
        return lit(c, side)
    tile("tile_ore", lambda x, z: .008 + .018 * wave(x, 0, z, 9., 4.), vein, 2.)
    def fung(x, y, z, r, side):
        c = mix(C(0x2C1F3C), C(0x4A3160), sstep(-.3, .4, wave(x, y, z, 6., 3.)))
        moss = sstep(.1, .45, wave(x, 0, z, 4.4, 6.))
        c = mix(c, C(0x22B394), moss)
        return lit(mix(c, C(0x7CF0D2), .55 * sstep(.45, .75, wave(x, 0, z, 13., 8.)) * moss), side)
    tile("tile_fungus", lambda x, z: .01 + .022 * wave(x, 0, z, 5., 7.), fung, 3.)
    def basalt(x, y, z, r, side):
        c = mix(C(0x171214), C(0x2F2525), sstep(-.3, .5, wave(x, y, z, 11., 6.)))
        return lit(c, side)
    tile("tile_ember", lambda x, z: .022 * abs(wave(x, 0, z, 8., 2.)), basalt, 4.)
    def seam(x, z):
        return abs(wave(x, 0, z, 3.1, 1.3))
    # The seam is a flat ribbon just above the basalt, only where the crack runs. It keeps off the token.
    def seam_shape(x, y, z):
        r = sqrt(x * x + z * z)
        d = max(seam(x, z) - .1, .3 - r, y - .172, .158 - y, max(abs(x), abs(x) * .5 + abs(z) * .866) - .8)
        return d * .6, mix(LAVA2, LAVA, sstep(.0, .09, seam(x, z)))
    mesh("seam", seam_shape, (.9, .2), .04, (0, 0, .7), BARE, floor=.12)
    def floor_stone(x, y, z, r, side):
        a = math.atan2(z, x)
        slab = sstep(.72, .96, abs(sin(a * 3))) * sstep(.48, .52, r)
        ring = sstep(.012, .0, abs(r - .47) - .012) + sstep(.012, .0, abs(r - .81) - .012)
        c = mix(C(0x6F695F), C(0x8E877A), sstep(-.4, .5, wave(x, y, z, 6., 2.)))
        return lit(mix(mix(c, C(0x3C3833), slab), C(0x2C2622), min(1., ring)), side)
    tile("tile_chamber", lambda x, z: 0., floor_stone, 5.)
    def runes(x, y, z):
        r = sqrt(x * x + z * z)
        a = math.atan2(z, x)
        broken = max(abs(r - .47) - .017, -(abs(sin(a * 6)) - .22) * .1, y - .178, .14 - y)
        outer = max(abs(r - .81) - .013, -(abs(sin(a * 9)) - .3) * .1, y - .178, .14 - y)
        return min(broken, outer), LAVA2
    mesh("runes", runes, (.9, .2), .036, (0, 0, .5), BARE, floor=.1)

def bits():
    mesh("rubble", rough(union(egg(0, .02, 0, .07, .045, .055, C(0x777B8C)), egg(.06, .012, .03, .036, .028, .032, C(0x9EA2B2))), .006, 40.), (.11, .08), .026, stand=BARE, floor=-.004)
    spike = rough(rod((0, 0, 0), (.01, .24, -.005), .05, .004, C(0x8A8EA0)), .004, 50.)
    mesh("stalag", paint(spike, lambda x, y, z, c: mix(C(0x565A6C), C(0xC3C7D4), sstep(.0, .22, y))), (.08, .27), .024, stand=".cone 0.05 0.2", floor=-.004)
    def crystal(cx, cz, h, r, col):
        def f(x, y, z):
            w = r * (1 - sstep(h * .55, h, y))
            d = max(abs(x - cx) + abs(z - cz) - w, y - h, -y)
            return d * .7, mix(col, (1., .95, .75), sstep(h * .3, h, y))
        return f
    mesh("ore_chunk", union(crystal(0, 0, .16, .05, C(0xE8982C)), crystal(.05, .03, .1, .034, C(0xD9823A)), crystal(-.045, .03, .085, .03, C(0xF2C94C))), (.1, .18), .02, (0, 0, .22), ".cone 0.05 0.14", floor=-.004)
    def cap(col, lit_):
        return union(rod((0, 0, 0), (.006, .17, 0), .013, .009, C(0xC9D8D0)), paint(egg(.006, .18, 0, .062, .03, .062, col), lambda x, y, z, c: mix(c, lit_, sstep(.3, .7, wave(x, y, z, 70.)))))
    mesh("cap_teal", cap(C(0x2FCDB0), C(0xBDFFF0)), (.08, .22), .022, (0, .02, .35), ".cone 0.05 0.2", floor=-.004)
    mesh("cap_violet", cap(C(0x9A6CE8), C(0xE6D6FF)), (.08, .22), .022, (0, .02, .3), ".cone 0.05 0.2", floor=-.004)
    mesh("hot_rock", paint(rough(egg(0, .025, 0, .07, .05, .06, C(0x241C1C)), .006, 44.), lambda x, y, z, c: mix(c, LAVA, sstep(.35, .55, abs(wave(x, y, z, 34.)))) ), (.09, .09), .022, (0, 0, .3), BARE, floor=-.004)
    # A brazier for the rim of the map. It is what makes the place read as torchlit.
    mesh("brazier_body", union(rod((0, 0, 0), (0, .2, 0), .03, .016, DARKSTONE), egg(0, .23, 0, .07, .034, .07, C(0x3A3430))), (.09, .27), .024, stand=".cylinder 0.05 0.25", floor=-.002)
    mesh("brazier_fire", union(egg(0, .28, 0, .05, .07, .05, FLAME2), egg(0, .31, 0, .026, .045, .026, FLAME)), (.07, .37), .022, (.06, .03, .75), BARE, floor=.2)

# ---- a law's stone, by what the law is about.
def stele(name, shape, h=.42, cell=.021, motion=(0, 0, .05)):
    foot = union(block(0, .012, 0, .078, .014, .078, STONE, .006), block(0, .036, 0, .056, .012, .056, PALE, .004))
    mesh(name, union(foot, shape), (.15, h), cell, motion, ".cone 0.08 0.3", floor=-.003)

def monuments():
    pillar = lambda h: block(0, h / 2, 0, .022, h / 2, .022, PALE, .004)
    stele("law_cost", union(pillar(.15), block(0, .165, 0, .075, .016, .034, C(0x8E94A2), .004), block(0, .19, 0, .042, .014, .024, C(0x8E94A2), .004), block(0, .217, 0, .09, .02, .032, C(0xC2C8D4), .004),
                            egg(-.095, .218, 0, .034, .014, .024, C(0xC2C8D4))), h=.26)
    crown = [rod((.05 * cos(i * 1.257), .245, .05 * sin(i * 1.257)), (.05 * cos(i * 1.257), .29, .05 * sin(i * 1.257)), .013, .004, GOLD) for i in range(5)]
    stele("law_points", union(pillar(.19), block(0, .2, 0, .04, .012, .04, PALE, .004), egg(0, .232, 0, .06, .022, .06, GOLD), *crown), h=.33)
    def ingots():
        out = []
        for i in range(3):
            for j in range(3 - i):
                out.append(block(-.036 * (2 - i) + .072 * j, .068 + .036 * i, .02, .033, .016, .05, mix(GOLD, COPPER, (i + j) % 2 * .55), .006))
        return out
    stele("law_bank", union(*ingots()), h=.2)
    stele("law_harvest", union(rod((0, .04, 0), (0, .19, 0), .022, .016, C(0xC9D8D0)), paint(egg(0, .205, 0, .09, .05, .09, C(0x2FCDB0)), lambda x, y, z, c: mix(c, C(0xD5FFF4), sstep(.3, .65, wave(x, y, z, 54.)))),
                            rod((.05, .04, .03), (.06, .11, .03), .012, .008, C(0xC9D8D0)), egg(.06, .12, .03, .042, .022, .042, C(0x9A6CE8))), h=.28, motion=(0, .012, .22))
    pick = lambda s: union(rod((s * -.07, .05, 0), (s * .07, .25, 0), .017, .017, C(0x9A6A3A)), rod((s * .07 - .085, .29, 0), (s * .07 + .085, .235, 0), .024, .012, C(0xE4E8F0)))
    stele("law_build", union(pick(1), pick(-1)), h=.33)
    stele("law_round", union(rod((0, .04, 0), (0, .15, 0), .022, .03, DARKSTONE), egg(0, .17, 0, .082, .04, .082, C(0x3A3430)), egg(0, .215, 0, .05, .07, .05, FLAME2), egg(0, .24, 0, .025, .045, .025, FLAME)), h=.33, motion=(.04, 0, .6))
    die = lambda cx, cy, cz, s: paint(block(cx, cy, cz, s, s, s, C(0xDDD5C4), .012), lambda x, y, z, c: mix(c, LAVA, sstep(.55, .85, cos((x - cx) * 40 / s * .12) * cos((z - cz) * 40 / s * .12) * cos((y - cy) * 40 / s * .12))))
    stele("law_roll", union(die(0, .1, 0, .052), die(.012, .19, .006, .037)), h=.26, motion=(0, 0, .4))
    def gem(x, y, z):
        return (abs(x) + abs(y - .19) + abs(z) - .082) * .577, mix(C(0x35D0E8), C(0xD8FBFF), sstep(.16, .26, y))
    stele("law_piece", union(pillar(.11), gem), h=.3, motion=(0, 0, .5))
    broken = carve(.012, block(0, .135, 0, .042, .11, .042, PALE, .004), rod((-.07, .25, .06), (.06, .17, -.06), .036, .036, C(0x3A3430)))
    crack = lambda x, y, z, c: mix(c, LAVA, sstep(.82, .97, abs(sin((x + z) * 26 + y * 11))) * sstep(.035, .18, y))
    stele("law_broken", union(paint(broken, crack), block(.075, .02, .05, .022, .014, .03, STONE, .005), block(-.05, .018, .08, .018, .012, .02, PALE, .004)), h=.26, motion=(0, 0, .3))
    # The head of the founder: the huge carved thing at the centre of the chamber.
    def head():
        skull = egg(0, .475, -.01, .17, .185, .16, STONE)
        helm = union(egg(0, .545, -.01, .185, .15, .175, C(0x7A7468)), block(0, .59, 0, .026, .13, .17, C(0xB89A52), .012), block(0, .49, .125, .17, .018, .04, C(0xB89A52), .008))
        beard = blend(.05, egg(0, .33, .06, .175, .13, .12, PALE), egg(0, .2, .085, .13, .12, .085, PALE), egg(0, .095, .1, .08, .09, .055, PALE))
        nose = egg(0, .42, .16, .036, .05, .045, STONE)
        brow = block(0, .452, .135, .13, .016, .035, C(0x7A7468), .012)
        pits = union(egg(-.07, .415, .15, .036, .024, .03, C(0x201A16)), egg(.07, .415, .15, .036, .024, .03, C(0x201A16)))
        base = union(block(0, .03, 0, .25, .032, .22, C(0x6F695F), .02), block(0, .1, -.04, .17, .06, .14, STONE, .02))
        strands = lambda x, y, z, c: mix(c, C(0x7E7668), sstep(.55, .95, abs(sin(x * 46 + 1.1 * sin(y * 13)))) if y < .4 else 0)
        return union(carve(.02, blend(.03, skull, brow, nose), pits), helm, paint(beard, strands), base)
    mesh("founder", faced(head()), (.3, .78), .03, (0, 0, 0), ".cone 0.22 0.7", floor=-.003)
    mesh("founder_eyes", faced(union(egg(-.07, .415, .165, .022, .014, .012, FLAME), egg(.07, .415, .165, .022, .014, .012, FLAME))), (.2, .46), .007, (0, 0, .9), BARE, floor=.3)

# ---- the mountain. a is toward the viewer and b to the right. The player's table lies at height 0 and the
# camera never turns, so the cut face below the map is painted on a low slope. From the one place anyone
# can look, it reads as a wall going down into the magma.
def world(a, b): return S2 * (a + b), S2 * (a - b)
TILES = [(0, 0), (1, -1), (-1, 1), (1, 0), (-1, 0), (0, 1), (0, -1), (2, -1), (-2, 1), (2, 0), (-2, 2), (1, 1), (-1, 2), (0, 2), (-1, -1), (3, -1), (-2, 3)]
CENTRES = [((1.732 * (q + r / 2) + 1.5 * r) * S2, (1.732 * (q + r / 2) - 1.5 * r) * S2) for q, r in TILES]
def front(b): return 5.05 + .32 * sin(b * 1.1) + .17 * sin(b * 2.9 + 1.)
BAND = 5.2  # how far the painted face runs toward the viewer

RIVERS = [[(-5.2, 7.9), (-3.6, 7.2), (-1.6, 6.7), (.4, 7.3), (2.2, 7.3), (3.8, 6.9), (front(6.9), 6.9)],
          [(-5.2, -7.3), (-3.8, -6.5), (-2.2, -5.5), (-.4, -5.8), (1.6, -6.2), (3.4, -5.9), (front(-5.9), -5.9)]]
def river_dist(a, b):
    best = 9.
    for pts in RIVERS:
        for p, q in zip(pts, pts[1:]):
            da, db = q[0] - p[0], q[1] - p[1]
            t = max(0., min(1., ((a - p[0]) * da + (b - p[1]) * db) / (da * da + db * db)))
            best = min(best, sqrt((a - p[0] - t * da) ** 2 + (b - p[1] - t * db) ** 2))
    return best

def ground_height(a, b):
    near = min(sqrt((a - ca) ** 2 + (b - cb) ** 2) for ca, cb in CENTRES)
    back = sstep(1.8, -1.9, a) * sstep(1.3, 2.4, near)
    side = sstep(8.2, 11., abs(b)) * .9
    rise = max(back, side)
    ridge = 1 - abs(wave(a, 0, b, .85, 2.))
    jag = 1 - abs(wave(a, 0, b, 2.3, 5.))
    h = .13 + .02 * wave(a, 0, b, 5., 1.) + rise * (.3 + 3.1 * sstep(.2, 3.2, near - 1) * (.5 + .5 * ridge) + .28 * jag * rise)
    return h, rise

STRATA = [(.3, 0x17151C), (.75, 0x25222C), (1.15, 0x1A171F), (1.6, 0x2C2732), (2.05, 0x1D1920), (2.5, 0x332D35), (3.0, 0x201B22), (3.6, 0x3A3439), (9., 0x2A252C)]
def ground_colour(a, b, h, rise):
    layer = h + .12 * sin(b * .55 + 1.) + .05 * sin(b * 1.7 + a)
    c = C(STRATA[-1][1])
    for top, col in STRATA:
        if layer < top:
            c = C(col)
            break
    c = mix(c, (0., 0., 0.), .35 * sstep(.2, .9, abs(wave(a, h * 2, b, 2.6, 4.))))
    gl = 1 - sstep(.0, .035, abs(wave(a, h, b, 1.25, 7.)))
    c = mix(c, C(0xB2752A), gl * sstep(.35, .7, rise) * .8)
    t = 1 - sstep(.0, .022, abs(wave(a + 3, h, b, 1.9, 2.)))
    return mix(c, C(0x3FA8B8), t * sstep(.5, .9, rise) * .55)

# Braziers around the map, and the warm light they throw on the rock.
BRAZIERS = [(-4.0, 0.0), (-2.3, 2.6), (-2.2, -3.2), (0.2, -5.0), (0.7, 4.7), (4.4, -1.8), (4.2, 2.8), (4.0, -4.9)]
def warmth(a, b):
    return max(sstep(1.25, .1, sqrt((a - p) ** 2 + (b - q) ** 2)) for p, q in BRAZIERS)

def sheet(name, nu, nv, a0, a1):
    def fn(u, v):
        b = -14.5 + 29 * u
        a = a0 + (min(a1, front(b)) - a0) * v
        h, rise = ground_height(a, b)
        d = river_dist(a, b)
        h -= .07 * sstep(.5, .1, d)
        c = mix(ground_colour(a, b, h, rise), C(0x4A170A), sstep(.55, .12, d))
        c = mix(c, C(0xC8782E), .75 * warmth(a, b) ** 1.6)
        x, z = world(a, b)
        return x, h, z, c
    grid(name, nu, nv, fn, (0, 1, 0), stand=BARE)

def ground():
    sheet("wall", 96, 58, -9.5, -2.2)
    sheet("ground", 86, 50, -2.3, 9.)

def rivers():
    for k, pts in enumerate(RIVERS):
        def fn(u, v, pts=pts):
            n = len(pts) - 1
            t = min(u * n, n - 1e-6)
            i = int(t)
            f = t - i
            a = pts[i][0] + (pts[i + 1][0] - pts[i][0]) * f + .06 * sin(u * 31 + k)
            b = pts[i][1] + (pts[i + 1][1] - pts[i][1]) * f + .06 * cos(u * 23 + k)
            da, db = pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1]
            m = sqrt(da * da + db * db)
            w = (.15 + .05 * sin(u * 17 + k)) * (2 * v - 1)
            a2, b2 = a + w * db / m, b - w * da / m
            h = ground_height(a2, b2)[0] - .02
            x, z = world(a2, b2)
            hot = 1 - abs(2 * v - 1)
            return x, h, z, mix(LAVA, FLAME, hot * hot)
        grid(f"river_{k}", 110, 2, fn, (0, 1, 0), (0, 0, .55), BARE)
        # It falls over the edge, down the painted face, into the magma.
        bf = pts[-1][1]
        def fall(u, v, bf=bf):
            b = bf + (.17 + .05 * sin(u * 9)) * (2 * v - 1) + .07 * sin(u * 7 + k)
            a = front(b) - .1 + (BAND + .1) * u
            x, z = world(a, b)
            hot = 1 - abs(2 * v - 1)
            return x, slope(u) + .03, z, mix(LAVA, FLAME, hot * hot)
        grid(f"fall_{k}", 26, 2, fall, (0, 1, 0), (0, 0, .55), BARE)

def slope(v): return .11 * (1 - v) ** 1.5 + .004

def cut_face():
    """The mountain cut open: bands of rock, veins of ore, and the magma's light rising from below. Here
    `depth` runs from 0 at the map's edge to 1 where the magma starts."""
    def fn(u, v):
        b = -14.5 + 29 * u
        layer = v + .035 * sin(b * .55 + 1.) + .018 * sin(b * 1.7) + .012 * wave(b, v * 8, 0, 3.1, 2.)
        bands = [(.1, 0x3A3644), (.2, 0x211E28), (.3, 0x423B40), (.4, 0x191620), (.52, 0x332A2E), (.64, 0x1A1419), (.76, 0x2A1E1C), (.88, 0x180F10), (9., 0x180F10)]
        c = C(bands[-1][1])
        for top, col in bands:
            if layer < top:
                c = C(col)
                break
        c = mix(c, (0., 0., 0.), .35 * sstep(.2, .9, abs(wave(b, v * 8, 0, 5., 4.))))
        g = 1 - sstep(.0, .05, abs(wave(b, v * 7, 0, 1.25, 1.)))
        c = mix(c, C(0xE8A23A), g * .85)
        t = 1 - sstep(.0, .035, abs(wave(b * .9, v * 9, 0, 2.2, 8.)))
        c = mix(c, C(0x42C8D8), t * .6 * sstep(.25, .45, v))
        c = mix(c, C(0xA82E0A), sstep(.5, 1., v) ** 2 * .85)
        c = mix(c, C(0xFF7A1A), sstep(.8, 1., v) ** 3)
        a = front(b) - .1 + BAND * v
        x, z = world(a, b)
        y = slope(v) + .012 * wave(b, v * 9, 0, 6., 3.) * (1 - v)
        return x, max(y, .003), z, c
    grid("cut_face", 110, 54, fn, (0, 1, 0), stand=BARE)
    def pool(u, v):
        b = -14.5 + 29 * u
        a = front(b) - .1 + BAND + 8 * v - .05
        x, z = world(a, b)
        hot = sstep(-.4, .5, wave(a, 0, b, 1.5, 1.)) * sstep(.45, .8, abs(wave(a, 0, b, 3.3, 4.)))
        return x, .006, z, mix(LAVA, FLAME, hot)
    grid("magma", 60, 12, pool, (0, 1, 0), (0, 0, .4), BARE)

# Halls cut into the mountain's back wall, all lit. They stand only where the wall faces the viewer and
# nothing nearer hides them, spaced out, in a fixed order.
def niche_places():
    screen = lambda a, b, h: h * .82 - a * .57
    found = []
    for i in range(240):
        b = -11 + 22 * ((i * .618034) % 1)
        a = -2.4 - 4.6 * ((i * .381966) % 1)
        h = ground_height(a, b)[0]
        v = screen(a, b, h)
        if not 2.4 < v < 4.7 or h < .9: continue
        # Toward the viewer, the wall must fall away, or something nearer stands in front.
        if any(screen(a + t * .25, b, ground_height(a + t * .25, b)[0]) > v - .12 * t for t in range(1, 14)): continue
        if any((b - q) ** 2 + (v - w) ** 2 < 2.2 ** 2 for q, w, _, _ in found): continue
        found.append((b, v, a, h))
    return [(a, b, h) for b, v, a, h in found][:9]

def niche_table():
    rows = []
    for i, (a, b, h) in enumerate(niche_places()):
        x, z = world(a, b)
        rows.append(f"({x:.3f}, {h - .06:.3f}, {z:.3f}, {1.1 + .5 * ((i * .618) % 1):.2f})")
    return "[" + ", ".join(rows) + "]"

def brazier_table():
    return "[" + ", ".join(f"({world(a, b)[0]:.3f}, {world(a, b)[1]:.3f})" for a, b in BRAZIERS) + "]"

def niche():
    frame = union(block(0, .17, -.02, .2, .19, .03, C(0x8A8478), .01), block(0, .375, .0, .24, .03, .05, C(0xB0A998), .01))
    inner = paint(block(0, .13, .01, .125, .135, .03, C(0xFFB04A), .012), lambda x, y, z, c: mix(FLAME, FLAME2, sstep(.05, .24, y)))
    mesh("niche", faced(union(frame, inner)), (.3, .44), .036, stand=BARE)

def rift():
    def bowl(x, y, z):
        r = sqrt(x * x + z * z)
        h = .3 * sstep(.86, .46, r) * sstep(.14, .4, r) + .02 + .03 * wave(x, 0, z, 9., 1.) - .3 * sstep(.8, .92, r)
        return y - h, mix(C(0x1E1820), C(0x4E2A1E), sstep(.05, .28, y))
    mesh("rift_rim", bowl, (.92, .4), .07, stand=".cylinder 0.7 0.2", floor=-.02)
    def core(x, y, z):
        r = sqrt(x * x + z * z)
        return max(r - .4, y - .12, .07 - y), mix(FLAME, LAVA, sstep(.08, .38, r + .1 * wave(x, 0, z, 12.)))
    mesh("rift_core", core, (.45, .16), .04, (0, 0, .75), ".cylinder 0.4 0.1", floor=.0)
    def shard(x, y, z):
        w = .04 * (1 - y / .3)
        return max(abs(x) + abs(z) - w, y - .3, -y) * .7, mix(LAVA, FLAME, sstep(.04, .28, y))
    mesh("shard", shard, (.06, .32), .03, (.05, 0, .55), ".cone 0.03 0.25", floor=-.004)

def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/strike-the-earth/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.StrikeTheEarth.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\n")
        out.write("/-- Where the lit halls stand on the back wall: x, y, z and size. -/\ndef niches : List (Float × Float × Float × Float) :=\n  " + niche_table() + "\n\n/-- Where the braziers stand: x and z. -/\ndef braziers : List (Float × Float) :=\n  " + brazier_table() + "\n\nend Charter.Games.StrikeTheEarth.Meshes\n")

if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    pieces(); tiles(); bits(); monuments(); ground(); rivers(); cut_face(); niche(); rift()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
