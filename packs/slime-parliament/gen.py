#!/usr/bin/env python3
"""Makes Slime Parliament's meshes: shapes from signed distances, turned into low triangle meshes by
surface nets. Run it from anywhere. It writes meshes/<sha256>.mesh here and the id table for Lean. It
uses no packages. The same code always makes the same bytes. Format: packages/lean-gpu-cmd/WIRE.md."""
import hashlib, math, os, struct, sys
from math import sin, cos, sqrt, pi

HERE = os.path.dirname(os.path.abspath(__file__))
OUT, LEAN = HERE + "/meshes", HERE + "/../../Charter/Games/SlimeParliament/Meshes.lean"
FACE = (.7071, .7071)  # toward the camera, on the table
RIGHT = (.7071, -.7071)  # the viewer's right, on the table

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
def path(pts, ra, rb, col):
    n = len(pts) - 1
    return union(*[rod(pts[i], pts[i + 1], ra + (rb - ra) * i / n, ra + (rb - ra) * (i + 1) / n, col) for i in range(n)])
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
def mesh(name, shape, size, cell, motion=(0, 0, 0), stand=None, floor=-.09, lo=None, hi=None):
    """One mesh file. `size` is half the width and the height of the box it fits in."""
    lo = lo or (-size[0], floor - cell, -size[0])
    hi = hi or (size[0], size[1], size[0])
    verts, tris = nets(shape, lo, hi, cell, floor)
    cols = [shape(*v)[1] for v in verts]
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

# ---- the slime: a white body takes the seat's colour from the draw. Grey in it is shade.
WHITE, CREAM, INK = (1., 1., 1.), C(0xF4EEDC), C(0x201512)
BARE = ".sphere 0.001"  # a part that is only detail has no stand-in worth seeing

def veined(s):
    return paint(s, lambda x, y, z, c: mix(c, (.6, .6, .6), sstep(.55, .85, abs(wave(x, y, z, 26.)))) if y > 0 else mix(c, (.55, .55, .55), .6))
def eyes(h, spread, out, r, look=0.):
    fx, fz, rx, rz = *FACE, *RIGHT
    parts = []
    for s in (-1, 1):
        ex, ez = fx * out + rx * s * spread, fz * out + rz * s * spread
        parts.append(ball(ex, h, ez, r, CREAM))
        l = -s * look
        parts.append(ball(ex + fx * r * .72 + rx * l * r, h + r * .1, ez + fz * r * .72 + rz * l * r, r * .5, INK))
    return union(*parts)

def backbencher():
    body = blend(.07, egg(0, .085, 0, .165, .135, .165, WHITE), egg(0, -.02, 0, .22, .09, .22, (.82, .82, .82)),
                 ball(.1, .03, -.13, .06, WHITE), ball(-.14, .03, .07, .055, WHITE))
    mesh("node_body", veined(rough(body, .008, 19.)), (.3, .26), .046, (.09, 0, .12), ".sphere 0.15")
    mesh("node_eyes", eyes(.15, .062, .115, .044, .3), (.26, .24), .021, (.09, 0, 0), BARE, floor=.05)

def speaker_of_the_house():
    lobes = [ball(.21 * cos(a), .1, .21 * sin(a), .12, WHITE) for a in (.5, 1.9, 3.3, 4.6, 5.7)]
    body = blend(.09, egg(0, .17, 0, .25, .22, .25, WHITE), egg(0, -.02, 0, .35, .1, .35, (.8, .8, .8)), *lobes)
    mesh("swell_body", veined(rough(body, .012, 15.)), (.46, .46), .055, (.07, 0, .14), ".sphere 0.26")
    rx, rz = RIGHT
    cap = egg(-.03, .35, -.03, .19, .1, .19, WHITE)
    lappets = [rod((s * .2 * rx - .02, .34, s * .2 * rz - .02), (s * .25 * rx, .1, s * .25 * rz), .055, .07, WHITE) for s in (-1, 1)]
    rolled = lambda x, y, z, c: mix(C(0xFBF6E6), C(0xA89C82), sstep(.2, .8, sin(y * 62)) * sstep(.43, .36, y))
    mesh("swell_wig", paint(blend(.03, cap, *lappets), rolled), (.36, .48), .03, (.07, 0, 0), BARE, floor=.03)
    mesh("swell_eyes", eyes(.235, .085, .2, .052, .3), (.34, .34), .019, (.07, 0, 0), BARE, floor=.12)

def puffball():
    mesh("puff_body", veined(blend(.05, egg(0, -.01, 0, .1, .06, .1, (.8, .8, .8)), rod((0, 0, 0), (0, .09, 0), .06, .05, WHITE))), (.16, .14), .03, (0, .02, 0), ".cylinder 0.08 0.1")
    head = carve(.012, rough(egg(0, .14, 0, .085, .08, .085, CREAM), .005, 42.), ball(0, .235, 0, .022, C(0x4A3B2E)))
    speck = paint(head, lambda x, y, z, c: mix(c, C(0xB9A98A), sstep(.3, .7, wave(x, y, z, 60.))))
    mesh("puff_head", speck, (.12, .25), .018, (0, .02, 0), ".sphere 0.08", floor=.04)

def tendril():
    pts = [(-.56, .012, .0), (-.38, .03, .05), (-.16, .018, -.045), (.06, .034, .04), (.3, .02, -.055), (.56, .012, 0)]
    stubs = [path([(-.2, .02, -.02), (-.25, .018, -.11), (-.33, .01, -.15)], .025, .008, WHITE),
             path([(.2, .022, 0), (.24, .018, .11), (.31, .01, .14)], .025, .008, WHITE),
             path([(.4, .02, -.02), (.44, .014, -.1)], .02, .008, WHITE)]
    ridge = rod((-.56, -.05, 0), (.56, -.05, 0), .075, .075, (.7, .7, .7))
    knots = [ball(-.38, .03, .05, .07, WHITE), ball(.06, .034, .04, .066, WHITE), ball(.3, .02, -.055, .06, WHITE)]
    vein = blend(.03, path(pts, .042, .042, WHITE), *knots, *stubs, ridge)
    mesh("tendril", paint(vein, lambda x, y, z, c: mix(c, (.68, .68, .68), sstep(.4, .9, abs(wave(x * .6, y, z * 2, 22.))))),
         (.62, .1), .048, (.09, 0, .12), ".box 0.9 0.05 0.1", lo=(-.62, -.1, -.2), hi=(.62, .1, .2))

# ---- the log's skin: each resource's tile is a low patch with a wobbly edge. The middle stays flat.
def patch(surface, colour, seed, edge=.95, wob=.075):
    def hexd(x, z):
        ax, az = abs(x), abs(z)
        return max(ax, ax * .5 + az * .866) - .866 * edge
    def f(x, y, z):
        r = sqrt(x * x + z * z)
        h = .15 + surface(x, z) * sstep(.26, .42, r)
        side = hexd(x, z) + wob * wave(x, 0, z, 4.3, seed)
        a, b, k = y - h, side, .06  # the larger of the two, with the corner rounded off
        t = max(0., min(1., .5 + .5 * (b - a) / k))
        return a + (b - a) * t + k * t * (1 - t), colour(x, y, z, r)
    return f
def tile(name, surface, colour, seed, rgb):
    mesh(name, patch(surface, colour, seed), (1.02, .24), .096, stand=".hexPrism 0.96 0.15", floor=-.1)

def tiles():
    moss, dark = C(0x6E8C3A), C(0x3F5C2A)
    tile("tile_oats", lambda x, z: .012 + .018 * wave(x, 0, z, 9.),
         lambda x, y, z, r: mix(mix(dark, moss, sstep(-.2, .35, wave(x, y, z, 7., 1.))), C(0xC8B575), .55 * sstep(.3, .7, wave(x, 0, z, 11., 3.))), 1., 0)
    tile("tile_dew", lambda x, z: .004 + .022 * wave(x, 0, z, 6., 2.),
         lambda x, y, z, r: mix(C(0x1F4F58), C(0x3C8C93), sstep(-.3, .6, wave(x, y, z, 9., 2.))), 2., 0)
    tile("tile_rot", lambda x, z: .01 + .035 * wave(x, 0, z, 13., 4.),
         lambda x, y, z, r: mix(mix(C(0x2C1A20), C(0x5A2F36), sstep(-.3, .4, wave(x, y, z, 12., 5.))), C(0x8A5A4A), .5 * sstep(.45, .8, wave(x, y, z, 21., 7.))), 3., 0)
    def lichen(x, y, z, r):
        rings = abs(sin(9 * sqrt((x - .3) ** 2 + (z + .25) ** 2))) * abs(sin(8 * sqrt((x + .4) ** 2 + (z - .3) ** 2)))
        return mix(C(0x9C5A1C), C(0xE29A2E), sstep(.1, .6, rings))
    tile("tile_spores", lambda x, z: .006 + .02 * wave(x, 0, z, 8., 6.), lichen, 4., 0)
    wood = lambda x, y, z, r: mix(C(0x8D6A42), C(0xC6A06A), sstep(-.25, .25, sin(r * 34 + 1.2 * wave(x, 0, z, 3.))))
    tile("tile_chamber", lambda x, z: 0., wood, 5., 0)

def bits():
    mesh("oat", paint(carve(.008, egg(0, .012, 0, .085, .016, .055, C(0xE7D79C)), egg(0, .034, 0, .09, .012, .01, C(0xB39B5E))),
                      lambda x, y, z, c: mix(c, C(0xFFF4C8), .4 * sstep(0, .03, x))), (.1, .04), .02, stand=".cylinder 0.07 0.03", floor=-.004)
    mesh("drop", egg(0, .018, 0, .06, .055, .06, C(0xA9E3EE)), (.08, .08), .024, (.035, 0, .12), ".sphere 0.05", floor=-.002)
    mesh("toadstool", union(rod((0, 0, 0), (0, .11, 0), .018, .013, C(0xC9BBA6)),
                            paint(egg(0, .12, 0, .062, .036, .062, C(0x7C5A87)), lambda x, y, z, c: mix(c, C(0xE9DCF0), sstep(.5, .9, wave(x, y, z, 70.))))),
         (.09, .17), .021, (0, .025, 0), ".cone 0.06 0.15", floor=-.004)
    mesh("sporeling", blend(.012, rod((0, 0, 0), (.012, .1, 0), .012, .01, C(0xD8C39B)), egg(.012, .135, 0, .042, .052, .042, C(0xF08A24))),
         (.08, .2), .017, (0, .035, .12), ".cone 0.05 0.18", floor=-.004)
    mesh("leaf", paint(egg(0, .012, 0, .24, .02, .11, C(0x6A4A22)), lambda x, y, z, c: mix(c, C(0x9A6A2C), sstep(0, .6, wave(x, 0, z, 18.)))), (.26, .05), .03, stand=".cylinder 0.15 0.02", floor=-.004)

def fruit(name, shape, h=.36, cell=.019, motion=(.0, .03, .1)):
    foot = egg(0, -.005, 0, .085, .03, .085, C(0x6C5A3E))
    mesh(name, blend(.012, foot, shape), (.2, h), cell, motion, ".cone 0.08 0.3", floor=-.004)

def fruiting_bodies():
    stalk = C(0xD9CDB4)
    fruit("fb_cost", union(rod((0, 0, 0), (0, .2, 0), .016, .012, stalk), rod((-.09, .215, 0), (.09, .215, 0), .015, .015, stalk),
                           rod((-.09, .22, 0), (-.09, .15, 0), .012, .012, stalk), rod((.09, .22, 0), (.09, .15, 0), .012, .012, stalk),
                           egg(-.09, .14, 0, .042, .03, .042, C(0xE0267F)), egg(.09, .14, 0, .042, .03, .042, C(0xE0267F))))
    fruit("fb_points", blend(.015, rod((0, 0, 0), (0, .25, 0), .017, .012, stalk), ball(0, .27, 0, .05, C(0xF4C21E))))
    fruit("fb_bank", union(rod((0, 0, 0), (0, .17, 0), .013, .011, stalk), *[egg(0, .05 + .045 * i, 0, .068 - i * .009, .016, .068 - i * .009, mix(C(0x2B9E9A), C(0x9FE3C8), i / 3)) for i in range(4)]))
    fruit("fb_harvest", paint(carve(.02, blend(.02, rod((0, 0, 0), (0, .1, 0), .02, .02, stalk), egg(0, .16, 0, .085, .07, .085, C(0xE8862A))), egg(0, .2, 0, .068, .06, .068, C(0xFFD27A))),
                              lambda x, y, z, c: mix(c, C(0xFFE9B0), .7 * sstep(.14, .19, y) * sstep(.08, .05, sqrt(x * x + z * z)))))
    speckled = lambda x, y, z, c: mix(c, C(0x6B2FA0), sstep(.45, .7, wave(x, y, z, 60.)))
    fruit("fb_roll", blend(.012, rod((0, 0, 0), (0, .1, 0), .02, .018, stalk),
                           paint(egg(0, .115, 0, .062, .05, .062, C(0xEFE6FA)), speckled), paint(egg(.012, .205, .01, .05, .045, .05, C(0xEFE6FA)), speckled)))
    fruit("fb_build", blend(.012, path([(-.07, 0, 0), (-.07, .13, 0), (-.04, .205, 0), (.04, .205, 0), (.07, .13, 0), (.07, 0, 0)], .018, .018, stalk), ball(0, .235, 0, .03, C(0x7FCB46))))
    morel = paint(rough(egg(0, .17, 0, .062, .092, .062, C(0x8C5A2E)), .009, 38.), lambda x, y, z, c: mix(c, C(0xD2A76A), sstep(0, .6, wave(x, y, z, 38.))))
    fruit("fb_round", blend(.012, rod((0, 0, 0), (0, .11, 0), .024, .022, stalk), morel))
    fruit("fb_piece", blend(.015, rod((-.05, 0, 0), (-.06, .13, 0), .012, .01, stalk), rod((.05, 0, 0), (.065, .09, 0), .012, .01, stalk), rod((0, 0, -.03), (0, .2, -.03), .012, .01, stalk),
                            ball(-.06, .15, 0, .036, C(0xF3EAD2)), ball(.065, .11, 0, .03, C(0xF3EAD2)), ball(0, .23, -.03, .042, C(0xF3EAD2))))
    fruit("fb_repeal", union(path([(0, 0, 0), (0, .1, 0), (.03, .16, 0), (.09, .17, 0), (.125, .13, 0)], .02, .014, C(0xB8AE9A)), egg(.135, .1, 0, .04, .034, .04, C(0x7C7468))), motion=(0, .012, 0))
    fx, fz = FACE
    mesh("speaker", union(blend(.03, egg(0, 0, 0, .3, .06, .3, C(0x6C5A3E)), rod((0, 0, 0), (0, .3, 0), .06, .045, stalk)),
                          paint(blend(.02, *[ball(.11 * cos(i * 1.05), .36 + .03 * (i % 2), .11 * sin(i * 1.05), .06, C(0xF2ECD8)) for i in range(6)], ball(0, .42, 0, .07, C(0xF2ECD8))), lambda x, y, z, c: c),
                          eyes(.33, .05, .085, .03, .35)), (.36, .54), .026, (0, .012, .05), ".cone 0.2 0.5", floor=-.004)

def law_made():
    def tall(x, y, z): return mix((.72, .72, .72), WHITE, sstep(0, .18, y))
    mesh("made_a", paint(blend(.02, rod((0, -.02, 0), (0, .17, 0), .05, .03, WHITE), ball(0, .21, 0, .07, WHITE)), lambda x, y, z, c: tall(x, y, z)), (.14, .3), .026, (.03, 0, .2))
    mesh("made_b", paint(carve(.02, blend(.03, rod((0, -.02, 0), (0, .08, 0), .05, .05, WHITE), egg(0, .14, 0, .12, .07, .12, WHITE)), egg(0, .2, 0, .09, .05, .09, (.6, .6, .6))), lambda x, y, z, c: c), (.18, .24), .026, (.03, 0, .2))
    mesh("made_c", paint(blend(.03, ball(-.07, .06, .02, .075, WHITE), ball(.07, .05, -.03, .065, WHITE), ball(0, .15, 0, .08, WHITE)), lambda x, y, z, c: tall(x, y, z)), (.18, .26), .026, (.03, 0, .2))

# ---- the world: a fallen log on the forest floor, and a stump for the treasury.
def log():
    L, W = 6.6, 3.15
    bark, ridge, mossy = C(0x3B2A1C), C(0x5E452D), C(0x4F6B2C)
    def f(x, y, z):
        ends = max(abs(x) - L - .25 * sin(z * 1.7 + 1.), 0.)
        across = sqrt(max(abs(z) - W + .5 - .22 * sin(x * .85 + (z > 0)) - .09 * sin(x * 2.9), 0.) ** 2 + ends * ends)
        groove = sin(z * 13 + 1.6 * sin(x * .9) + .9 * sin(x * 2.3 + z)) * .022 + wave(x, 0, z, 4.) * .012
        h = .17 + groove - 1.1 * across * across * (1 if across < .9 else 1.3)
        c = mix(bark, ridge, sstep(-.4, .8, sin(z * 13 + 1.6 * sin(x * .9) + .9 * sin(x * 2.3 + z))))
        c = mix(c, mossy, sstep(.15, .6, wave(x, 0, z, 1.4, 2.)) * .85)
        return y - h, c
    mesh("log", f, None, .17, stand=".box 13 0.16 6.4", floor=.004, lo=(-L - .8, -.02, -W - .4), hi=(L + .8, .25, W + .4))

def stump():
    wood = lambda x, y, z, c: mix(C(0x9A7446), C(0xD4AE76), sstep(-.2, .3, sin(sqrt(x * x + z * z) * 46))) if y > .29 else mix(C(0x3A2818), C(0x5C4228), sstep(-.3, .5, sin(atan(x, z) * 16 + y * 6)))
    atan = math.atan2
    body = blend(.05, rod((0, 0, 0), (0, .28, 0), .3, .25, WHITE), *[rod((.3 * cos(a), 0, .3 * sin(a)), (.46 * cos(a), 0, .46 * sin(a)), .1, .04, WHITE) for a in (.4, 1.6, 2.9, 4.1, 5.4)])
    mesh("stump", paint(carve(.03, body, ball(0, .58, 0, .24, WHITE)), wood), (.56, .36), .05, stand=".cylinder 0.3 0.33", floor=-.004)

def write_table():
    ident = lambda s: "".join(w if i == 0 else w.capitalize() for i, w in enumerate(s.split("_")))
    with open(LEAN, "w") as out:
        out.write("import GpuCmd\n\n/-! Written by `packs/slime-parliament/gen.py`. Do not edit it by hand: run the script again. -/\n\n")
        out.write("namespace Charter.Games.SlimeParliament.Meshes\nopen GpuCmd\n\n")
        for i, row in enumerate(TABLE):
            out.write(f"def {ident(row[0])} : UInt32 := {100 + i}\n")
        out.write("\n/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/\ndef defs : List Cmd :=\n  [ ")
        rows = []
        for i, (name, sha, tint, m, stand, _, _) in enumerate(TABLE):
            rows.append(f'.defineMeshFile {100 + i} "{sha}" 0x{tint:06X} {{ pulse := {m[0]}, sway := {m[1]}, glow := {m[2]} }} ({stand})')
        out.write("\n  , ".join(rows) + " ]\n\n/-- How many triangles each mesh has, by id. -/\ndef triangles : List (UInt32 × Nat) :=\n  [ ")
        out.write(", ".join(f"({100 + i}, {r[5]})" for i, r in enumerate(TABLE)) + " ]\n\nend Charter.Games.SlimeParliament.Meshes\n")

if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    os.makedirs(os.path.dirname(LEAN), exist_ok=True)
    for f in os.listdir(OUT): os.remove(f"{OUT}/{f}")
    backbencher(); speaker_of_the_house(); puffball(); tendril(); tiles(); bits(); fruiting_bodies(); law_made(); log(); stump()
    write_table()
    print(f"{len(TABLE)} meshes, {sum(r[5] for r in TABLE)} triangles, {sum(r[6] for r in TABLE)} bytes")
