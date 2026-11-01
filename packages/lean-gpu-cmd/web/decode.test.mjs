// Node test for the JS decoder: `node web/decode.test.mjs` (run `lake test` first).
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';
import { decodeStream } from './player.js';
import { decodeMeshFile, MAX_MESH_TRIANGLES } from './meshfile.js';

const here = new URL('..', import.meta.url);
const load = (p) => new Uint8Array(readFileSync(new URL(p, here)));

const g = decodeStream(load('Tests/golden.gpc'));
assert.equal(g.length, 14);
assert.deepEqual(g[0], { op: 'clear', rgb: 0x112233 });
assert.deepEqual(g[1], { op: 'camera', eye: [1, 2, 3], target: [0, 0, 0], fov: 45 });
assert.deepEqual(g[2], { op: 'light', dir: [-0.5, -1, 0.25], intensity: 1.5 });
assert.deepEqual(g.slice(3, 9).map((c) => [c.id, c.prim, c.args]), [
  [7, 'hexPrism', [1, 0.20000000298023224]], [8, 'box', [1, 2, 3]], [9, 'cylinder', [0.5, 1]],
  [10, 'cone', [0.5, 1]], [11, 'sphere', [0.30000001192092896]], [12, 'house', [1, 1, 1]]]);
assert.deepEqual(g[9], { op: 'draw', mesh: 7, pos: [1.5, 0, -2], rotY: 0.5, scale: [1, 2, 1], rgb: 0x80ff0000, pick: 42 });
assert.equal(g[10].text, 'Grüße · 6 ⚑');
assert.equal(g[11].text, 'x'.repeat(300));
assert.deepEqual(g[12], { op: 'highlight', pick: 42, rgb: 0xffd700 });
assert.deepEqual(g[13], { op: 'meshFile', id: 20, sha: 'ab', tint: 0x445566, motion: { pulse: 0.5, sway: 0.25, glow: 1 }, prim: 'sphere', args: [0.5] });

for (const f of ['examples/barchart-a.gpc', 'examples/barchart-b.gpc']) {
  const cs = decodeStream(load(f));
  assert.equal(cs.length, 63);
  assert.equal(cs.filter((c) => c.op === 'draw').length, 37);
}
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x32])), /magic/);
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x31, 1, 0])), /truncated/);
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x31, 99])), /opcode/);

// A mesh file: 1 triangle, numbers only. Anything else is refused.
const meshFile = (v = 3, t = 1, extra = 0, tri = [0, 1, 2]) => {
  const b = new Uint8Array(36 + 9 * v + 6 * t + extra), dv = new DataView(b.buffer);
  b.set([0x47, 0x50, 0x4d, 0x31]); dv.setUint32(4, v, true); dv.setUint32(8, t, true);
  dv.setFloat32(24, 1, true); dv.setFloat32(28, 1, true); dv.setFloat32(32, 1, true);
  dv.setUint16(36, 65535, true); dv.setUint8(36 + 6 * v, 200);
  for (let i = 0; i < 3 * t; i++) dv.setUint16(36 + 9 * v + 2 * i, tri[i] ?? 0, true);
  return b;
};
const m = decodeMeshFile(meshFile());
assert.equal(m.vertices, 3); assert.equal(m.triangles, 1);
assert.deepEqual([...m.positions.slice(0, 3)], [1, 0, 0]);
assert.ok(m.colors[0] > 0.5 && m.colors[0] < 0.6 && m.colors[1] === 0);
assert.deepEqual([...m.index], [0, 1, 2]);
assert.throws(() => decodeMeshFile(new Uint8Array(10)), /short/);
assert.throws(() => decodeMeshFile(new TextEncoder().encode('<svg onload=alert(1)>'.repeat(4))), /magic/);
assert.throws(() => decodeMeshFile(meshFile(3, 1, 1)), /length/);
assert.throws(() => decodeMeshFile(meshFile(3, 1, 0, [0, 1, 3])), /index/);
const many = meshFile(); new DataView(many.buffer).setUint32(8, MAX_MESH_TRIANGLES + 1, true);
assert.throws(() => decodeMeshFile(many), /many/);
const nan = meshFile(); new DataView(nan.buffer).setFloat32(12, NaN, true);
assert.throws(() => decodeMeshFile(nan), /bounds/);
console.log('decode.test.mjs: ok');
