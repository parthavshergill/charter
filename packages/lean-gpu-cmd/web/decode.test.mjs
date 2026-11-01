// Node test for the JS decoder: `node web/decode.test.mjs` (run `lake test` first).
import { readFileSync } from 'node:fs';
import assert from 'node:assert/strict';
import { decodeStream } from './player.js';

const here = new URL('..', import.meta.url);
const load = (p) => new Uint8Array(readFileSync(new URL(p, here)));

const g = decodeStream(load('Tests/golden.gpc'));
assert.equal(g.length, 13);
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

for (const f of ['examples/barchart-a.gpc', 'examples/barchart-b.gpc']) {
  const cs = decodeStream(load(f));
  assert.equal(cs.length, 63);
  assert.equal(cs.filter((c) => c.op === 'draw').length, 37);
}
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x32])), /magic/);
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x31, 1, 0])), /truncated/);
assert.throws(() => decodeStream(new Uint8Array([0x47, 0x50, 0x43, 0x31, 99])), /opcode/);
console.log('decode.test.mjs: ok');
