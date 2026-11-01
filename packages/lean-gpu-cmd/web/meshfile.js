// Mesh files: reads the small binary that `defineMeshFile` names, and refuses anything else.
// Format: see ../WIRE.md. It has numbers only, so the worst a bad file can do is be refused.

/** The most triangles one file may hold. */
export const MAX_MESH_TRIANGLES = 12000;
const MAX_VERTICES = 65535, HEADER = 36;
/** The largest file that can pass, so a download can be refused before it is read. */
export const MAX_MESH_BYTES = HEADER + 9 * MAX_VERTICES + 6 * MAX_MESH_TRIANGLES;

const LINEAR = Float32Array.from({ length: 256 }, (_, i) => {
  const c = i / 255;
  return c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4;
});

/** Read a mesh file into arrays for a geometry. Throws on anything malformed. */
export function decodeMeshFile(buf) {
  const b = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
  if (b.length < HEADER) throw new Error('mesh: too short');
  if (b.length > MAX_MESH_BYTES) throw new Error('mesh: too large');
  if (b[0] !== 0x47 || b[1] !== 0x50 || b[2] !== 0x4d || b[3] !== 0x31) throw new Error('mesh: bad magic');
  const dv = new DataView(b.buffer, b.byteOffset, b.byteLength);
  const vertices = dv.getUint32(4, true), triangles = dv.getUint32(8, true);
  if (vertices > MAX_VERTICES || triangles > MAX_MESH_TRIANGLES) throw new Error('mesh: too many vertices or triangles');
  if (b.length !== HEADER + 9 * vertices + 6 * triangles) throw new Error('mesh: wrong length');
  const lo = [0, 1, 2].map((i) => dv.getFloat32(12 + 4 * i, true));
  const hi = [0, 1, 2].map((i) => dv.getFloat32(24 + 4 * i, true));
  for (let i = 0; i < 3; i++) {
    if (!Number.isFinite(lo[i]) || !Number.isFinite(hi[i]) || lo[i] > hi[i]) throw new Error('mesh: bad bounds');
  }
  const positions = new Float32Array(3 * vertices), colors = new Float32Array(3 * vertices), index = new Uint16Array(3 * triangles);
  let o = HEADER;
  for (let i = 0; i < 3 * vertices; i++, o += 2) {
    const a = i % 3;
    positions[i] = lo[a] + (hi[a] - lo[a]) * dv.getUint16(o, true) / 65535;
  }
  for (let i = 0; i < 3 * vertices; i++, o++) colors[i] = LINEAR[b[o]];
  for (let i = 0; i < 3 * triangles; i++, o += 2) {
    const v = dv.getUint16(o, true);
    if (v >= vertices) throw new Error('mesh: index past the last vertex');
    index[i] = v;
  }
  return { vertices, triangles, positions, colors, index };
}

/** Fetch a mesh file by hash, check it, and read it. Throws when the file is missing or bad. */
export async function fetchMeshFile(assetBase, sha) {
  if (!/^[0-9a-f]{64}$/.test(sha)) throw new Error('mesh: bad hash');
  const res = await fetch(`${assetBase}/${sha}.mesh`);
  if (!res.ok) throw new Error(`mesh: ${res.status}`);
  if (Number(res.headers.get('content-length') || 0) > MAX_MESH_BYTES) throw new Error('mesh: too large');
  const buf = await res.arrayBuffer();
  // A page on plain http has no crypto.subtle, and then the file's other checks still run.
  if (globalThis.crypto?.subtle) {
    const got = new Uint8Array(await crypto.subtle.digest('SHA-256', buf));
    const hex = Array.from(got, (x) => x.toString(16).padStart(2, '0')).join('');
    if (hex !== sha) throw new Error('mesh: the file does not match its hash');
  }
  return decodeMeshFile(buf);
}
