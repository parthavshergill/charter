// lean-gpu-cmd player: renders a GPC1 command stream with three.js (vendored).
// API: const p = new GpuPlayer(canvas, opts); p.render(arrayBuffer); p.onPick = (id) => {};
// Wire format: see ../WIRE.md.
import * as THREE from './vendor/three.module.min.js';
import { fetchMeshFile } from './meshfile.js';

// ---------------------------------------------------------------- decoding

const MAGIC = [0x47, 0x50, 0x43, 0x31]; // "GPC1"
const PRIMS = [null, 'hexPrism', 'box', 'cylinder', 'cone', 'sphere', 'house', 'gable', 'pyramid'];
const PRIM_ARGS = [0, 2, 3, 2, 2, 1, 3, 3, 2];

/** Decode a GPC1 stream into plain command objects. Throws on malformed input. */
export function decodeStream(buf) {
  const bytes = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let o = 0;
  const need = (n) => { if (o + n > bytes.length) throw new Error(`gpc: truncated at ${o}`); };
  const u8 = () => { need(1); return bytes[o++]; };
  const u32 = () => { need(4); const v = dv.getUint32(o, true); o += 4; return v; };
  const f32 = () => { need(4); const v = dv.getFloat32(o, true); o += 4; return v; };
  const vec3 = () => [f32(), f32(), f32()];
  const str = () => {
    let n = 0, shift = 0, b;
    do { b = u8(); n += (b & 0x7f) * 2 ** shift; shift += 7; } while (b & 0x80);
    need(n);
    const s = new TextDecoder('utf-8', { fatal: true }).decode(bytes.subarray(o, o + n));
    o += n;
    return s;
  };
  const prim = () => {
    const kind = u8();
    if (!PRIMS[kind]) throw new Error(`gpc: bad prim ${kind}`);
    const args = [];
    for (let k = 0; k < PRIM_ARGS[kind]; k++) args.push(f32());
    return { prim: PRIMS[kind], args };
  };
  for (let i = 0; i < 4; i++) if (bytes[i] !== MAGIC[i]) throw new Error('gpc: bad magic');
  o = 4;
  const cmds = [];
  while (o < bytes.length) {
    const op = u8();
    switch (op) {
      case 1: cmds.push({ op: 'clear', rgb: u32() }); break;
      case 2: cmds.push({ op: 'camera', eye: vec3(), target: vec3(), fov: f32() }); break;
      case 3: cmds.push({ op: 'light', dir: vec3(), intensity: f32() }); break;
      case 4: { const id = u32(); cmds.push({ op: 'mesh', id, ...prim() }); break; }
      case 5: cmds.push({ op: 'draw', mesh: u32(), pos: vec3(), rotY: f32(), scale: vec3(), rgb: u32(), pick: u32() }); break;
      case 6: cmds.push({ op: 'label', text: str(), pos: vec3(), size: f32(), rgb: u32(), pick: u32() }); break;
      case 7: cmds.push({ op: 'highlight', pick: u32(), rgb: u32() }); break;
      case 8: cmds.push({ op: 'meshFile', id: u32(), sha: str(), tint: u32(), motion: { pulse: f32(), sway: f32(), glow: f32() }, ...prim() }); break;
      default: throw new Error(`gpc: bad opcode ${op} at ${o - 1}`);
    }
  }
  return cmds;
}

// ---------------------------------------------------------------- easing

export const ease = {
  outCubic: (t) => 1 - (1 - t) ** 3,
  inOutCubic: (t) => (t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2),
  outBack: (t) => { const c1 = 1.70158, c3 = c1 + 1; return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2; },
};
const clamp01 = (t) => (t <= 0 ? 0 : t >= 1 ? 1 : t);
// Height fraction above the rest position for a drop-in: fall, then one small hop.
function dropCurve(t) {
  if (t < 0.62) { const u = t / 0.62; return 1 - u * u; }
  const u = (t - 0.62) / 0.38;
  return 0.09 * Math.sin(Math.PI * u);
}
// Squash factor around the landing moment (0 = none).
const squash = (t) => (t > 0.55 && t < 0.85 ? Math.sin(Math.PI * (t - 0.55) / 0.3) : 0);

const MOVE_MS = 350, APPEAR_MS = 420, VANISH_MS = 200;
const reduceMotion = () => typeof matchMedia === 'function' && matchMedia('(prefers-reduced-motion: reduce)').matches;

// ---------------------------------------------------------------- quality

// How much the player spends on looks. A lower tier never leaves anything out of the game: pieces, numbers
// and owner colors are the same on all of them. It draws fewer pixels and simpler shadows.
// dpr: the most pixels per CSS pixel. shadow: the shadow map's side, 0 for no shadows. softShadow: blur them.
// wood: the table texture's side. liveShadow: shadows follow things as they move. dropIn: the board's
// scenery falls into place on the first frame. motionMs and pulseMs: the time between frames of things that
// move by themselves and of glowing places. 0 for motionMs means they stand still.
export const TIERS = [
  { dpr: 1, shadow: 0, softShadow: false, wood: 256, anisotropy: 2, liveShadow: false, dropIn: false, motionMs: 0, pulseMs: 66 },
  { dpr: 1.25, shadow: 1024, softShadow: false, wood: 512, anisotropy: 4, liveShadow: false, dropIn: false, motionMs: 0, pulseMs: 50 },
  { dpr: 1.75, shadow: 2048, softShadow: false, wood: 512, anisotropy: 8, liveShadow: false, dropIn: false, motionMs: 50, pulseMs: 33 },
  { dpr: 2, shadow: 4096, softShadow: true, wood: 1024, anisotropy: 16, liveShadow: true, dropIn: true, motionMs: 32, pulseMs: 0 },
];
const TIER_KEY = 'charter.tier';
const PACE_FRAMES = 40;     // how many frames one judgement of the pace takes
const PACE_SLOW_MS = 35;    // slower than about 28 frames a second, step down a tier
const PACE_HOPELESS_MS = 90; // this slow on the lowest tier, say so: the page can use the 2D board
const isTouchDevice = () => typeof matchMedia === 'function' && matchMedia('(pointer: coarse)').matches;
function storedTier() { try { const n = parseInt(localStorage.getItem(TIER_KEY)); return n >= 0 && n < TIERS.length ? n : null; } catch { return null; } }
function storeTier(n) { try { localStorage.setItem(TIER_KEY, String(n)); } catch {} }
/** A touch screen starts one tier down. A tier this device has already fallen to stays fallen. */
function startingTier(asked) {
  if (asked != null) return Math.max(0, Math.min(TIERS.length - 1, asked));
  const top = isTouchDevice() ? TIERS.length - 2 : TIERS.length - 1, seen = storedTier();
  return seen == null ? top : Math.min(top, seen);
}

// ---------------------------------------------------------------- geometry

// Low-poly on purpose: few sides and flat shading, so every shape shows its facets.
function extrudeUp(shape, h, b) {
  const g = new THREE.ExtrudeGeometry(shape, {
    depth: Math.max(h - 2 * b, 1e-4), bevelEnabled: b > 0, bevelThickness: b, bevelSize: b,
    bevelSegments: 1, curveSegments: 6,
  });
  g.rotateX(-Math.PI / 2); // extrusion axis -> +Y, shape y -> -Z
  g.translate(0, b, 0);
  return g;
}

function lathe(r, h, b, cone) {
  const pts = [new THREE.Vector2(0, 0)];
  if (cone) {
    pts.push(new THREE.Vector2(r, 0), new THREE.Vector2(0, h));
    return new THREE.LatheGeometry(pts, 7);
  }
  pts.push(new THREE.Vector2(r, 0), new THREE.Vector2(r, h - b), new THREE.Vector2(r - b, h), new THREE.Vector2(0, h));
  return new THREE.LatheGeometry(pts, 14);
}

function prism(w, h, d) {
  const s = new THREE.Shape();
  s.moveTo(-w / 2, 0); s.lineTo(w / 2, 0); s.lineTo(0, h); s.closePath();
  const g = new THREE.ExtrudeGeometry(s, { depth: d, bevelEnabled: false });
  g.translate(0, 0, -d / 2);
  return g;
}

function buildGeometry(prim, a) {
  const pos = (x) => Math.max(x, 1e-3);
  switch (prim) {
    case 'hexPrism': {
      const r = pos(a[0]), h = pos(a[1]), b = Math.min(0.012 * r, 0.1 * h);
      const R = r - b / Math.cos(Math.PI / 6), s = new THREE.Shape();
      for (let k = 0; k < 6; k++) {
        const t = Math.PI / 2 + (k * Math.PI) / 3;
        k ? s.lineTo(R * Math.cos(t), R * Math.sin(t)) : s.moveTo(R * Math.cos(t), R * Math.sin(t));
      }
      s.closePath();
      return extrudeUp(s, h, b);
    }
    case 'box': {
      const w = pos(a[0]), h = pos(a[1]), d = pos(a[2]), b = Math.min(w, h, d) * 0.02;
      const s = new THREE.Shape();
      s.moveTo(-w / 2 + b, -d / 2 + b); s.lineTo(w / 2 - b, -d / 2 + b); s.lineTo(w / 2 - b, d / 2 - b); s.lineTo(-w / 2 + b, d / 2 - b); s.closePath();
      return extrudeUp(s, h, b);
    }
    case 'cylinder': { const r = pos(a[0]), h = pos(a[1]); return lathe(r, h, Math.min(0.04 * r, 0.1 * h), false); }
    case 'cone': return lathe(pos(a[0]), pos(a[1]), 0, true);
    case 'sphere': { const r = pos(a[0]); const g = new THREE.IcosahedronGeometry(r, 1); g.translate(0, r, 0); return g; }
    case 'house': {
      const w = pos(a[0]), h = pos(a[1]), d = pos(a[2]), b = Math.min(w, h, d) * 0.05;
      const W = w / 2 - b, H = h - 2 * b, s = new THREE.Shape();
      s.moveTo(-W, 0); s.lineTo(W, 0); s.lineTo(W, 0.6 * H); s.lineTo(0, H); s.lineTo(-W, 0.6 * H); s.closePath();
      const g = new THREE.ExtrudeGeometry(s, { depth: Math.max(d - 2 * b, 1e-4), bevelEnabled: true, bevelThickness: b, bevelSize: b, bevelSegments: 1 });
      g.translate(0, b, -(d - 2 * b) / 2);
      return g;
    }
    case 'gable': return prism(pos(a[0]), pos(a[1]), pos(a[2]));
    case 'pyramid': { const g = new THREE.ConeGeometry(pos(a[0]), pos(a[1]), 4, 1); g.translate(0, pos(a[1]) / 2, 0); return g; }
  }
  throw new Error(`gpc: unknown prim ${prim}`);
}

// A mesh file's stand-in has vertex colors too, so that the same material draws it and the file.
function tinted(geo, rgb) {
  const c = new THREE.Color(rgb & 0xffffff), n = geo.attributes.position.count, a = new Float32Array(3 * n);
  for (let i = 0; i < n; i++) { a[3 * i] = c.r; a[3 * i + 1] = c.g; a[3 * i + 2] = c.b; }
  geo.setAttribute('color', new THREE.BufferAttribute(a, 3));
  return geo;
}

function meshFileGeometry(m) {
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(m.positions, 3));
  geo.setAttribute('color', new THREE.BufferAttribute(m.colors, 3));
  geo.setIndex(new THREE.BufferAttribute(m.index, 1));
  geo.computeVertexNormals();
  return geo;
}

// ---------------------------------------------------------------- textures

function rng(seed) { let s = seed >>> 0; return () => ((s = (s * 1664525 + 1013904223) >>> 0) / 4294967296); }

function woodTexture(N, anisotropy) {
  const c = document.createElement('canvas');
  c.width = c.height = N;
  const g = c.getContext('2d'), rnd = rng(7), planks = 6, ph = N / planks;
  g.scale(N / 1024, N / 1024);
  for (let p = 0; p < planks; p++) {
    const y0 = p * 1024 / planks, l = 13 + rnd() * 4;
    g.fillStyle = `hsl(${22 + rnd() * 6}, 38%, ${l}%)`;
    g.fillRect(0, y0, 1024, 1024 / planks);
    for (let i = 0; i < 70; i++) {
      const yy = y0 + rnd() * 1024 / planks, ph1 = rnd() * 6, amp = 1 + rnd() * 4;
      g.strokeStyle = rnd() < 0.5 ? `rgba(20,10,4,${0.08 + rnd() * 0.18})` : `rgba(255,214,160,${0.015 + rnd() * 0.035})`;
      g.lineWidth = 0.6 + rnd() * 2.2;
      g.beginPath();
      for (let x = 0; x <= 1024; x += 16) {
        const y = yy + Math.sin(x * 0.006 + ph1) * amp + Math.sin(x * 0.021 + i) * 0.8;
        x ? g.lineTo(x, y) : g.moveTo(x, y);
      }
      g.stroke();
    }
    g.fillStyle = 'rgba(8,4,2,0.7)';
    g.fillRect(0, y0, 1024, 3);
  }
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  t.wrapS = t.wrapT = THREE.RepeatWrapping;
  t.repeat.set(26, 26);
  t.anisotropy = anisotropy;
  return t;
}

const css = (rgb) => `#${(rgb & 0xffffff).toString(16).padStart(6, '0')}`;
const luminance = (rgb) => (0.3 * ((rgb >> 16) & 255) + 0.59 * ((rgb >> 8) & 255) + 0.11 * (rgb & 255)) / 255;

function labelTexture(text, rgb, glow) {
  const fontPx = 96, pad = 28, c = document.createElement('canvas'), g = c.getContext('2d');
  const font = `700 ${fontPx}px "Iowan Old Style", "Palatino Linotype", Palatino, Georgia, serif`;
  g.font = font;
  const w = Math.ceil(g.measureText(text).width) + pad * 2, h = fontPx + pad * 2;
  c.width = w; c.height = h;
  g.font = font; g.textAlign = 'center'; g.textBaseline = 'middle';
  if (glow != null) { g.shadowColor = css(glow); g.shadowBlur = 26; }
  // Pale text gets a dark edge. Dark text sits on a pale token and needs none.
  if (luminance(rgb) > 0.5) {
    g.lineJoin = 'round'; g.lineWidth = 14; g.strokeStyle = 'rgba(28,18,10,0.85)';
    g.strokeText(text, w / 2, h / 2 + 4);
  }
  g.shadowBlur = 0;
  g.fillStyle = css(rgb);
  g.fillText(text, w / 2, h / 2 + 4);
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  t.anisotropy = 4;
  return { tex: t, aspect: w / h, scale: h / fontPx };
}

// ---------------------------------------------------------------- player

const v3 = (a) => new THREE.Vector3(a[0], a[1], a[2]);
const opacityOf = (rgb) => 1 - ((rgb >>> 24) & 0xff) / 255;
const sameV = (a, b, eps = 1e-4) => Math.abs(a.x - b.x) < eps && Math.abs(a.y - b.y) < eps && Math.abs(a.z - b.z) < eps;
const lerpAngle = (a, b, t) => { let d = (b - a) % (2 * Math.PI); if (d > Math.PI) d -= 2 * Math.PI; if (d < -Math.PI) d += 2 * Math.PI; return a + d * t; };

export class GpuPlayer {
  /** @param {HTMLCanvasElement} canvas @param {{table?: boolean, background?: number, hoverFx?: (id:number)=>boolean, clickable?: (id:number)=>boolean}} opts */
  constructor(canvas, opts = {}) {
    this.canvas = canvas;
    this.onPick = null;   // (pickId) => void
    this.onHover = null;  // (pickId | 0, clientX, clientY) => void
    this.onTier = null;   // (tier) => void, after the quality has changed
    this.onTooSlow = null; // () => void, once, if even the lowest tier cannot keep up
    this._raf = null;
    this._nf = false;
    this.paused = false;
    this._tick = this._tick.bind(this);
    this.tier = startingTier(opts.tier);
    this.q = TIERS[this.tier];
    this.reduced = reduceMotion();
    this.hoverFx = opts.hoverFx || (() => true);
    this.clickable = opts.clickable || (() => true);
    const r = (this.renderer = new THREE.WebGLRenderer({ canvas, antialias: this.tier >= 2, preserveDrawingBuffer: !!opts.preserveDrawingBuffer }));
    r.setPixelRatio(Math.min(window.devicePixelRatio || 1, this.q.dpr));
    r.shadowMap.enabled = this.q.shadow > 0;
    r.shadowMap.type = this.q.softShadow ? THREE.PCFSoftShadowMap : THREE.PCFShadowMap;
    r.shadowMap.autoUpdate = false;
    r.outputColorSpace = THREE.SRGBColorSpace;
    r.toneMapping = THREE.NoToneMapping;

    const scene = (this.scene = new THREE.Scene());
    this.bg = new THREE.Color(opts.background ?? 0x241a12);
    scene.background = this.bg;
    this.camera = new THREE.OrthographicCamera(-8, 8, 6, -6, 0.1, 400);

    // Warm late-afternoon light: a soft sky, a low sun, and a cool fill in the shadows.
    this.hemi = new THREE.HemisphereLight(0xfff3df, 0x6a5a55, 1.5);
    scene.add(this.hemi);
    const sun = (this.sun = new THREE.DirectionalLight(0xffe0b0, 2.2));
    sun.castShadow = this.q.shadow > 0;
    this.maxTex = r.capabilities.maxTextureSize || 2048;
    sun.shadow.mapSize.setScalar(Math.min(this.q.shadow || 1024, this.maxTex));
    sun.shadow.bias = -0.0003;
    sun.shadow.normalBias = 0.006;
    scene.add(sun, sun.target);
    this.sunDir = new THREE.Vector3(-0.6, -1, -0.2).normalize();
    this.sunPower = 1;
    const fill = new THREE.DirectionalLight(0xbcd4ff, 0.38);
    fill.position.set(8, 5, 9);
    scene.add(fill);

    this.table = new THREE.Mesh(
      new THREE.PlaneGeometry(400, 400),
      new THREE.MeshStandardMaterial({ map: woodTexture(this.q.wood, Math.min(this.q.anisotropy, r.capabilities.getMaxAnisotropy())), roughness: 0.82, metalness: 0.0 }),
    );
    this.table.rotation.x = -Math.PI / 2;
    this.table.position.y = -0.003;
    this.table.receiveShadow = true;
    this.table.visible = opts.table !== false;
    scene.add(this.table);

    this.root = new THREE.Group();
    scene.add(this.root);
    this.geoms = new Map();     // mesh id -> {key, geo, colored, motion, sha}
    this.assetBase = opts.assetBase ?? '/assets';
    this.meshFiles = new Map(); // sha -> the file's geometry once loaded, null before then or if it failed
    this.motionAt = 0; this.motionSlow = 0;
    this.items = [];            // live objects
    this.dying = [];            // objects fading out
    this.batches = [];          // scenery that holds still, drawn in one call per shape
    this._batchDirty = false;
    this._batchMats = new Map();
    this._pace = { sum: 0, n: 0 };
    this._drewLast = false;
    this.pulseAt = 0;
    this.maxZoom = isTouchDevice() ? 4 : 3;
    this.gesture = false;       // a finger or the mouse holds the board, so the camera follows at once
    this.highlights = new Map();
    this.hoverId = 0;
    this._hlColor = new THREE.Color();
    this.frames = 0;
    this.lastCameraKey = null;

    // A fixed direction. `zoom` and `pan` are what the viewer can change; `insets` are the pixels
    // the interface covers, so the whole board stays in the free part of the canvas.
    this.view = { target: new THREE.Vector3(), dir: new THREE.Vector3(1, 1, 1).normalize(), radius: 6, elev: 0.6 };
    this.zoom = 1; this.zoomGoal = 1;
    this.pan = new THREE.Vector2(); this.panGoal = new THREE.Vector2();
    this.insets = { l: 0, r: 0, t: 0, b: 0 }; this.insetsGoal = { l: 0, r: 0, t: 0, b: 0 };
    this.raycaster = new THREE.Raycaster();
    this.pointer = new THREE.Vector2(-2, -2);
    this.pointerInside = false;
    this.pointerPx = { x: 0, y: 0 };
    this._bindInput();
    if (typeof ResizeObserver === 'function') new ResizeObserver(() => { this.needsFrame = true; }).observe(canvas);
    // A phone can take the GPU away while the page is in the background. three.js rebuilds what it holds.
    canvas.addEventListener('webglcontextrestored', () => { r.shadowMap.needsUpdate = true; this.needsFrame = true; });

    this._clock = performance.now();
    this.needsFrame = true;
  }

  // Nothing runs while nothing moves: asking for a frame is what starts the loop, and the loop stops itself.
  get needsFrame() { return this._nf; }
  set needsFrame(v) { this._nf = v; if (v) this._wake(); }
  _wake() { if (this._raf == null && !this.paused) this._raf = requestAnimationFrame(this._tick); }

  /** Stop all work while the page shows the 2D board. */
  setPaused(paused) { this.paused = paused; if (paused) { if (this._raf != null) cancelAnimationFrame(this._raf); this._raf = null; } else this.needsFrame = true; }

  /** Change the quality. Everything on the board stays. */
  setTier(n) {
    n = Math.max(0, Math.min(TIERS.length - 1, n));
    if (n === this.tier) return;
    const q = (this.q = TIERS[n]), r = this.renderer, sun = this.sun;
    this.tier = n;
    r.setPixelRatio(Math.min(window.devicePixelRatio || 1, q.dpr));
    const soft = q.softShadow ? THREE.PCFSoftShadowMap : THREE.PCFShadowMap;
    r.shadowMap.enabled = q.shadow > 0;
    sun.castShadow = q.shadow > 0;
    if (r.shadowMap.type !== soft) { r.shadowMap.type = soft; this.scene.traverse((o) => { if (o.material) o.material.needsUpdate = true; }); }
    const side = Math.min(q.shadow || 1024, this.maxTex);
    if (sun.shadow.mapSize.x !== side) {
      sun.shadow.mapSize.setScalar(side);
      sun.shadow.map?.dispose();
      sun.shadow.map = null;
    }
    r.shadowMap.needsUpdate = true;
    this.needsFrame = true;
    if (this.onTier) this.onTier(n);
  }

  // Judge the pace from real frame times, only while frames are being drawn. A long gap is not slowness:
  // the page was hidden or had nothing to draw. Scenery falling into place at the start is not judged.
  _watchPace(rawMs, landing) {
    const p = this._pace;
    if (rawMs > 400 || landing > 60 || document.hidden) { p.sum = 0; p.n = 0; return; }
    // The time since the last frame counts only if that frame drew something. A frame with nothing to draw
    // says nothing about the pace, and must not throw away what has been counted.
    if (!this._drewLast) return;
    p.sum += rawMs; p.n++;
    if (p.n < PACE_FRAMES) return;
    const mean = p.sum / p.n;
    p.sum = 0; p.n = 0;
    if (mean > PACE_SLOW_MS && this.tier > 0) {
      this.setTier(this.tier - 1);
      storeTier(this.tier);
    } else if (mean > PACE_HOPELESS_MS && this.tier === 0 && this.onTooSlow) {
      const say = this.onTooSlow;
      this.onTooSlow = null;
      say();
    }
  }

  /** Keep the board inside the part of the canvas the interface does not cover. */
  setInsets(i) { Object.assign(this.insetsGoal, i); this.needsFrame = true; }

  /** Render a GPC1 stream (ArrayBuffer or Uint8Array). Throws on malformed input. */
  render(buf) {
    const cmds = decodeStream(buf);
    this.lastCommands = cmds;
    const now = performance.now(), first = this.frames === 0;
    const draws = [], labels = [];
    this.highlights = new Map();
    for (const c of cmds) {
      switch (c.op) {
        case 'clear':
          this.bg.setHex(c.rgb & 0xffffff);
          break;
        case 'camera': this._setCamera(c); break;
        case 'light':
          this.sunDir.set(...c.dir);
          if (this.sunDir.lengthSq() < 1e-9) this.sunDir.set(0, -1, 0);
          this.sunDir.normalize();
          this.sun.intensity = 2.2 * c.intensity;
          break;
        case 'mesh': {
          const key = c.prim + ':' + c.args.join(',');
          const old = this.geoms.get(c.id);
          if (!old || old.key !== key) {
            const geo = buildGeometry(c.prim, c.args);
            this.geoms.set(c.id, { key, geo });
            if (old) for (const it of this.items) if (it.mesh === c.id) this._swapGeo(it, geo, old.geo);
          }
          break;
        }
        case 'meshFile': this._defineMeshFile(c); break;
        case 'draw': draws.push(c); break;
        case 'label': labels.push(c); break;
        case 'highlight': this.highlights.set(c.pick, c.rgb); break;
      }
    }
    this._reconcile(draws, labels, now, first);
    this._fitShadow();
    this._wake();
    this.renderer.shadowMap.needsUpdate = true;
    this.needsFrame = true;
    this.frames++;
  }

  _swapGeo(it, geo, oldGeo) {
    if (it.obj.geometry === oldGeo) it.obj.geometry = geo;
    if (it.outline) it.outline.geometry = geo;
    const g = this.geoms.get(it.mesh), m = it.obj.material;
    it.motion = g?.motion ?? null;
    this._batchDirty = true;
    if (g && m.vertexColors !== !!g.colored) { m.vertexColors = !!g.colored; m.needsUpdate = true; }
  }

  // The stand-in draws until the file loads. It stays if the file never does: a missing file is no error.
  _defineMeshFile(c) {
    const key = `file:${c.sha}:${c.tint}:${c.prim}:${c.args.join(',')}:${c.motion.pulse},${c.motion.sway},${c.motion.glow}`;
    const old = this.geoms.get(c.id);
    if (old && old.key === key) return;
    const motion = c.motion.pulse || c.motion.sway || c.motion.glow ? { ...c.motion, tint: new THREE.Color(c.tint & 0xffffff) } : null;
    const geo = this.meshFiles.get(c.sha) || tinted(buildGeometry(c.prim, c.args), c.tint);
    this.geoms.set(c.id, { key, geo, colored: true, motion, sha: c.sha });
    if (old) for (const it of this.items) if (it.mesh === c.id) this._swapGeo(it, geo, old.geo);
    if (!this.meshFiles.has(c.sha)) this._loadMeshFile(c.sha);
  }

  async _loadMeshFile(sha) {
    this.meshFiles.set(sha, null); // once only
    let geo;
    try { geo = meshFileGeometry(await fetchMeshFile(this.assetBase, sha)); }
    catch (e) { console.warn(`gpc: mesh file ${sha.slice(0, 12)} stays a stand-in: ${e.message}`); return; }
    this.meshFiles.set(sha, geo);
    for (const [id, g] of this.geoms) {
      if (g.sha !== sha) continue;
      const oldGeo = g.geo;
      g.geo = geo;
      for (const it of [...this.items, ...this.dying]) if (it.mesh === id) this._swapGeo(it, geo, oldGeo);
      oldGeo.dispose();
    }
    this.renderer.shadowMap.needsUpdate = true;
    this.needsFrame = true;
  }

  _classOf(c, isLabel) {
    if (isLabel) return c.pick ? `L#${c.pick}` : `L:${c.text}`;
    return c.pick ? `P#${c.pick}:${c.mesh}` : `M:${c.mesh}`;
  }

  _reconcile(draws, labels, now, first) {
    const pool = new Map();
    for (const it of this.items) {
      if (!pool.has(it.cls)) pool.set(it.cls, []);
      pool.get(it.cls).push(it);
    }
    const next = [], fresh = [];
    const place = (c, isLabel) => {
      const cls = this._classOf(c, isLabel), cand = pool.get(cls) || [];
      const pos = v3(c.pos);
      let idx = cand.findIndex((it) => sameV(it.to.pos, pos));
      // Decoration never glides: with no object at this exact place, a new one drops in.
      if (idx < 0 && cand.length && (isLabel || c.pick)) idx = 0;
      let it;
      if (idx >= 0) { it = cand.splice(idx, 1)[0]; this._update(it, c, isLabel, now); }
      else { it = this._create(c, isLabel, cls); if (!it) return; fresh.push(it); }
      next.push(it);
    };
    for (const d of draws) place(d, false);
    for (const l of labels) place(l, true);
    // appear animations, staggered (radially on the first frame)
    const c0 = this._centerOf(draws);
    this.reduced = reduceMotion();
    fresh.forEach((it, k) => {
      const delay = first ? Math.min(600, it.to.pos.distanceTo(c0) * 60) : Math.min(k * 9, 260);
      // On a lower tier the scenery of a new board is simply there. Only what can be acted on drops in.
      const still = this._holdsStill(it);
      const drops = !this.reduced && (!first || this.q.dropIn || !still);
      if (drops) it.anim = { kind: 'appear', t0: now + delay, dur: APPEAR_MS };
      this._apply(it, now);
      if (still) this._batchDirty = true;
    });
    for (const rest of pool.values()) for (const it of rest) {
      this._unbatch(it);
      it.anim = { kind: 'vanish', t0: now, dur: VANISH_MS, from: this._snapshot(it) };
      this.dying.push(it);
    }
    this.items = next;
    this._refreshHighlights();
  }

  _centerOf(draws) {
    const c = new THREE.Vector3();
    if (!draws.length) return c;
    for (const d of draws) c.add(v3(d.pos));
    return c.multiplyScalar(1 / draws.length);
  }

  _target(c, isLabel) {
    return {
      pos: v3(c.pos),
      rotY: isLabel ? 0 : c.rotY,
      scale: isLabel ? new THREE.Vector3(c.size, c.size, 1) : v3(c.scale),
      color: new THREE.Color(c.rgb & 0xffffff),
      opacity: opacityOf(c.rgb),
    };
  }

  _create(c, isLabel, cls) {
    const it = { cls, pick: c.pick, label: isLabel, rgb: c.rgb, hover: 0 };
    it.to = this._target(c, isLabel);
    if (isLabel) {
      it.text = c.text;
      const mat = new THREE.SpriteMaterial({ transparent: true, depthWrite: false, depthTest: false, toneMapped: false, fog: false });
      it.obj = new THREE.Sprite(mat);
      it.obj.renderOrder = 10;
      this._labelTex(it, null);
    } else {
      const g = this.geoms.get(c.mesh);
      if (!g) { console.warn(`gpc: draw of undefined mesh ${c.mesh}`); return null; }
      it.mesh = c.mesh;
      it.motion = g.motion ?? null;
      it.phase = (c.pos[0] * 2.7 + c.pos[2] * 4.1) % (2 * Math.PI);
      const mat = new THREE.MeshStandardMaterial({ color: it.to.color, roughness: 0.86, metalness: 0, flatShading: true, vertexColors: !!g.colored });
      it.obj = new THREE.Mesh(g.geo, mat);
      it.obj.castShadow = it.to.opacity > 0.6;
      it.obj.receiveShadow = true;
    }
    it.obj.userData.item = it;
    this.root.add(it.obj);
    return it;
  }

  _labelTex(it, glow) {
    const key = `${it.text}|${it.rgb & 0xffffff}|${glow}`;
    if (it.texKey === key) return;
    const old = it.obj.material.map;
    const { tex, aspect, scale } = labelTexture(it.text, it.rgb, glow);
    it.obj.material.map = tex;
    it.obj.material.needsUpdate = true;
    it.aspect = aspect; it.texScale = scale; it.texKey = key;
    if (old) old.dispose();
  }

  _update(it, c, isLabel, now) {
    const from = this._snapshot(it), to = this._target(c, isLabel);
    const moved = !sameV(from.pos, to.pos) || !sameV(from.scale, to.scale) || Math.abs(from.rotY - to.rotY) > 1e-4 ||
      !from.color.equals(to.color) || Math.abs(from.opacity - to.opacity) > 1e-3;
    if (!isLabel && c.mesh !== it.mesh) {
      const g = this.geoms.get(c.mesh);
      if (g) { it.mesh = c.mesh; it.obj.geometry = g.geo; if (it.outline) it.outline.geometry = g.geo; }
    }
    it.rgb = c.rgb; it.pick = c.pick; it.to = to; it.dirty = true;
    if (isLabel) it.text = c.text;
    if (isLabel) this._labelTex(it, this.highlights.get(it.pick) ?? null);
    else it.obj.castShadow = to.opacity > 0.6;
    if (moved) { this._unbatch(it); it.anim = { kind: 'move', t0: now, dur: MOVE_MS, from }; }
  }

  // ------------------------------------------------------------ scenery in batches

  // A late board has more than a thousand things on it, nearly all of them scenery that never moves. Each
  // of those is one draw call if it is drawn alone. Once it holds still it joins a batch of its shape, and
  // draws in one call with the others of that shape. It looks exactly the same, and it cannot be picked
  // anyway. It leaves the batch the moment it has to move.
  _unbatch(it) {
    if (!it.batched) return;
    it.batched = false;
    this.root.add(it.obj);
    this._batchDirty = true;
  }

  // Things that react to a pointer, or glow, need a material of their own. A piece or a tile can be pointed
  // at for its details, and picking does not need it to be drawn alone.
  _holdsStill(it) { return !it.label && (!it.pick || (!this.hoverFx(it.pick) && !this.highlights.has(it.pick))); }

  _batchMaterial(colored) {
    let m = this._batchMats.get(colored);
    if (!m) { m = new THREE.MeshStandardMaterial({ roughness: 0.86, metalness: 0, flatShading: true, vertexColors: colored }); this._batchMats.set(colored, m); }
    return m;
  }

  _rebatch() {
    this._batchDirty = false;
    const groups = new Map();
    for (const it of this.items) {
      const fits = this._holdsStill(it) && !it.motion && !it.anim && it.to.opacity >= 0.999;
      if (!fits) { this._unbatch(it); this._batchDirty = false; continue; }
      // Picking still uses its own place, so that place must be up to date when it leaves the scene.
      if (!it.batched) { it.batched = true; this.root.remove(it.obj); it.obj.updateMatrixWorld(true); }
      const geo = it.obj.geometry;
      if (!groups.has(geo)) groups.set(geo, []);
      groups.get(geo).push(it);
    }
    for (const b of this.batches) { this.root.remove(b); b.dispose(); }
    this.batches = [];
    const d = this._dummy || (this._dummy = new THREE.Object3D());
    for (const [geo, list] of groups) {
      const b = new THREE.InstancedMesh(geo, this._batchMaterial(!!this.geoms.get(list[0].mesh)?.colored), list.length);
      b.castShadow = true; b.receiveShadow = true; b.frustumCulled = false;
      list.forEach((it, i) => {
        d.position.copy(it.to.pos); d.rotation.set(0, it.to.rotY, 0); d.scale.copy(it.to.scale); d.updateMatrix();
        b.setMatrixAt(i, d.matrix);
        b.setColorAt(i, it.to.color);
      });
      this.root.add(b);
      this.batches.push(b);
    }
    this.renderer.shadowMap.needsUpdate = true;
  }

  // current displayed state (mid-animation values included)
  _snapshot(it) {
    if (!it.shown) return { ...it.to, pos: it.to.pos.clone(), scale: it.to.scale.clone(), color: it.to.color.clone() };
    const s = it.shown;
    return { pos: s.pos.clone(), rotY: s.rotY, scale: s.scale.clone(), color: s.color.clone(), opacity: s.opacity };
  }

  _apply(it, now) {
    const to = it.to, a = it.anim;
    let pos = to.pos.clone(), rotY = to.rotY, scale = to.scale.clone(), color = to.color.clone(), opacity = to.opacity;
    if (a) {
      if (this._holdsStill(it) && (now - a.t0) >= a.dur) this._batchDirty = true;
      const t = clamp01((now - a.t0) / a.dur);
      if (a.kind === 'move') {
        const e = ease.outCubic(t);
        pos = a.from.pos.clone().lerp(to.pos, e);
        scale = a.from.scale.clone().lerp(to.scale, e);
        rotY = lerpAngle(a.from.rotY, to.rotY, e);
        color = a.from.color.clone().lerp(to.color, e);
        opacity = a.from.opacity + (to.opacity - a.from.opacity) * e;
      } else if (a.kind === 'appear') {
        if (it.label) {
          pos.y += 0.4 * (1 - ease.outCubic(t));
          opacity *= clamp01(t * 2.2);
        } else {
          const h = Math.max(0.55, scale.y * 2);
          pos.y += h * dropCurve(t);
          const s = squash(t);
          scale.y *= 1 - 0.14 * s;
          scale.x *= 1 + 0.07 * s; scale.z *= 1 + 0.07 * s;
          opacity *= clamp01(t * 3);
        }
      } else if (a.kind === 'vanish') {
        const e = ease.inOutCubic(t);
        pos = a.from.pos; rotY = a.from.rotY; color = a.from.color;
        scale = a.from.scale.clone().multiplyScalar(1 - 0.85 * e);
        opacity = a.from.opacity * (1 - e);
      }
      if (t >= 1) it.anim = null;
      if (now < a.t0 && a.kind === 'appear') opacity = 0;
    }
    it.shown = { pos, rotY, scale, color, opacity };
    // hover / highlight cosmetics
    const hl = this.highlights.get(it.pick);
    const o = it.obj;
    o.position.copy(pos);
    if (it.label) {
      const k = 1 + 0.08 * it.hover;
      o.scale.set(scale.x * it.aspect * it.texScale * k, scale.y * it.texScale * k, 1);
      o.material.opacity = opacity;
      o.material.color.setScalar(1);
    } else {
      o.rotation.y = rotY;
      const k = 1 + 0.05 * it.hover;
      o.scale.set(scale.x * k, scale.y * k, scale.z * k);
      o.position.y += 0.04 * it.hover;
      const m = o.material;
      m.color.copy(color);
      m.opacity = opacity;
      const translucent = opacity < 0.999;
      if (m.transparent !== translucent) { m.transparent = translucent; m.depthWrite = !translucent || opacity > 0.9; m.needsUpdate = true; }
      const pulse = hl != null ? (this.reduced ? 0.6 : 0.5 + 0.5 * Math.sin(now * 0.006)) : 0;
      if (hl != null) m.emissive.copy(color).lerp(this._hlColor.setHex(hl & 0xffffff), 0.3).multiplyScalar(0.1 + 0.3 * pulse + 0.2 * it.hover);
      else m.emissive.copy(color).multiplyScalar(0.28 * it.hover);
      if (it.motion && !this.still) {
        const wave = Math.sin(now * 0.0017 + it.phase), mo = it.motion;
        if (mo.pulse) { const w = mo.pulse * wave; o.scale.x *= 1 - 0.6 * w; o.scale.y *= 1 + w; o.scale.z *= 1 - 0.6 * w; }
        if (mo.sway) { o.rotation.x = mo.sway * wave; o.rotation.z = mo.sway * Math.cos(now * 0.0013 + it.phase); }
        if (mo.glow) { const g = mo.glow * (0.5 + 0.5 * wave); m.emissive.r += color.r * mo.tint.r * g; m.emissive.g += color.g * mo.tint.g * g; m.emissive.b += color.b * mo.tint.b * g; }
      }
      if (it.outline) {
        it.outline.material.opacity = (0.55 + 0.45 * pulse) * Math.min(1, opacity * 1.5);
        // constant world-space rim: ~0.05 sideways, ~0.035 above the top
        const bb = it.obj.geometry.boundingBox || (it.obj.geometry.computeBoundingBox(), it.obj.geometry.boundingBox);
        const rx = Math.max(1e-3, (bb.max.x - bb.min.x) / 2 * Math.abs(scale.x)), rz = Math.max(1e-3, (bb.max.z - bb.min.z) / 2 * Math.abs(scale.z));
        const hy = Math.max(1e-3, bb.max.y * Math.abs(scale.y));
        it.outline.scale.set(1 + 0.018 / rx, 1 + 0.014 / hy, 1 + 0.018 / rz);
      }
    }
    o.visible = opacity > 0.002;
  }

  _refreshHighlights() {
    for (const it of this.items) {
      const hl = this.highlights.get(it.pick);
      if (it.label) { this._labelTex(it, hl ?? null); continue; }
      if (hl != null) this._unbatch(it);
      if ((hl != null) !== !!it.lit) { it.lit = hl != null; it.dirty = true; this._batchDirty = true; }
      if (hl != null && it.pick) {
        if (!it.outline) {
          it.outline = new THREE.Mesh(it.obj.geometry, new THREE.MeshBasicMaterial({ side: THREE.BackSide, transparent: true, depthWrite: false, toneMapped: false }));
          it.outline.position.y = -0.01;
          it.obj.add(it.outline);
        }
        it.outline.material.color.setHex(hl & 0xffffff);
      } else if (it.outline) {
        it.obj.remove(it.outline);
        it.outline.material.dispose();
        it.outline = null;
      }
    }
  }

  // ------------------------------------------------------------ camera

  _setCamera(c) {
    const key = [...c.eye, ...c.target, c.fov].join(',');
    if (key === this.lastCameraKey) return;
    this.lastCameraKey = key;
    const eye = v3(c.eye), tgt = v3(c.target), d = eye.clone().sub(tgt);
    this.view.target.copy(tgt);
    this.view.dir.copy(d).normalize();
    this.view.elev = Math.asin(THREE.MathUtils.clamp(this.view.dir.y, -1, 1));
    this.view.radius = c.fov < 0 ? -c.fov : Math.max(d.length() * 0.5, 2);
    this.needsFrame = true;
  }

  /** Return to the whole board. */
  resetView() { this.zoomGoal = 1; this.panGoal.set(0, 0); this.needsFrame = true; }

  _bindInput() {
    const el = this.canvas, ptrs = new Map();
    let tap = null, pinch = null;
    el.style.touchAction = 'none';
    el.style.webkitTouchCallout = 'none';
    el.style.webkitUserSelect = 'none';
    el.style.userSelect = 'none';
    // Safari's own pinch would zoom the whole page.
    el.addEventListener('gesturestart', (e) => e.preventDefault());
    const rect = () => el.getBoundingClientRect();
    const setPointer = (e) => {
      const r = rect();
      this.pointer.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
      this.pointerPx = { x: e.clientX, y: e.clientY };
    };
    const pinchOf = () => {
      const [a, b] = [...ptrs.values()];
      return { d: Math.max(1, Math.hypot(a.x - b.x, a.y - b.y)), x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
    };
    el.addEventListener('contextmenu', (e) => e.preventDefault());
    el.addEventListener('pointerdown', (e) => {
      el.setPointerCapture(e.pointerId);
      ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
      this.gesture = true;
      if (ptrs.size === 1) tap = { x0: e.clientX, y0: e.clientY, t0: performance.now(), moved: false, touch: e.pointerType !== 'mouse' };
      else { if (tap) tap.moved = true; pinch = ptrs.size === 2 ? pinchOf() : null; }
    });
    el.addEventListener('pointermove', (e) => {
      // A finger only hovers while it is down, so only a mouse shows what is under the pointer.
      if (e.pointerType === 'mouse') { setPointer(e); this.pointerInside = true; this.needsFrame = true; }
      const last = ptrs.get(e.pointerId);
      if (!last) return;
      const dx = e.clientX - last.x, dy = e.clientY - last.y;
      last.x = e.clientX; last.y = e.clientY;
      if (ptrs.size === 2 && pinch) {
        const now = pinchOf(), r = rect();
        this._zoomBy(now.d / pinch.d, now.x - r.left, now.y - r.top);
        this._panBy(now.x - pinch.x, now.y - pinch.y);
        pinch = now;
        return;
      }
      if (ptrs.size !== 1 || !tap) return;
      if (!tap.moved && Math.hypot(e.clientX - tap.x0, e.clientY - tap.y0) > (tap.touch ? 8 : 5)) tap.moved = true;
      if (tap.moved) this._panBy(dx, dy);
    });
    const end = (e) => {
      ptrs.delete(e.pointerId);
      pinch = null;
      if (ptrs.size === 0) { this.gesture = false; this.needsFrame = true; }
      if (!tap) return;
      if (!tap.moved && ptrs.size === 0 && performance.now() - tap.t0 < 700 && e.type === 'pointerup' && e.button === 0) {
        setPointer(e);
        const r = rect();
        const id = tap.touch ? this.pickNear(e.clientX - r.left, e.clientY - r.top) : this.pickAt(this.pointer.x, this.pointer.y);
        if (id && this.onPick) this.onPick(id, e.clientX, e.clientY);
      }
      if (ptrs.size === 0) tap = null;
    };
    el.addEventListener('pointerup', end);
    el.addEventListener('pointercancel', end);
    el.addEventListener('pointerleave', () => { this.pointerInside = false; this.needsFrame = true; });
    el.addEventListener('wheel', (e) => { e.preventDefault(); const r = rect(); this._zoomBy(Math.exp(-e.deltaY * 0.0012), e.clientX - r.left, e.clientY - r.top); }, { passive: false });
    el.addEventListener('dblclick', () => this.resetView());
  }

  /** Change the zoom. The point of the board under (px, py) in the canvas stays under it. */
  _zoomBy(f, px, py) {
    const before = this.zoomGoal, c = this.canvas, I = this.insets;
    this.zoomGoal = THREE.MathUtils.clamp(this.zoomGoal * f, 1, this.maxZoom);
    if (px != null && this._k && this.zoomGoal !== before) {
      const base = this._k / this.zoom, change = 1 / (base * before) - 1 / (base * this.zoomGoal);
      this.panGoal.x += (px - (c.clientWidth || 1) / 2 - (I.l - I.r) / 2) * change;
      this.panGoal.y += ((c.clientHeight || 1) / 2 - py + (I.t - I.b) / 2) * change;
    }
    this.needsFrame = true;
    this._clampPan();
  }

  _panBy(dx, dy) {
    const k = this._k || 40;
    this.panGoal.x -= dx / k;
    this.panGoal.y += dy / k;
    this._clampPan();
    this.needsFrame = true;
  }

  // Zoomed all the way out, the board cannot leave its place. Zoomed in, it can move only as far as
  // needed to see its edges.
  _clampPan() {
    const R = this.view.radius, slackX = R * (1 - 1 / this.zoomGoal), slackY = slackX * Math.sin(this.view.elev);
    this.panGoal.x = THREE.MathUtils.clamp(this.panGoal.x, -slackX, slackX);
    this.panGoal.y = THREE.MathUtils.clamp(this.panGoal.y, -slackY, slackY);
  }

  _updateCamera(dt) {
    const c = this.canvas, W = c.clientWidth || 1, H = c.clientHeight || 1;
    // While it is held, the board stays under the finger. Otherwise it eases into place.
    const K = 1 - Math.exp(-dt * 12);
    let moving = false;
    const step = (cur, goal, eps) => { if (Math.abs(goal - cur) < eps) return goal; moving = true; return cur + (goal - cur) * K; };
    const hold = (cur, goal) => { if (cur !== goal) moving = true; return goal; };
    const follow = this.gesture ? hold : step;
    this.zoom = follow(this.zoom, this.zoomGoal, 1e-3);
    this.pan.x = follow(this.pan.x, this.panGoal.x, 1e-3);
    this.pan.y = follow(this.pan.y, this.panGoal.y, 1e-3);
    for (const s of ['l', 'r', 't', 'b']) this.insets[s] = step(this.insets[s], this.insetsGoal[s], 0.3);
    const I = this.insets, R = this.view.radius, Rx = R, Ry = R * Math.sin(this.view.elev) + 0.45;
    const k = Math.min(Math.max(W - I.l - I.r, 80) / (2 * Rx), Math.max(H - I.t - I.b, 80) / (2 * Ry)) * this.zoom;
    this._k = k;
    const hw = W / (2 * k), hh = H / (2 * k);
    const ox = -(I.l - I.r) / (2 * k) + this.pan.x, oy = (I.t - I.b) / (2 * k) + this.pan.y;
    const cam = this.camera;
    cam.left = -hw + ox; cam.right = hw + ox; cam.top = hh + oy; cam.bottom = -hh + oy;
    cam.position.copy(this.view.target).addScaledVector(this.view.dir, 60);
    cam.lookAt(this.view.target);
    cam.updateProjectionMatrix();
    return moving;
  }

  // ------------------------------------------------------------ shadows, picking, loop

  _fitShadow() {
    const R = this.view.radius + 2.2, center = this.view.target, s = this.sun.shadow.camera;
    s.left = s.bottom = -R; s.right = s.top = R; s.near = 0.1; s.far = R * 6;
    s.updateProjectionMatrix();
    this.sun.target.position.copy(center);
    this.sun.position.copy(center).addScaledVector(this.sunDir, -R * 3);
    this.sun.target.updateMatrixWorld();
  }

  /** Pick id under normalized device coords (x, y in [-1, 1]); 0 if none. */
  pickAt(x, y) {
    this.raycaster.setFromCamera(new THREE.Vector2(x, y), this.camera);
    const objs = this.items.filter((it) => it.pick && it.obj.visible).map((it) => it.obj);
    for (const hit of this.raycaster.intersectObjects(objs, false)) {
      const it = hit.object.userData.item;
      if (it && it.pick) return it.pick;
    }
    return 0;
  }

  /** What a finger meant at (px, py) in the canvas. A finger is wider than a small target, so if what is
   *  exactly under it cannot be acted on, look nearby, closest first, for what can. If nothing can, it is
   *  what pickAt reports there. */
  pickNear(px, py) {
    const c = this.canvas, W = c.clientWidth || 1, H = c.clientHeight || 1;
    const at = (x, y) => this.pickAt((x / W) * 2 - 1, -(y / H) * 2 + 1);
    const exact = at(px, py);
    if (exact && this.clickable(exact)) return exact;
    for (const r of [7, 14, 22]) {
      const seen = new Set();
      for (let k = 0; k < 12; k++) {
        const id = at(px + r * Math.cos(k * Math.PI / 6), py + r * Math.sin(k * Math.PI / 6));
        if (id && this.clickable(id)) seen.add(id);
      }
      if (seen.size) {
        const away = (id) => { const p = this.screenOf(id); return p ? Math.hypot(p.x - px, p.y - py) : Infinity; };
        return [...seen].sort((a, b) => away(a) - away(b))[0];
      }
    }
    return exact;
  }

  /** Screen position (CSS px, relative to canvas) of the first object with this pick id. */
  screenOf(pickId) {
    const it = this.items.find((i) => i.pick === pickId);
    if (!it) return null;
    const p = it.obj.getWorldPosition(new THREE.Vector3());
    if (!it.label) p.y += 0.5 * it.to.scale.y * 0.2;
    p.project(this.camera);
    const r = this.canvas.getBoundingClientRect();
    return { x: (p.x + 1) / 2 * r.width, y: (1 - p.y) / 2 * r.height };
  }

  /** Screen position (CSS px, relative to the canvas) of a point in the world. */
  worldToScreen(x, y, z) {
    const p = new THREE.Vector3(x, y, z).project(this.camera), r = this.canvas.getBoundingClientRect();
    return { x: (p.x + 1) / 2 * r.width, y: (1 - p.y) / 2 * r.height };
  }

  /** Counts for tests and debugging. */
  stats() {
    return { meshes: this.items.filter((i) => !i.label).length, labels: this.items.filter((i) => i.label).length,
      pickables: new Set(this.items.filter((i) => i.pick).map((i) => i.pick)).size, highlights: this.highlights.size,
      animating: this.items.filter((i) => i.anim).length + this.dying.length, hover: this.hoverId,
      moving: this.items.filter((i) => i.motion).length, batched: this.items.filter((i) => i.batched).length, batches: this.batches.length, tier: this.tier, triangles: this.items.reduce((n, i) => { const g = i.obj.geometry; return i.label ? n : n + (g.index ? g.index.count : g.attributes.position.count) / 3; }, 0),
      meshFiles: [...this.meshFiles.values()].filter(Boolean).length, standIns: [...this.meshFiles.values()].filter((g) => !g).length };
  }

  setTable(visible) { this.table.visible = !!visible; this.needsFrame = true; }

  _resize() {
    const c = this.canvas, w = c.clientWidth | 0, h = c.clientHeight | 0;
    if (w && h && (c.width !== Math.floor(w * this.renderer.getPixelRatio()) || c.height !== Math.floor(h * this.renderer.getPixelRatio()))) {
      this.renderer.setSize(w, h, false);
      this.renderer.shadowMap.needsUpdate = true;
      return true;
    }
    return false;
  }

  _tick(now) {
    this._raf = null;
    if (this.paused) return;
    const raw = now - this._clock;
    const dt = Math.min(0.1, raw / 1000);
    this._clock = now;
    let frame = this._nf;
    this._nf = false;
    if (this._resize()) frame = true;
    const moving = this._updateCamera(dt);
    if (moving) frame = true;
    this.camera.updateMatrixWorld();
    // hover
    const id = this.pointerInside ? this.pickAt(this.pointer.x, this.pointer.y) : 0;
    const changed = id !== this.hoverId;
    if (changed) {
      this.hoverId = id;
      this.canvas.style.cursor = id && this.clickable(id) ? 'pointer' : '';
      frame = true;
    }
    if (this.onHover && (this.pointerInside || changed)) this.onHover(id, this.pointerPx.x, this.pointerPx.y);
    const kh = 1 - Math.exp(-dt * 14);
    const t = performance.now();
    const fx = id && this.hoverFx(id) ? id : 0;
    let animating = false, landing = 0, anyMotion = false;
    // Things that move by themselves are drawn at the tier's own rate, and their shadows stay put. A machine
    // that cannot keep up at 10 frames a second gets a still board instead of a slow one.
    this.reduced = reduceMotion();
    this.still = this.reduced || !this.q.motionMs || this.motionSlow >= 20;
    const moveNow = !this.still && t - this.motionAt >= this.q.motionMs;
    if (moveNow) {
      this.motionSlow = t - this.motionAt > 100 && this.motionAt ? this.motionSlow + 1 : 0;
      this.motionAt = t;
    }
    // A glowing place keeps the loop running, at the tier's own rate.
    const glowing = this.highlights.size > 0 && !this.reduced;
    const pulseNow = glowing && t - this.pulseAt >= this.q.pulseMs;
    if (pulseNow) this.pulseAt = t;
    for (const it of this.items) {
      if (it.batched) continue;
      const h = it.pick && it.pick === fx ? 1 : 0;
      const hover = Math.abs(h - it.hover) < 1e-3 ? h : it.hover + (h - it.hover) * kh;
      const easing = hover !== it.hover;
      it.hover = hover;
      if (it.motion && !this.still) anyMotion = true;
      const pulsing = pulseNow && this.highlights.has(it.pick);
      const busy = it.anim || easing || it.dirty || pulsing || (it.motion && moveNow);
      if (busy || it.wasBusy) { this._apply(it, t); frame = true; }
      if (it.anim) { animating = true; landing++; }
      // One more frame after a motion ends, to draw where it stopped. A pulse needs none: the next one is coming.
      it.wasBusy = !!(it.anim || easing || it.dirty);
      it.dirty = false;
    }
    this.dying = this.dying.filter((it) => {
      this._apply(it, t);
      frame = true; animating = true;
      if (it.anim) return true;
      this.root.remove(it.obj);
      it.obj.material.map?.dispose();
      it.obj.material.dispose();
      return false;
    });
    // Scenery joins its batches once it has all landed, so the batches are built once.
    if (this._batchDirty && !this.items.some((it) => it.anim && this._holdsStill(it))) { this._rebatch(); frame = true; }
    // A lower tier moves shadows only when the motion ends.
    if (animating ? this.q.liveShadow : this._wasAnimating) this.renderer.shadowMap.needsUpdate = true;
    this._wasAnimating = animating;
    this._watchPace(raw, landing);
    this._drewLast = frame;
    if (frame) this.renderer.render(this.scene, this.camera);
    if (frame || moving || animating || glowing || anyMotion || this._nf) this._wake();
  }

  dispose() {
    if (this._raf != null) cancelAnimationFrame(this._raf);
    this._raf = null;
    this.paused = true;
    for (const b of this.batches) b.dispose();
    for (const g of this.geoms.values()) g.geo.dispose();
    this.renderer.dispose();
  }
}

export default GpuPlayer;
