// lean-gpu-cmd player: renders a GPC1 command stream with three.js (vendored).
// API: const p = new GpuPlayer(canvas, opts); p.render(arrayBuffer); p.onPick = (id) => {};
// Wire format: see ../WIRE.md.
import * as THREE from './vendor/three.module.min.js';

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
  for (let i = 0; i < 4; i++) if (bytes[i] !== MAGIC[i]) throw new Error('gpc: bad magic');
  o = 4;
  const cmds = [];
  while (o < bytes.length) {
    const op = u8();
    switch (op) {
      case 1: cmds.push({ op: 'clear', rgb: u32() }); break;
      case 2: cmds.push({ op: 'camera', eye: vec3(), target: vec3(), fov: f32() }); break;
      case 3: cmds.push({ op: 'light', dir: vec3(), intensity: f32() }); break;
      case 4: {
        const id = u32(), kind = u8();
        if (!PRIMS[kind]) throw new Error(`gpc: bad prim ${kind}`);
        const args = [];
        for (let k = 0; k < PRIM_ARGS[kind]; k++) args.push(f32());
        cmds.push({ op: 'mesh', id, prim: PRIMS[kind], args });
        break;
      }
      case 5: cmds.push({ op: 'draw', mesh: u32(), pos: vec3(), rotY: f32(), scale: vec3(), rgb: u32(), pick: u32() }); break;
      case 6: cmds.push({ op: 'label', text: str(), pos: vec3(), size: f32(), rgb: u32(), pick: u32() }); break;
      case 7: cmds.push({ op: 'highlight', pick: u32(), rgb: u32() }); break;
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

const MOVE_MS = 350, APPEAR_MS = 460, VANISH_MS = 220;

// ---------------------------------------------------------------- geometry

function extrudeUp(shape, h, b) {
  const g = new THREE.ExtrudeGeometry(shape, {
    depth: Math.max(h - 2 * b, 1e-4), bevelEnabled: b > 0, bevelThickness: b, bevelSize: b,
    bevelSegments: 3, curveSegments: 24,
  });
  g.rotateX(-Math.PI / 2); // extrusion axis -> +Y, shape y -> -Z
  g.translate(0, b, 0);
  return g;
}

function lathe(r, h, b, cone) {
  const pts = [new THREE.Vector2(0, 0)];
  const steps = 4;
  if (cone) {
    pts.push(new THREE.Vector2(r, 0), new THREE.Vector2(0, h));
  } else {
    pts.push(new THREE.Vector2(r - b, 0));
    for (let i = 1; i <= steps; i++) { const a = (i / steps) * Math.PI / 2; pts.push(new THREE.Vector2(r - b + b * Math.sin(a), b - b * Math.cos(a))); }
    for (let i = 0; i <= steps; i++) { const a = (i / steps) * Math.PI / 2; pts.push(new THREE.Vector2(r - b + b * Math.cos(a), h - b + b * Math.sin(a))); }
    pts.push(new THREE.Vector2(0, h));
  }
  return new THREE.LatheGeometry(pts, 48);
}

function buildGeometry(prim, a) {
  const pos = (x) => Math.max(x, 1e-3);
  switch (prim) {
    case 'hexPrism': {
      const r = pos(a[0]), h = pos(a[1]), b = Math.min(0.05 * r, 0.3 * h);
      const R = r - b / Math.cos(Math.PI / 6), s = new THREE.Shape();
      for (let k = 0; k < 6; k++) {
        const t = Math.PI / 2 + (k * Math.PI) / 3;
        k ? s.lineTo(R * Math.cos(t), R * Math.sin(t)) : s.moveTo(R * Math.cos(t), R * Math.sin(t));
      }
      s.closePath();
      return extrudeUp(s, h, b);
    }
    case 'box': {
      const w = pos(a[0]), h = pos(a[1]), d = pos(a[2]), b = Math.min(w, h, d) * 0.035;
      const s = new THREE.Shape();
      s.moveTo(-w / 2 + b, -d / 2 + b); s.lineTo(w / 2 - b, -d / 2 + b); s.lineTo(w / 2 - b, d / 2 - b); s.lineTo(-w / 2 + b, d / 2 - b); s.closePath();
      return extrudeUp(s, h, b);
    }
    case 'cylinder': { const r = pos(a[0]), h = pos(a[1]); return lathe(r, h, Math.min(0.12 * r, 0.25 * h), false); }
    case 'cone': return lathe(pos(a[0]), pos(a[1]), 0, true);
    case 'sphere': { const r = pos(a[0]); const g = new THREE.SphereGeometry(r, 32, 20); g.translate(0, r, 0); return g; }
    case 'house': {
      const w = pos(a[0]), h = pos(a[1]), d = pos(a[2]), b = Math.min(w, h, d) * 0.05;
      const W = w / 2 - b, H = h - 2 * b, s = new THREE.Shape();
      s.moveTo(-W, 0); s.lineTo(W, 0); s.lineTo(W, 0.6 * H); s.lineTo(0, H); s.lineTo(-W, 0.6 * H); s.closePath();
      const g = new THREE.ExtrudeGeometry(s, { depth: Math.max(d - 2 * b, 1e-4), bevelEnabled: true, bevelThickness: b, bevelSize: b, bevelSegments: 2 });
      g.translate(0, b, -(d - 2 * b) / 2);
      return g;
    }
    case 'gable': {
      const w = pos(a[0]), h = pos(a[1]), d = pos(a[2]), s = new THREE.Shape();
      s.moveTo(-w / 2, 0); s.lineTo(w / 2, 0); s.lineTo(0, h); s.closePath();
      const g = new THREE.ExtrudeGeometry(s, { depth: d, bevelEnabled: false });
      g.translate(0, 0, -d / 2);
      return g;
    }
    case 'pyramid': { const g = new THREE.ConeGeometry(pos(a[0]), pos(a[1]), 4, 1); g.translate(0, pos(a[1]) / 2, 0); return g; }
  }
  throw new Error(`gpc: unknown prim ${prim}`);
}

// ---------------------------------------------------------------- textures

function rng(seed) { let s = seed >>> 0; return () => ((s = (s * 1664525 + 1013904223) >>> 0) / 4294967296); }

function woodTexture(renderer) {
  const N = 1024, c = document.createElement('canvas');
  c.width = c.height = N;
  const g = c.getContext('2d'), rnd = rng(7), planks = 6, ph = N / planks;
  for (let p = 0; p < planks; p++) {
    const y0 = p * ph, l = 27 + rnd() * 7;
    g.fillStyle = `hsl(${24 + rnd() * 6}, 46%, ${l}%)`;
    g.fillRect(0, y0, N, ph);
    for (let i = 0; i < 70; i++) {
      const yy = y0 + rnd() * ph, ph1 = rnd() * 6, amp = 1 + rnd() * 4;
      g.strokeStyle = rnd() < 0.5 ? `rgba(48,26,12,${0.06 + rnd() * 0.16})` : `rgba(255,214,160,${0.03 + rnd() * 0.06})`;
      g.lineWidth = 0.6 + rnd() * 2.2;
      g.beginPath();
      for (let x = 0; x <= N; x += 16) {
        const y = yy + Math.sin(x * 0.006 + ph1) * amp + Math.sin(x * 0.021 + i) * 0.8;
        x ? g.lineTo(x, y) : g.moveTo(x, y);
      }
      g.stroke();
    }
    g.fillStyle = 'rgba(25,12,6,0.55)';
    g.fillRect(0, y0, N, 3);
  }
  const t = new THREE.CanvasTexture(c);
  t.colorSpace = THREE.SRGBColorSpace;
  t.wrapS = t.wrapT = THREE.RepeatWrapping;
  t.repeat.set(14, 14);
  t.anisotropy = renderer.capabilities.getMaxAnisotropy();
  return t;
}

// A tiny procedural "room" (warm ceiling glow, dark floor) prefiltered for reflections.
function warmEnvironment(renderer) {
  const env = new THREE.Scene(), geo = new THREE.SphereGeometry(10, 32, 16), col = [];
  const top = new THREE.Color(0xfff1dd), bottom = new THREE.Color(0x2a1a0f), pos = geo.attributes.position;
  for (let i = 0; i < pos.count; i++) { const c = bottom.clone().lerp(top, (pos.getY(i) / 10 + 1) / 2); col.push(c.r, c.g, c.b); }
  geo.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  env.add(new THREE.Mesh(geo, new THREE.MeshBasicMaterial({ vertexColors: true, side: THREE.BackSide })));
  const panel = new THREE.Mesh(new THREE.PlaneGeometry(6, 6), new THREE.MeshBasicMaterial({ color: 0xffffff }));
  panel.position.set(-3, 8, -2); panel.lookAt(0, 0, 0); env.add(panel);
  const pm = new THREE.PMREMGenerator(renderer), rt = pm.fromScene(env, 0.02);
  pm.dispose();
  return rt.texture;
}

const css = (rgb) => `#${(rgb & 0xffffff).toString(16).padStart(6, '0')}`;

function labelTexture(text, rgb, glow) {
  const fontPx = 96, pad = 28, c = document.createElement('canvas'), g = c.getContext('2d');
  const font = `600 ${fontPx}px ui-sans-serif, system-ui, -apple-system, "Segoe UI", sans-serif`;
  g.font = font;
  const w = Math.ceil(g.measureText(text).width) + pad * 2, h = fontPx + pad * 2;
  c.width = w; c.height = h;
  g.font = font; g.textAlign = 'center'; g.textBaseline = 'middle';
  if (glow != null) { g.shadowColor = css(glow); g.shadowBlur = 26; }
  g.lineJoin = 'round'; g.lineWidth = 14; g.strokeStyle = 'rgba(28,18,10,0.85)';
  g.strokeText(text, w / 2, h / 2 + 4);
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
  /** @param {HTMLCanvasElement} canvas @param {{table?: boolean, background?: number}} opts */
  constructor(canvas, opts = {}) {
    this.canvas = canvas;
    this.onPick = null;   // (pickId) => void
    this.onHover = null;  // (pickId | 0) => void
    const r = (this.renderer = new THREE.WebGLRenderer({ canvas, antialias: true, preserveDrawingBuffer: !!opts.preserveDrawingBuffer }));
    r.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    r.shadowMap.enabled = true;
    r.shadowMap.type = THREE.PCFSoftShadowMap;
    r.outputColorSpace = THREE.SRGBColorSpace;
    r.toneMapping = THREE.ACESFilmicToneMapping;
    r.toneMappingExposure = 1.05;

    const scene = (this.scene = new THREE.Scene());
    this.bg = new THREE.Color(opts.background ?? 0x241a12);
    scene.background = this.bg;
    scene.fog = new THREE.Fog(this.bg, 30, 90);
    this.camera = new THREE.PerspectiveCamera(45, 1, 0.05, 500);

    scene.environment = warmEnvironment(r);
    scene.environmentIntensity = 0.25;
    this.hemi = new THREE.HemisphereLight(0xfff0dc, 0x4a301c, 1.0);
    scene.add(this.hemi);
    const sun = (this.sun = new THREE.DirectionalLight(0xffe2b8, 2.4));
    sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048);
    sun.shadow.bias = -0.0004;
    sun.shadow.normalBias = 0.02;
    sun.shadow.radius = 3;
    scene.add(sun, sun.target);
    this.sunDir = new THREE.Vector3(-0.45, -1, -0.35).normalize();
    const fill = new THREE.DirectionalLight(0xcfe0ff, 0.35);
    fill.position.set(6, 4, 8);
    scene.add(fill);

    this.table = new THREE.Mesh(
      new THREE.PlaneGeometry(400, 400),
      new THREE.MeshStandardMaterial({ map: woodTexture(r), roughness: 0.78, metalness: 0.0 }),
    );
    this.table.rotation.x = -Math.PI / 2;
    this.table.position.y = -0.003;
    this.table.receiveShadow = true;
    this.table.visible = opts.table !== false;
    scene.add(this.table);

    this.root = new THREE.Group();
    scene.add(this.root);
    this.geoms = new Map();     // mesh id -> {key, geo}
    this.items = [];            // live objects
    this.dying = [];            // objects fading out
    this.highlights = new Map();
    this.hoverId = 0;
    this._hlColor = new THREE.Color();
    this.frames = 0;
    this.lastCameraKey = null;
    this.bounds = { center: new THREE.Vector3(), radius: 8 };

    // orbit state (spherical around target); `goal` is where damping heads
    this.orbit = { target: new THREE.Vector3(), radius: 14, theta: 0.6, phi: 0.9 };
    this.goal = { target: new THREE.Vector3(), radius: 14, theta: 0.6, phi: 0.9 };
    this.limits = { minR: 2, maxR: 60, minPhi: 0.12, maxPhi: 1.38 };
    this.raycaster = new THREE.Raycaster();
    this.pointer = new THREE.Vector2(-2, -2);
    this.pointerInside = false;
    this._bindInput();

    this._clock = performance.now();
    this._tick = this._tick.bind(this);
    this._raf = requestAnimationFrame(this._tick);
  }

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
          this.scene.fog.color.copy(this.bg);
          break;
        case 'camera': this._setCamera(c); break;
        case 'light':
          this.sunDir.set(...c.dir);
          if (this.sunDir.lengthSq() < 1e-9) this.sunDir.set(0, -1, 0);
          this.sunDir.normalize();
          this.sun.intensity = 2.4 * c.intensity;
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
        case 'draw': draws.push(c); break;
        case 'label': labels.push(c); break;
        case 'highlight': this.highlights.set(c.pick, c.rgb); break;
      }
    }
    this._reconcile(draws, labels, now, first);
    this._fitShadow();
    this.frames++;
  }

  _swapGeo(it, geo, oldGeo) {
    if (it.obj.geometry === oldGeo) it.obj.geometry = geo;
    if (it.outline) it.outline.geometry = geo;
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
      if (idx < 0 && cand.length) idx = 0;
      let it;
      if (idx >= 0) { it = cand.splice(idx, 1)[0]; this._update(it, c, isLabel, now); }
      else { it = this._create(c, isLabel, cls); if (!it) return; fresh.push(it); }
      next.push(it);
    };
    for (const d of draws) place(d, false);
    for (const l of labels) place(l, true);
    // appear animations, staggered (radially on the first frame)
    const c0 = this._centerOf(draws);
    fresh.forEach((it, k) => {
      const delay = first ? Math.min(700, it.to.pos.distanceTo(c0) * 45) : Math.min(k * 28, 300);
      it.anim = { kind: 'appear', t0: now + delay, dur: APPEAR_MS };
      this._apply(it, now);
    });
    for (const rest of pool.values()) for (const it of rest) {
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
      const mat = new THREE.SpriteMaterial({ transparent: true, depthWrite: false, toneMapped: false, fog: false });
      it.obj = new THREE.Sprite(mat);
      it.obj.renderOrder = 10;
      this._labelTex(it, null);
    } else {
      const g = this.geoms.get(c.mesh);
      if (!g) { console.warn(`gpc: draw of undefined mesh ${c.mesh}`); return null; }
      it.mesh = c.mesh;
      const mat = new THREE.MeshStandardMaterial({ color: it.to.color, roughness: 0.55, metalness: 0.04 });
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
    if (moved) it.anim = { kind: 'move', t0: now, dur: MOVE_MS, from };
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
          const h = Math.max(1.6, scale.y * 2);
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
      const k = 1 + 0.12 * it.hover;
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
      const pulse = hl != null ? 0.5 + 0.5 * Math.sin(now * 0.006) : 0;
      if (hl != null) m.emissive.copy(color).lerp(this._hlColor.setHex(hl & 0xffffff), 0.3).multiplyScalar(0.1 + 0.3 * pulse + 0.2 * it.hover);
      else m.emissive.copy(color).multiplyScalar(0.28 * it.hover);
      if (it.outline) {
        it.outline.material.opacity = (0.55 + 0.45 * pulse) * Math.min(1, opacity * 1.5);
        // constant world-space rim: ~0.05 sideways, ~0.035 above the top
        const bb = it.obj.geometry.boundingBox || (it.obj.geometry.computeBoundingBox(), it.obj.geometry.boundingBox);
        const rx = Math.max(1e-3, (bb.max.x - bb.min.x) / 2 * Math.abs(scale.x)), rz = Math.max(1e-3, (bb.max.z - bb.min.z) / 2 * Math.abs(scale.z));
        const hy = Math.max(1e-3, bb.max.y * Math.abs(scale.y));
        it.outline.scale.set(1 + 0.05 / rx, 1 + 0.035 / hy, 1 + 0.05 / rz);
      }
    }
    o.visible = opacity > 0.002;
  }

  _refreshHighlights() {
    for (const it of this.items) {
      const hl = this.highlights.get(it.pick);
      if (it.label) { this._labelTex(it, hl ?? null); continue; }
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
    const snap = this.lastCameraKey === null;
    this.lastCameraKey = key;
    const eye = v3(c.eye), tgt = v3(c.target), d = eye.clone().sub(tgt);
    const radius = Math.max(d.length(), 0.5);
    const g = this.goal;
    g.target.copy(tgt);
    g.radius = radius;
    g.phi = Math.acos(THREE.MathUtils.clamp(d.y / radius, -1, 1));
    g.theta = Math.atan2(d.x, d.z);
    this.limits.minR = radius * 0.3;
    this.limits.maxR = radius * 2.6;
    this.limits.maxPhi = Math.max(1.38, Math.min(g.phi, 1.5));
    this.home = { target: tgt.clone(), radius, phi: g.phi, theta: g.theta };
    this.camera.fov = c.fov > 1 && c.fov < 170 ? c.fov : 45;
    this.camera.updateProjectionMatrix();
    if (snap) { const o = this.orbit; o.target.copy(g.target); o.radius = g.radius; o.phi = g.phi; o.theta = g.theta; }
    else { const dt = g.theta - this.orbit.theta; this.orbit.theta += Math.round(dt / (2 * Math.PI)) * 2 * Math.PI; }
  }

  /** Return the camera to the stream's camera. */
  resetView() {
    if (!this.home) return;
    const g = this.goal, h = this.home;
    g.target.copy(h.target); g.radius = h.radius; g.phi = h.phi;
    g.theta = this.orbit.theta + (((h.theta - this.orbit.theta + Math.PI) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
  }

  _bindInput() {
    const el = this.canvas, ptrs = new Map();
    let drag = null;
    el.style.touchAction = 'none';
    const rect = () => el.getBoundingClientRect();
    const setPointer = (e) => {
      const r = rect();
      this.pointer.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
    };
    el.addEventListener('contextmenu', (e) => e.preventDefault());
    el.addEventListener('pointerdown', (e) => {
      el.setPointerCapture(e.pointerId);
      ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
      drag = { x: e.clientX, y: e.clientY, x0: e.clientX, y0: e.clientY, t0: performance.now(),
        pan: e.button === 2 || e.button === 1 || e.shiftKey, pinch: ptrs.size === 2 ? this._pinchDist(ptrs) : 0 };
    });
    el.addEventListener('pointermove', (e) => {
      setPointer(e);
      this.pointerInside = true;
      if (!drag || !ptrs.has(e.pointerId)) return;
      ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (ptrs.size === 2) {
        const d = this._pinchDist(ptrs);
        if (drag.pinch) this._zoom(drag.pinch / d);
        drag.pinch = d;
        drag.moved = true;
        return;
      }
      const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
      drag.x = e.clientX; drag.y = e.clientY;
      if (Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) > 5) drag.moved = true;
      const h = rect().height || 1;
      if (drag.pan) this._pan(dx / h, dy / h);
      else {
        this.goal.theta -= (dx / h) * Math.PI * 1.1;
        this.goal.phi = THREE.MathUtils.clamp(this.goal.phi - (dy / h) * Math.PI * 0.9, this.limits.minPhi, this.limits.maxPhi);
      }
    });
    const end = (e) => {
      ptrs.delete(e.pointerId);
      if (!drag) return;
      if (!drag.moved && performance.now() - drag.t0 < 700 && e.type === 'pointerup' && e.button === 0) {
        setPointer(e);
        const id = this.pickAt(this.pointer.x, this.pointer.y);
        if (id && this.onPick) this.onPick(id);
      }
      if (ptrs.size === 0) drag = null;
    };
    el.addEventListener('pointerup', end);
    el.addEventListener('pointercancel', end);
    el.addEventListener('pointerleave', () => { this.pointerInside = false; });
    el.addEventListener('wheel', (e) => { e.preventDefault(); this._zoom(Math.exp(e.deltaY * 0.0012)); }, { passive: false });
    el.addEventListener('dblclick', () => this.resetView());
  }

  _pinchDist(ptrs) { const [a, b] = [...ptrs.values()]; return Math.max(1, Math.hypot(a.x - b.x, a.y - b.y)); }

  _zoom(f) { this.goal.radius = THREE.MathUtils.clamp(this.goal.radius * f, this.limits.minR, this.limits.maxR); }

  _pan(dx, dy) {
    const cam = this.camera, k = this.orbit.radius * Math.tan((cam.fov * Math.PI) / 360) * 2;
    const right = new THREE.Vector3().setFromMatrixColumn(cam.matrix, 0).setY(0).normalize();
    const fwd = new THREE.Vector3(-Math.sin(this.orbit.theta), 0, -Math.cos(this.orbit.theta));
    this.goal.target.addScaledVector(right, -dx * k).addScaledVector(fwd, dy * k);
    const c = this.bounds.center, off = this.goal.target.clone().sub(c), lim = this.bounds.radius * 1.2;
    off.y = 0;
    if (off.length() > lim) this.goal.target.copy(c).add(off.setLength(lim)).setY(this.goal.target.y);
  }

  _updateCamera(dt) {
    const o = this.orbit, g = this.goal, k = 1 - Math.exp(-dt * 10);
    o.theta += (g.theta - o.theta) * k;
    o.phi += (g.phi - o.phi) * k;
    o.radius += (g.radius - o.radius) * k;
    o.target.lerp(g.target, k);
    const sp = Math.sin(o.phi), cam = this.camera;
    cam.position.set(o.target.x + o.radius * sp * Math.sin(o.theta), o.target.y + o.radius * Math.cos(o.phi), o.target.z + o.radius * sp * Math.cos(o.theta));
    cam.lookAt(o.target);
    this.scene.fog.near = o.radius * 1.8;
    this.scene.fog.far = o.radius * 5.5;
  }

  // ------------------------------------------------------------ shadows, picking, loop

  _fitShadow() {
    const box = new THREE.Box3();
    for (const it of this.items) {
      if (it.label) continue;
      const g = it.obj.geometry;
      if (!g.boundingBox) g.computeBoundingBox();
      box.expandByPoint(it.to.pos).expandByPoint(it.to.pos.clone().setY(it.to.pos.y + g.boundingBox.max.y * it.to.scale.y));
    }
    if (box.isEmpty()) box.set(new THREE.Vector3(-5, 0, -5), new THREE.Vector3(5, 1, 5));
    const center = box.getCenter(new THREE.Vector3()), R = Math.max(box.getSize(new THREE.Vector3()).length() / 2 + 2, 4);
    this.bounds = { center, radius: R };
    const s = this.sun.shadow.camera;
    s.left = s.bottom = -R; s.right = s.top = R; s.near = 0.1; s.far = R * 6;
    s.updateProjectionMatrix();
    this.sun.target.position.copy(center);
    this.sun.position.copy(center).addScaledVector(this.sunDir, -R * 3);
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

  /** Counts for tests and debugging. */
  stats() {
    return { meshes: this.items.filter((i) => !i.label).length, labels: this.items.filter((i) => i.label).length,
      pickables: new Set(this.items.filter((i) => i.pick).map((i) => i.pick)).size, highlights: this.highlights.size,
      animating: this.items.filter((i) => i.anim).length + this.dying.length, hover: this.hoverId };
  }

  setTable(visible) { this.table.visible = !!visible; }

  _resize() {
    const c = this.canvas, w = c.clientWidth | 0, h = c.clientHeight | 0;
    if (w && h && (c.width !== Math.floor(w * this.renderer.getPixelRatio()) || c.height !== Math.floor(h * this.renderer.getPixelRatio()))) {
      this.renderer.setSize(w, h, false);
      this.camera.aspect = w / h;
      this.camera.updateProjectionMatrix();
    }
  }

  _tick(now) {
    this._raf = requestAnimationFrame(this._tick);
    const dt = Math.min(0.1, (now - this._clock) / 1000);
    this._clock = now;
    this._resize();
    this._updateCamera(dt);
    this.camera.updateMatrixWorld();
    // hover
    const id = this.pointerInside ? this.pickAt(this.pointer.x, this.pointer.y) : 0;
    if (id !== this.hoverId) {
      this.hoverId = id;
      this.canvas.style.cursor = id ? 'pointer' : '';
      if (this.onHover) this.onHover(id);
    }
    const kh = 1 - Math.exp(-dt * 14);
    const t = performance.now();
    for (const it of this.items) {
      const h = it.pick && it.pick === id ? 1 : 0;
      it.hover = Math.abs(h - it.hover) < 1e-3 ? h : it.hover + (h - it.hover) * kh;
      const busy = it.anim || it.hover || it.dirty || this.highlights.has(it.pick);
      if (busy || it.wasBusy) this._apply(it, t);  // one extra frame to settle cosmetics
      it.wasBusy = !!busy;
      it.dirty = false;
    }
    this.dying = this.dying.filter((it) => {
      this._apply(it, t);
      if (it.anim) return true;
      this.root.remove(it.obj);
      it.obj.material.map?.dispose();
      it.obj.material.dispose();
      return false;
    });
    this.renderer.render(this.scene, this.camera);
  }

  dispose() {
    cancelAnimationFrame(this._raf);
    for (const g of this.geoms.values()) g.geo.dispose();
    this.renderer.dispose();
  }
}

export default GpuPlayer;
