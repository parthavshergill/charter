// A pack's look off the board. It arrives as data, and nothing here trusts it: each value is checked
// and is dropped if it is not of the one form it may have. So a pack can set colours, choose a font and
// draw marks. It cannot run a script. The words and structure of the screens do not come from here.
import { setIconLook } from "./icons.js";

// The colour tokens at the top of app.css. Nothing else can be set.
const TOKENS = new Set(["walnut-0", "walnut-1", "walnut-2", "walnut-3", "brass", "vellum", "vellum-2", "vellum-3",
  "ink", "ink-2", "ink-3", "gold", "gold-2", "gold-ink", "wax", "wax-2", "wax-0", "pale", "pale-2",
  "sign-ink", "act-hover", "act-hover-2", "field", "bright", "err-ink", "tool-off", "need", "good", "stain",
  "roll-0", "roll-1", "roll-2", "roll-3", "roll-4", "roll-5", "roll-6", "roll-7", "roll-8"]);
// The fixed list of fonts. These are on the player's machine, so nothing is fetched.
const FONTS = {
  book: 'Palatino, "Palatino Linotype", "Book Antiqua", "Iowan Old Style", Georgia, serif',
  slab: 'Rockwell, "Roboto Slab", "Courier New", Georgia, serif',
  humanist: '"Avenir Next", Avenir, Optima, Candara, "Segoe UI", sans-serif',
  rounded: '"SF Pro Rounded", ui-rounded, "Hiragino Maru Gothic ProN", "Arial Rounded MT Bold", "Trebuchet MS", sans-serif',
  typewriter: '"American Typewriter", "Courier Prime", "Courier New", monospace',
};
const HEX = /^#[0-9a-fA-F]{6}$/;
const PATH = /^[MmLlHhVvCcSsQqTtAaZz0-9eE.,+\- ]{1,4000}$/;
const paint = v => v === "none" || v === "currentColor" || HEX.test(v);
const inRange = (v, lo, hi) => typeof v === "number" && Number.isFinite(v) && v >= lo && v <= hi;

/** One shape of a mark as attributes to set, or null if any part of it is not allowed. */
function pathAttrs(p) {
  if (!p || !PATH.test(p.d) || !paint(p.fill) || !paint(p.stroke) || !inRange(p.width, 0, 8) || !inRange(p.opacity, 0, 1)) return null;
  const a = { d: p.d, fill: p.fill, stroke: p.stroke, "stroke-linecap": "round", "stroke-linejoin": "round" };
  if (p.width > 0) a["stroke-width"] = String(p.width);
  if (p.opacity < 1) a.opacity = String(p.opacity);
  return a;
}

function checkedIcons(icons) {
  const out = Object.create(null);
  for (const [name, paths] of Object.entries(icons || {})) {
    const attrs = Array.isArray(paths) ? paths.slice(0, 16).map(pathAttrs) : [];
    if (attrs.length && attrs.every(Boolean)) out[name] = attrs;
    else console.warn(`look: the mark for ${name} is not allowed, so it is left out`);
  }
  return out;
}

let shown = null, set = [];
/** Show this look. A value that is left out goes back to the one in app.css. */
export function applyLook(look) {
  const key = JSON.stringify(look ?? null);
  if (key === shown) return;
  shown = key;
  const root = document.documentElement.style;
  for (const name of set) root.removeProperty(name);
  set = [];
  const put = (name, value) => { root.setProperty(name, value); set.push(name); };
  for (const [k, v] of Object.entries(look?.tokens || {})) {
    if (TOKENS.has(k) && HEX.test(v)) put(`--${k}`, v);
    else console.warn(`look: ${k} is not a colour token this page can set`);
  }
  if (Object.hasOwn(FONTS, look?.bodyFont ?? "")) put("--serif", FONTS[look.bodyFont]);
  if (Object.hasOwn(FONTS, look?.displayFont ?? "")) put("--brand-text", FONTS[look.displayFont]);
  setIconLook(checkedIcons(look?.icons), Object.assign(Object.create(null), look?.marks));
}
