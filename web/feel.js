// How the table reacts. Two tools keep motion honest while the view is polled:
// - `morphKids` updates a row in place, so a new view never restarts what is moving, and never takes a
//   button away in the middle of a press.
// - `anim` is the only way to start a one-time motion. It runs when something calls it, and renders do
//   not call it, so a motion fires once per real event. Input is never held up: nothing here waits.
export const reduced = () => matchMedia("(prefers-reduced-motion: reduce)").matches;

/** Start a motion, unless the player asked for none. It moves with `translate`, `scale` and `rotate`,
 *  which add to an element's own transform and are cheap to draw. */
export function anim(el, frames, opts) {
  return !el || reduced() ? null : el.animate(frames, { easing: "cubic-bezier(.2,.9,.3,1)", ...opts });
}

function morph(to, from) {
  if (to === from || to.isEqualNode(from)) return;
  if (to.nodeType === Node.TEXT_NODE) { to.data = from.data; return; }
  for (const a of [...to.attributes]) if (!from.hasAttribute(a.name)) to.removeAttribute(a.name);
  for (const a of from.attributes) if (to.getAttribute(a.name) !== a.value) to.setAttribute(a.name, a.value);
  morphKids(to, [...from.childNodes]);
}
/** Make `parent` hold `kids`, keeping the nodes it can. A child matches by `data-key`, otherwise by its
 *  tag and order. A kept node keeps its listeners, so give a key to anything whose handler can change. */
export function morphKids(parent, kids) {
  kids = kids.flat(9).filter(k => k != null && k !== false);
  const keyed = new Map(), loose = [];
  for (const n of parent.childNodes) { if (n.dataset?.key != null) keyed.set(n.dataset.key, n); else loose.push(n); }
  kids.forEach((k, i) => {
    let n;
    if (k.dataset?.key != null) n = keyed.get(k.dataset.key);
    else { const j = loose.findIndex(x => x.nodeName === k.nodeName); if (j >= 0) n = loose.splice(j, 1)[0]; }
    if (n?.nodeName !== k.nodeName) n = null;
    if (n) { keyed.delete(k.dataset?.key); morph(n, k); }
    const node = n || k;
    if (parent.childNodes[i] !== node) parent.insertBefore(node, parent.childNodes[i] ?? null);
  });
  while (parent.childNodes.length > kids.length) parent.lastChild.remove();
}

/** Put something on top of the table for `life` ms, then take it away. It takes no clicks. */
export function spawn(node, life) {
  document.body.append(node);
  setTimeout(() => node.remove(), life);
  return node;
}

/** The middle of an element, on the screen. */
export function middleOf(el) {
  const r = el.getBoundingClientRect();
  return { x: r.left + r.width / 2, y: r.top + r.height / 2 };
}

/** A small jolt, as if something heavy landed on what `el` shows. */
export const thump = (el, px = 2, delay = 0) =>
  anim(el, [{ translate: "0 0" }, { translate: `0 ${px}px` }, { translate: `0 ${-px / 3}px` }, { translate: "0 0" }], { duration: 190, delay, easing: "ease-out" });
