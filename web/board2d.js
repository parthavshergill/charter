// The 2D fallback board. It draws the server's view and turns a click on a marked spot into the
// pick id of the matching legal moves, the same id the 3D player reports.
const NS = "http://www.w3.org/2000/svg";
export const SCALE = 52;

function el(tag, attrs, parent) {
  const n = document.createElementNS(NS, tag);
  for (const k in attrs) n.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(n);
  return n;
}

/** One finger pans and two fingers pinch, by moving the viewBox. The drawing is never redone for it. */
function bindGestures(svg) {
  if (svg.dataset.gestures) return;
  svg.dataset.gestures = "1";
  svg.style.touchAction = "none";
  const ptrs = new Map();
  let pinch = 0;
  const box = () => svg.viewBox.baseVal;
  const zoom = (f, x, y) => {
    const b = box(), home = svg._home, w = Math.min(home.w, Math.max(home.w / 4, b.width / f)), h = w * home.h / home.w;
    const r = svg.getBoundingClientRect(), px = (x - r.left) / r.width, py = (y - r.top) / r.height;
    const nx = b.x + (b.width - w) * px, ny = b.y + (b.height - h) * py;
    svg.setAttribute("viewBox", `${nx} ${ny} ${w} ${h}`);
    clamp();
  };
  const clamp = () => {
    const b = box(), home = svg._home;
    svg.setAttribute("viewBox", `${Math.max(home.x, Math.min(home.x + home.w - b.width, b.x))} ${Math.max(home.y, Math.min(home.y + home.h - b.height, b.y))} ${b.width} ${b.height}`);
    svg._box = svg.getAttribute("viewBox");
  };
  svg.addEventListener("pointerdown", e => {
    if (e.pointerType === "mouse") return;
    svg.setPointerCapture?.(e.pointerId);
    ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY, x0: e.clientX, y0: e.clientY, moved: false });
    if (ptrs.size === 2) { const [a, b] = [...ptrs.values()]; pinch = Math.hypot(a.x - b.x, a.y - b.y); a.moved = b.moved = true; }
  });
  svg.addEventListener("pointermove", e => {
    const p = ptrs.get(e.pointerId);
    if (!p) return;
    const dx = e.clientX - p.x, dy = e.clientY - p.y;
    p.x = e.clientX; p.y = e.clientY;
    if (Math.hypot(p.x - p.x0, p.y - p.y0) > 8) p.moved = true;
    if (ptrs.size === 2) {
      const [a, b] = [...ptrs.values()], d = Math.hypot(a.x - b.x, a.y - b.y);
      if (pinch) zoom(d / pinch, (a.x + b.x) / 2, (a.y + b.y) / 2);
      pinch = d;
    } else if (p.moved) {
      const v = box(), r = svg.getBoundingClientRect(), k = v.width / r.width;
      svg.setAttribute("viewBox", `${v.x - dx * k} ${v.y - dy * k} ${v.width} ${v.height}`);
      clamp();
    }
  });
  const end = e => {
    const p = ptrs.get(e.pointerId);
    ptrs.delete(e.pointerId);
    if (ptrs.size < 2) pinch = 0;
    // A finger that travelled was panning, and the click it ends with is not a pick.
    if (p?.moved) svg._dragged = performance.now();
  };
  svg.addEventListener("pointerup", end);
  svg.addEventListener("pointercancel", end);
}

export function renderBoard2D(svg, view, seatColor, onPick) {
  svg.innerHTML = "";
  bindGestures(svg);
  const b = view.board;
  const xy = p => [p.x * SCALE, p.y * SCALE];
  // The board's own size, since a pack can draw a board of any size.
  const xs = b.tiles.map(t => t.x), ys = b.tiles.map(t => t.y);
  const x0 = Math.min(...xs) - 1.25, x1 = Math.max(...xs) + 1.25, y0 = Math.min(...ys) - 1.25, y1 = Math.max(...ys) + 1.25;
  const home = { x: x0 * SCALE, y: y0 * SCALE, w: (x1 - x0) * SCALE, h: (y1 - y0) * SCALE };
  const same = svg._home && svg._home.w === home.w && svg._home.h === home.h && svg._home.x === home.x && svg._home.y === home.y;
  svg._home = home;
  // A redraw keeps where the person has moved to.
  svg.setAttribute("viewBox", same && svg._box ? svg._box : `${home.x} ${home.y} ${home.w} ${home.h}`);
  const pickFor = pick => () => { if (!(performance.now() - (svg._dragged || -1000) < 80)) onPick(pick); };
  for (const t of b.tiles) {
    const [cx, cy] = xy(t);
    const pts = [0, 1, 2, 3, 4, 5].map(i => {
      const a = Math.PI / 180 * (60 * i - 90);
      return `${cx + SCALE * Math.cos(a)},${cy + SCALE * Math.sin(a)}`;
    }).join(" ");
    el("polygon", { points: pts, fill: t.color || "#f0d9a0", stroke: "#f3e6c8", "stroke-width": 3 }, svg);
    if (t.number != null) {
      el("circle", { cx, cy, r: 15, fill: view.lastRoll === t.number ? "#ffd23f" : "#fbf3df", stroke: "#8c785f" }, svg);
      const n = el("text", { x: cx, y: cy + 6, "text-anchor": "middle", "font-size": 17, "font-weight": 700, fill: "#2a2017" }, svg);
      n.textContent = t.number;
    }
    const lbl = el("text", { x: cx, y: cy + SCALE * 0.62, "text-anchor": "middle", "font-size": 9, fill: "rgba(0,0,0,.55)", "font-weight": 600 }, svg);
    lbl.textContent = (t.res || "").toUpperCase();
  }
  const spot = v => xy(b.spots[v]);
  for (const p of view.pieces || []) {
    const col = seatColor(p.owner);
    if (p.link) {
      const [x1, y1] = spot(p.link[0]), [x2, y2] = spot(p.link[1]);
      el("line", { x1, y1, x2, y2, stroke: "#1d140e", "stroke-width": 10, "stroke-linecap": "round" }, svg);
      el("line", { x1, y1, x2, y2, stroke: col, "stroke-width": 7, "stroke-linecap": "round" }, svg);
    }
  }
  for (const p of view.pieces || []) {
    if (p.spot == null) continue;
    const [x, y] = spot(p.spot);
    // Bigger is worth more, and the letter says which piece it is, whatever a pack calls its pieces.
    const worth = (view.pieceDefs || []).find(d => d.name === p.kind)?.points || 0, size = worth > 1 ? 13 : 10;
    el("rect", { x: x - size, y: y - size, width: 2 * size, height: 2 * size, rx: 3, fill: seatColor(p.owner), stroke: "#1d140e", "stroke-width": 2 }, svg);
    const t = el("text", { x, y: y + 4, "text-anchor": "middle", "font-size": 11, fill: "#fff", "font-weight": 700 }, svg);
    t.textContent = p.kind[0].toUpperCase();
  }
  const seen = new Set();
  for (const m of view.legalMoves || []) {
    if (m.pick == null || seen.has(m.pick)) continue;
    seen.add(m.pick);
    let node, reach;
    if (m.move.spot != null) {
      const [cx, cy] = spot(m.move.spot);
      node = el("circle", { cx, cy, r: 10, fill: "#ffc83d", "fill-opacity": .75, stroke: "#fff", "stroke-width": 2.5 }, svg);
      reach = el("circle", { cx, cy, r: 24, fill: "transparent" }, svg);
    } else {
      const [x1, y1] = spot(m.move.link[0]), [x2, y2] = spot(m.move.link[1]);
      node = el("line", { x1, y1, x2, y2, stroke: "#ffc83d", "stroke-opacity": .8, "stroke-width": 9, "stroke-linecap": "round" }, svg);
      reach = el("line", { x1, y1, x2, y2, stroke: "transparent", "stroke-width": 30, "stroke-linecap": "round" }, svg);
    }
    // A fingertip is wider than the mark, so a wider shape that cannot be seen takes the tap.
    for (const n of [node, reach]) {
      n.style.cursor = "pointer";
      el("title", {}, n).textContent = m.label;
      n.addEventListener("click", pickFor(m.pick));
    }
  }
}
