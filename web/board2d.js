// The 2D fallback board. It draws the server's view and turns a click on a marked spot into the
// pick id of the matching legal moves, the same id the 3D player reports.
const NS = "http://www.w3.org/2000/svg";
const SCALE = 52;
const RES_COLOR = { grain: "#f5c518", timber: "#2f9e44", ore: "#8fa3c4", wool: "#9be15d", brick: "#e0612a", helium: "#8e7cc3", alloy: "#8c95a3", ice: "#9cc4d8", crystal: "#b05a9c" };

function el(tag, attrs, parent) {
  const n = document.createElementNS(NS, tag);
  for (const k in attrs) n.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(n);
  return n;
}

export function renderBoard2D(svg, view, seatColor, onPick) {
  svg.innerHTML = "";
  const b = view.board;
  const xy = p => [p.x * SCALE, p.y * SCALE];
  svg.setAttribute("viewBox", `${-5.2 * SCALE} ${-4.6 * SCALE} ${10.4 * SCALE} ${9.2 * SCALE}`);
  for (const t of b.tiles) {
    const [cx, cy] = xy(t);
    const pts = [0, 1, 2, 3, 4, 5].map(i => {
      const a = Math.PI / 180 * (60 * i - 90);
      return `${cx + SCALE * Math.cos(a)},${cy + SCALE * Math.sin(a)}`;
    }).join(" ");
    el("polygon", { points: pts, fill: RES_COLOR[t.res] || "#f0d9a0", stroke: "#f3e6c8", "stroke-width": 3 }, svg);
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
    const size = p.kind === "settlement" ? 9 : 13;
    el("rect", { x: x - size, y: y - size, width: 2 * size, height: 2 * size, rx: 3, fill: seatColor(p.owner), stroke: "#1d140e", "stroke-width": 2 }, svg);
    if (p.kind !== "settlement") {
      const t = el("text", { x, y: y + 4, "text-anchor": "middle", "font-size": 11, fill: "#fff", "font-weight": 700 }, svg);
      t.textContent = p.kind[0].toUpperCase();
    }
  }
  const seen = new Set();
  for (const m of view.legalMoves || []) {
    if (m.pick == null || seen.has(m.pick)) continue;
    seen.add(m.pick);
    let node;
    if (m.move.spot != null) {
      const [cx, cy] = spot(m.move.spot);
      node = el("circle", { cx, cy, r: 10, fill: "#ffc83d", "fill-opacity": .75, stroke: "#fff", "stroke-width": 2.5 }, svg);
    } else {
      const [x1, y1] = spot(m.move.link[0]), [x2, y2] = spot(m.move.link[1]);
      node = el("line", { x1, y1, x2, y2, stroke: "#ffc83d", "stroke-opacity": .8, "stroke-width": 9, "stroke-linecap": "round" }, svg);
    }
    node.style.cursor = "pointer";
    el("title", {}, node).textContent = m.label;
    node.addEventListener("click", () => onPick(m.pick));
  }
}
