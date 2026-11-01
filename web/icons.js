// The game's drawn marks, inline so the game works from a clean clone with nothing fetched.
// Each is a meaning, not decoration: a resource, a piece, a control, or a house's arms.
const NS = "http://www.w3.org/2000/svg";

function svg(viewBox, inner, cls) {
  const t = document.createElementNS(NS, "svg");
  t.setAttribute("viewBox", viewBox);
  t.setAttribute("aria-hidden", "true");
  if (cls) t.setAttribute("class", cls);
  t.innerHTML = inner;
  return t;
}

const RES = {
  grain: `<g fill="#a97c12"><path d="M12 2.2c1.4 1.3 1.4 3 0 4.5-1.4-1.5-1.4-3.2 0-4.500zM11.3 8.300c-.3-2-2-3.2-4.3-3 .3 2.2 2 3.4 4.3 3zM12.7 8.300c.3-2 2-3.2 4.3-3-.3 2.2-2 3.4-4.3 3zM11.3 12.800c-.3-2-2-3.2-4.3-3 .3 2.2 2 3.4 4.3 3zM12.7 12.800c.3-2 2-3.2 4.3-3-.3 2.2-2 3.4-4.3 3zM11.3 17.300c-.3-2-2-3.2-4.3-3 .3 2.2 2 3.4 4.3 3zM12.7 17.300c.3-2 2-3.2 4.3-3-.3 2.2-2 3.4-4.3 3z"/><rect x="11.2" y="6" width="1.6" height="16"/></g>`,
  timber: `<g><path d="M12 2 6.8 9.200h2.500L5.6 14.500h3L5 20h14l-3.6-5.500h3l-3.7-5.300h2.500z" fill="#2f5d38"/><rect x="10.8" y="19.5" width="2.4" height="3" fill="#5b3e26"/></g>`,
  ore: `<g><path d="M3 18.5 7 8.500l5.5-4.5 5 3.5 3.5 11z" fill="#6f747e"/><path d="m7 8.5 4 3 1.5-7.500zM11 11.500l6.5-4-5-3.500zM3 18.500l8-7 1 7zM12 18.500l-1-7 6.5-4L21 18.500z" fill="#8d929c"/><path d="m11 11.5 6.5-4L21 18.500h-9z" fill="#5b5f69"/></g>`,
  wool: `<g><path d="M6.5 16.500a3.3 3.3 0 0 1-.8-6.4 3.6 3.6 0 0 1 5.1-3 3.8 3.8 0 0 1 6 1.1 3.3 3.3 0 0 1 2.3 5.9 3 3 0 0 1-3.6 2.400z" fill="#f6f1e2" stroke="#6d7f3e" stroke-width="1.1"/><path d="M4.4 11.300c-1.5-.1-2.4 1-2.4 2.3 0 1.1.8 1.9 1.9 1.9.8 0 1.3-.3 1.8-.9z" fill="#3a302b"/><rect x="8" y="16.3" width="1.7" height="4.2" fill="#3a302b"/><rect x="14.3" y="16.3" width="1.7" height="4.2" fill="#3a302b"/></g>`,
  brick: `<g fill="#a9502e"><rect x="2.5" y="6" width="9" height="5"/><rect x="12.5" y="6" width="9" height="5"/><rect x="7.5" y="12" width="9" height="5" fill="#bd6239"/><rect x="2.5" y="12" width="4" height="5" fill="#8f4226"/><rect x="17.5" y="12" width="4" height="5" fill="#8f4226"/><rect x="2.5" y="18" width="9" height="3" fill="#8f4226"/><rect x="12.5" y="18" width="9" height="3" fill="#8f4226"/></g>`,
};
// The Belt's resources.
Object.assign(RES, {
  helium: `<circle cx="12" cy="12" r="8.500" fill="#b7a6e0" stroke="#5a4a78" stroke-width="1.400"/><circle cx="9.200" cy="9.200" r="2.200" fill="#efe9fb"/>`,
  alloy: `<path d="M3 17 8 7h13l-5 10z" fill="#a8b0bc" stroke="#5f6670" stroke-width="1.400"/><path d="M8 7 3 17" stroke="#fff" stroke-width="1"/>`,
  ice: `<path d="M12 2.500 19 8l-2 10-5 3.500L7 18 5 8z" fill="#d7ecf7" stroke="#5f93ad" stroke-width="1.400"/><path d="M12 2.500V21.500M5 8l14 0" stroke="#8dbdd4" stroke-width="1"/>`,
  crystal: `<path d="M12 2 18 9l-6 13L6 9z" fill="#d65fb8" stroke="#7a3e6e" stroke-width="1.400"/><path d="M6 9h12M12 2v20" stroke="#f3b6e0" stroke-width="1"/>`,
});
// Not Catan's own resources.
Object.assign(RES, {
  laurel: `<path d="M12 21C6 19 3.500 14 4 7.500c1.800.600 3 1.800 3.500 3.500M12 21c6-2 8.500-7 8-13.500-1.800.600-3 1.800-3.500 3.500" fill="none" stroke="#3f6b35" stroke-width="2"/><path d="M4.500 12.500c1.500-.2 2.700.3 3.500 1.500-1.500.400-2.700 0-3.500-1.500zM6.500 16.500c1.500-.5 2.800-.200 3.800 1-1.500.600-2.800.300-3.800-1zM19.500 12.500c-1.500-.2-2.700.3-3.500 1.500 1.500.400 2.700 0 3.500-1.500zM17.500 16.500c-1.500-.5-2.800-.200-3.800 1 1.500.600 2.800.300 3.800-1z" fill="#4f8042"/>`,
});
// A resource with no drawn mark still shows something: its first letter.
const letterMark = r => `<circle cx="12" cy="12" r="9" fill="#d3c295" stroke="#5f4f3b" stroke-width="1.400"/><text x="12" y="16.500" text-anchor="middle" font-size="12" font-family="serif" fill="#2a1f14">${String(r || "?")[0].toUpperCase()}</text>`;
export const resIcon = (r, cls = "res") => svg("0 0 24 24", RES[r] || letterMark(r), cls);

const UI = {
  quill: `<path d="M21 3c-6.5.4-11 3.7-13.2 9.2-.8 2-1.4 4.3-1.8 6.800l-2 2.5.9.9 2.2-2.200c2.7-.4 5-1 7-2-1.2-.2-2.2-.2-3-.1 1.2-.5 2.7-1.3 4.3-2.5-1-.1-1.9-.1-2.7.1 3.2-2.8 6-7.3 8.3-13.500z" fill="currentColor"/>`,
  seal: `<path d="M12 2.500c1.3 0 1.8 1 3 1.300s2.2-.3 3.2.5.7 1.8 1.4 2.8 1.8 1.3 2 2.6-.8 2-.8 3.2.8 2-.2 3.1-2 .9-3 1.6-1.2 1.9-2.5 2.3-2-.5-3.3-.5-2 .9-3.3.5-1.5-1.6-2.5-2.3-2.1-.5-3-1.6.2-2 -.2-3.1-1-2-.8-3.2 1.3-1.6 2-2.6.4-2 1.4-2.8 2-.2 3.2-.5 1.7-1.3 3-1.300z" fill="currentColor"/><circle cx="12" cy="12" r="5.3" fill="none" stroke="#00000055" stroke-width="1.2"/>`,
  book: `<path d="M4 4.500c3-1 5.8-.8 8 1 2.2-1.8 5-2 8-1v15c-3-1-5.8-.8-8 1-2.2-1.8-5-2-8-1z" fill="none" stroke="currentColor" stroke-width="1.7"/><path d="M12 5.500v15" stroke="currentColor" stroke-width="1.7"/>`,
  scroll: `<path d="M7 3.500h11a2 2 0 0 1 2 2V7h-3.500M7 3.500a2 2 0 0 0-2 2V18a2.5 2.5 0 0 1-2.5 0M7 3.500a2 2 0 0 1 2 2v13.500a2.5 2.5 0 0 1-2.5 2H16a2.5 2.5 0 0 0 2-2.500V7" fill="none" stroke="currentColor" stroke-width="1.7"/><path d="M11.5 9h4M11.5 12.500h4M11.5 16h3" stroke="currentColor" stroke-width="1.5"/>`,
  dots: `<circle cx="5" cy="12" r="1.9" fill="currentColor"/><circle cx="12" cy="12" r="1.9" fill="currentColor"/><circle cx="19" cy="12" r="1.9" fill="currentColor"/>`,
  trade: `<path d="M3.5 8h14m-4.5-4.500L17.5 8 13 12.500M20.5 16h-14m4.5-4.500L6.5 16l4.5 4.5" fill="none" stroke="currentColor" stroke-width="1.9"/>`,
  close: `<path d="m6 6 12 12M18 6 6 18" stroke="currentColor" stroke-width="2"/>`,
  talk: `<path d="M3.500 5h17v11h-9l-4.500 4v-4H3.500z" fill="none" stroke="currentColor" stroke-width="1.700"/><path d="M7.500 9h9M7.500 12.500h6" stroke="currentColor" stroke-width="1.500"/>`,
};
export const uiIcon = (n, cls = "ui") => svg("0 0 24 24", UI[n] || "", cls);

const PIECE = {
  road: `<path d="M3 19 18 4l3 3L6 22z" fill="currentColor"/><path d="m10 12 2 2m2-6 2 2m-10 6 2 2" stroke="#00000066" stroke-width="1.3"/>`,
  settlement: `<path d="M3 21v-8l6-5 6 5v8z" fill="currentColor"/><path d="M15 21v-6l3-2.5 3 2.500v6z" fill="currentColor" opacity=".72"/><path d="M7.5 21v-4h3v4z" fill="#00000066"/>`,
  city: `<path d="M2.5 21V10h2V8h1.500v2h1.500V8h1.500v2h2v11z" fill="currentColor"/><path d="M11.5 21V6.500L15 2.500l3.5 4V21z" fill="currentColor" opacity=".8"/><path d="M18.5 21v-8h3v8z" fill="currentColor"/><path d="M14 21v-4h2v4z" fill="#00000066"/>`,
  made: `<path d="M12 2.5 14 7h-4zM9.5 8h5l1 11h3v2.500H5.500V19h3z" fill="currentColor"/><path d="M11 10h2v8h-2z" fill="#00000044"/>`,
};
// The Belt's pieces have the same roles as the Island's, so they share marks.
Object.assign(PIECE, { lane: PIECE.road, outpost: PIECE.settlement, station: PIECE.city });
// Not Catan's pieces.
Object.assign(PIECE, {
  knight: `<path d="M12 2.500 14 7h-4zM6 8h12v3c0 5-2.500 9-6 11-3.500-2-6-6-6-11z" fill="currentColor"/><path d="M12 10v8M9 13h6" stroke="#00000066" stroke-width="1.600"/>`,
  relic: `<path d="M5 21v-2h2l1.500-9h7L17 19h2v2zM9 8a3 3 0 1 1 6 0z" fill="currentColor"/><path d="M12 12v5" stroke="#00000066" stroke-width="1.600"/>`,
  wreath: `<path d="M12 21C6 19 3.500 14 4 6.500c2.500.800 4 2.500 4.500 5M12 21c6-2 8.500-7 8-14.500-2.500.800-4 2.500-4.500 5" fill="none" stroke="currentColor" stroke-width="2.600"/>`,
});
export const pieceIcon = (k, cls = "piece") => svg("0 0 24 24", PIECE[k] || PIECE.made, cls);

// Each house has a charge as well as a colour, so colour is never the only cue.
const CHARGE = [
  `<path d="M0 44 30 22l30 22v12L30 34 0 56z" fill="#f4ecd8"/>`,                       // chevron
  `<rect x="22" y="0" width="16" height="84" fill="#f4ecd8"/>`,                        // pale
  `<rect x="0" y="20" width="60" height="12" fill="#2a2017"/><rect x="0" y="42" width="60" height="12" fill="#2a2017"/>`, // bars
  `<path d="M0 8 8 0l60 60-8 8zM0 40 8 32l40 40-8 8z" fill="#f4ecd8"/>`,               // bends
  `<path d="M0 8 8 0l52 60-8 8zM60 8l-8-8L0 60l8 8z" fill="#f4ecd8"/>`,                // saltire
  `<rect x="24" y="0" width="12" height="84" fill="#f4ecd8"/><rect x="0" y="26" width="60" height="12" fill="#f4ecd8"/>`, // cross
];
export const chargeOf = seat => CHARGE[seat % CHARGE.length];

/** A small shield with a house's colour and charge. */
export function shield(seat, color, cls = "shield") {
  // Clipped by CSS (.shield), so a copy of a document keeps its arms.
  return svg("0 0 60 70",
    `<rect width="60" height="70" fill="${color}"/>${chargeOf(seat)}` +
    `<path d="M1.5 1.5h57v37L30 68.5 1.5 38.5z" fill="none" stroke="#1c120b" stroke-width="3"/>`, cls);
}

/** The wax seal stamped on an enacted law. */
export function waxSeal(cls = "wax") {
  return svg("0 0 100 100",
    `<path d="M50 4c7 0 9 6 15 8s12-1 17 4 2 11 5 16 10 7 10 15-7 10-8 16 3 13-3 18-12 2-18 5-9 10-17 10-10-7-16-9-13 0-18-6-2-12-5-17-10-8-9-16 8-10 9-16-2-12 4-17 12-1 17-4 8-7 17-7z" fill="#8f1f17"/>` +
    `<path d="M50 4c7 0 9 6 15 8s12-1 17 4 2 11 5 16 10 7 10 15" fill="none" stroke="#c9483c" stroke-width="2"/>` +
    `<circle cx="50" cy="50" r="28" fill="#7c1812" stroke="#5e100c" stroke-width="2"/>` +
    `<path d="M50 28 54 39 66 39 56 46 60 58 50 51 40 58 44 46 34 39 46 39z" fill="#b8352a"/>`, cls);
}
