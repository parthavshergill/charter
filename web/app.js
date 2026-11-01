// The Charter client. It shows what the server sends and holds no game rules: every move it posts
// comes from `view.legalMoves` or from text the engine then accepts or rejects, and every cost, reason
// and deal statement is written by Lean. A law's description is Claude's or a pack's words, and the law's
// source below it is what counts. What is here is presentation: what to show, when, and where.
import { renderBoard2D, SCALE } from "./board2d.js";
import { resIcon, uiIcon, pieceIcon, shield, chargeOf, waxSeal } from "./icons.js";
import { reduced, anim, morphKids, spawn, middleOf, thump } from "./feel.js";
import { applyLook } from "./look.js";
import { CONSTITUTION } from "./constitution.js";

const app = document.getElementById("app");
const params = new URLSearchParams(location.search);
const DEFAULT_COLORS = ["#b5281f", "#2257ae", "#e39a1b", "#1c8560", "#6f42a8", "#c4507f"];
const seatColor = i => (G.view?.seatColors || DEFAULT_COLORS)[i % 6];
const manyOf = w => w.endsWith("y") ? `${w.slice(0, -1)}ies` : `${w}s`;
const plural = (n, w) => `${n} ${n === 1 ? w : manyOf(w)}`;
const capital = s => s ? s[0].toUpperCase() + s.slice(1) : s;

function h(tag, attrs = {}, ...kids) {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v == null || v === false) continue;
    if (k === "class") n.className = v;
    else if (k.startsWith("on")) n.addEventListener(k.slice(2), v);
    else if (k === "style" && typeof v === "object") Object.assign(n.style, v);
    else if (k === "value") n.value = v;
    else n.setAttribute(k, v === true ? "" : v);
  }
  for (const k of kids.flat(9)) if (k != null && k !== false) n.append(k.nodeType ? k : String(k));
  return n;
}
const fill = (n, ...kids) => n.replaceChildren(...kids.flat(9).filter(k => k != null && k !== false));
// The seat token goes in a header, not the address, so it stays out of anything that logs addresses.
let seatToken = null;
async function api(path, body) {
  const headers = seatToken ? { "X-Charter-Token": seatToken } : {};
  const opt = body === undefined ? { headers } : { method: "POST", headers: { ...headers, "Content-Type": "application/json" }, body: JSON.stringify(body) };
  const r = await fetch(path, opt);
  const ct = r.headers.get("content-type") || "";
  return ct.includes("json") ? r.json() : r.arrayBuffer();
}
const store = {
  get: k => { try { return localStorage.getItem(k); } catch { return null; } },
  set: (k, v) => { try { localStorage.setItem(k, v); } catch {} },
  del: k => { try { localStorage.removeItem(k); } catch {} },
};
const tokenKey = code => `charter.token.${code}`;
const costOf = (b, cls = "small") => h("span", { class: "cost" }, (b || []).map(x => h("span", {}, String(x.n), resIcon(x.res, `res ${cls}`))));
const costText = b => (b || []).map(x => `${x.n} ${x.res}`).join(", ");
const ROUND_WORDS = ["", "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth", "tenth", "eleventh", "twelfth", "thirteenth", "fourteenth", "fifteenth", "sixteenth", "seventeenth", "eighteenth", "nineteenth", "twentieth"];

// ---------------------------------------------------------------- the 3D table
async function loadPlayer(canvas) {
  try {
    const mod = await import("./vendor/player.js");
    return new mod.GpuPlayer(canvas, {
      hoverFx: id => id < 3000 || id >= 9000,
      clickable: id => id < 3000 || id >= 9000,
    });
  } catch (e) { console.warn("3D table unavailable:", e); return null; }
}

/** This player's share of the dice seed, from the browser's own random source. The server does not
 *  choose it: that is the point of it. 52 bits fit a JSON number exactly. */
function myNonce() {
  const [a, b] = crypto.getRandomValues(new Uint32Array(2));
  return (a & 0xfffff) * 2 ** 32 + b;
}

// ---------------------------------------------------------------- the scroll
/** The document a table is founded on: a sheet, with a roller and the seal at its foot. */
const scrollSheet = (...kids) => h("div", { class: "scroll" },
  h("div", { class: "titlepage vellum" }, kids),
  h("div", { class: "roller", "aria-hidden": "true" }, h("span", { class: "roll" }), waxSeal("seal")));

/** Open the scroll once. A first visit waits for the board and takes the whole fall and unroll; any other
 *  visit takes a short unroll. The animation only hides the form: it can be typed in throughout, and any
 *  key, click or focus inside the sheet opens it at once. Returns the call that starts a waiting scroll. */
function openScroll(scroll, whole) {
  const finish = () => {
    scroll.classList.remove("opening", "whole", "waiting");
    document.removeEventListener("keydown", finish, true);
    document.removeEventListener("pointerdown", finish, true);
    scroll.removeEventListener("focusin", focused);
    scroll.removeEventListener("animationend", ended);
  };
  const ended = e => { if (e.target.classList.contains("roller")) finish(); };
  // The name line may already hold the focus, and its event can arrive late, when the window gains focus.
  const held = document.activeElement;
  const focused = e => { if (e.target !== held) finish(); };
  scroll.classList.add("opening");
  if (whole) scroll.classList.add("whole", "waiting");
  document.addEventListener("keydown", finish, true);
  document.addEventListener("pointerdown", finish, true);
  scroll.addEventListener("focusin", focused);
  scroll.addEventListener("animationend", ended);
  return () => scroll.classList.remove("waiting");
}
const TURN_MS = 520; // as .scroll.turning in app.css

// ---------------------------------------------------------------- the constitution
/** What the game promises a player, as one short document, on the title scroll and in the dock. The words
 *  are in constitution.js. Each promise opens to its theorem's name and any small print. */
const constitutionDoc = (...after) => h("div", { class: "constitution" },
  h("h2", { tabindex: "-1" }, CONSTITUTION.heading),
  h("p", { class: "opening" }, CONSTITUTION.opening),
  h("ol", { class: "promises" }, CONSTITUTION.promises.map(p => h("li", {},
    h("details", { name: "promise", "data-n": p.n },
      h("summary", {}, h("span", { class: "numeral" }, p.n), h("span", { class: "promise" }, p.line)),
      h("div", { class: "behind" }, h("code", {}, p.theorem.split(/(?<=_)/).map(w => [w, h("wbr")])), p.small ? h("p", {}, p.small) : null))))),
  h("p", { class: "notpromised" }, CONSTITUTION.notPromised),
  after);

// ---------------------------------------------------------------- title page
async function lobby() {
  const stage = h("div", { class: "stage" }, h("canvas"), h("div", { class: "vignette" }));
  let seats = 4;
  const name = h("input", { class: "signline", "aria-label": "Your name", value: store.get("charter.name") || "", autocomplete: "off", spellcheck: "false", autocapitalize: "words" });
  const joinCode = h("input", { class: "input", placeholder: "Code", "aria-label": "Table code", maxlength: 5, value: params.get("join") || "" });
  const err = h("div", { class: "errline", role: "status" });
  const seatButtons = [2, 3, 4].map(n =>
    h("button", { "data-n": n, onclick: () => { seats = n; showSeats(); } }, String(n)));
  const seg = h("div", { class: "seg" }, h("span", { class: "smallcaps lbl" }, "Seats"), seatButtons);
  // The games come from the server's list. The first is the base game, and it is the default.
  let game = null, defs = [];
  const showSeats = () => {
    const d = defs.find(x => x.id === game);
    const fits = n => !d || (d.minSeats <= n && n <= d.maxSeats);
    if (!fits(seats)) seats = Math.min(Math.max(seats, d.minSeats), d.maxSeats);
    for (const b of seatButtons) {
      const n = Number(b.dataset.n);
      b.classList.toggle("on", n === seats);
      b.setAttribute("aria-pressed", n === seats);
      b.disabled = !fits(n);
      b.title = fits(n) ? "" : `${d.name} has ${d.minSeats} to ${d.maxSeats} seats`;
    }
  };
  showSeats();
  const packList = h("div", { class: "packs", role: "group", "aria-label": "World" });
  const packNote = h("p", { class: "packnote" });
  // The chosen game's line and empty board. The base game is first, so the sheet starts with its line.
  const tagline = h("p", { class: "sub" }, "Settle an island. Rewrite its rules. The constitution holds.");
  let stagePlayer = null, stageShown = null, stageLoad = null;
  const showBackdrop = d => {
    if (!stagePlayer) return null;
    if (stageShown === d.id) return stageLoad;
    stageShown = d.id;
    return (stageLoad = api(`/api/defs/${d.id}/scene`).then(buf => { if (stageShown === d.id && buf.byteLength > 4) stagePlayer.render(buf); }));
  };
  // The row shows the first three games, and the chosen game if it is further along.
  // Every game after the first three is on the Library's shelf.
  const libraryLink = h("button", { class: "link library", onclick: () => turnTo("shelf") }, "Library");
  const showPacks = () => {
    const row = defs.filter((d, i) => i < 3 || d.id === game);
    fill(packList, h("span", { class: "smallcaps lbl" }, "World"), row.map(d =>
      h("button", { class: "pack" + (d.id === game ? " on" : ""), "aria-pressed": d.id === game ? "true" : "false", onclick: () => { game = d.id; showPacks(); showSeats(); packList.querySelector(".pack.on").focus(); } }, d.name)), libraryLink);
    packNote.textContent = defs.find(d => d.id === game)?.blurb || "";
    const d = defs.find(x => x.id === game);
    if (d) { applyLook(d.look); tagline.textContent = d.look.tagline; showBackdrop(d); }
  };
  showPacks();
  const defsLoaded = api("/api/defs").then(list => { defs = list; game = list[0]?.id ?? null; showPacks(); showSeats(); });
  const seatRange = d => d.minSeats === d.maxSeats ? plural(d.minSeats, "seat") : `${d.minSeats} to ${d.maxSeats} seats`;
  // One row of the shelf. A picture can go after .shelftext later: the row leaves no gap without one.
  const shelfRow = d => h("button", { class: "shelfrow" + (d.id === game ? " on" : ""), "aria-pressed": d.id === game ? "true" : "false", onclick: () => { game = d.id; showPacks(); showSeats(); turnTo("form", () => packList.querySelector(".pack.on")); } },
    waxSeal("seal small"),
    h("span", { class: "shelftext" }, h("span", { class: "shelfname" }, d.name), h("span", { class: "shelfblurb" }, d.blurb), h("span", { class: "smallcaps" }, seatRange(d))));
  const libraryHead = h("h2", { tabindex: "-1" }, "Library");
  const shelf = h("div", { class: "shelf", hidden: true, onkeydown: e => { if (e.key === "Escape") turnTo("form"); } });
  const showShelf = () => {
    const rest = defs.slice(3);
    fill(shelf, libraryHead,
      rest.length ? h("div", { class: "shelflist" }, rest.map(shelfRow)) : h("p", { class: "shelfempty" }, "No charters are shelved here yet."),
      h("button", { class: "link shelfback", onclick: () => turnTo("form") }, "Back to the charter"));
  };
  // The numerals on the sheet open the constitution at that promise, and going back returns to the numeral.
  let cameFrom = null;
  const backFromPromises = () => turnTo("form", () => cameFrom);
  const promises = h("div", { class: "promisesheet", hidden: true, onkeydown: e => { if (e.key === "Escape") backFromPromises(); } },
    constitutionDoc(h("button", { class: "link shelfback", onclick: backFromPromises }, "Back to the charter")));
  const openPromise = (n, from) => {
    cameFrom = from;
    for (const x of promises.querySelectorAll("details")) { x.open = false; x.classList.toggle("here", x.dataset.n === n); }
    turnTo("promises", () => promises.querySelector(".here summary"));
  };
  const numeralKeys = e => {
    const all = [...e.currentTarget.children], at = all.indexOf(document.activeElement);
    const to = e.key === "ArrowRight" ? at + 1 : e.key === "ArrowLeft" ? at - 1 : -1;
    if (all[to]) { e.preventDefault(); all[at].tabIndex = -1; all[to].tabIndex = 0; all[to].focus(); }
  };
  // Change between the form and the Library: the sheet rolls up and comes down again with the other side.
  // Its top stays where it is. The Library is never taller than the form, so a long list scrolls inside it.
  // The constitution takes the height it needs, down to the window's foot, and scrolls only past that.
  let turning = false;
  const turnTo = (side, focusTarget) => {
    if (turning) return;
    const sheet = page.firstChild;
    const toLibrary = side === "shelf", away = side !== "form";
    const swap = () => {
      turning = false;
      if (away) {
        const top = page.getBoundingClientRect().top;
        Object.assign(page.style, { top: `${top}px`, transform: "none", maxHeight: `calc(100dvh - ${top + 36}px)` });
        if (toLibrary) { sheet.style.maxHeight = `${sheet.offsetHeight}px`; showShelf(); }
      } else page.style.top = page.style.transform = page.style.maxHeight = sheet.style.maxHeight = "";
      page.classList.toggle("shelved", toLibrary);
      form.hidden = away; shelf.hidden = !toLibrary; promises.hidden = side !== "promises";
      sheet.scrollTop = 0;
      if (toLibrary) shelf.querySelector(".shelfrow.on")?.scrollIntoView({ block: "nearest" });
      if (side === "promises") promises.querySelector(".here")?.scrollIntoView({ block: "center" });
      (focusTarget?.() ?? (toLibrary ? libraryHead : libraryLink)).focus({ preventScroll: true });
    };
    if (reduced()) { swap(); return; }
    turning = true;
    page.classList.add("turning");
    setTimeout(swap, TURN_MS / 2);
    setTimeout(() => page.classList.remove("turning"), TURN_MS);
  };
  const nameOk = () => {
    const v = name.value.trim();
    if (!v) { err.textContent = "A player needs a name."; name.focus(); return false; }
    store.set("charter.name", v); err.textContent = ""; return true;
  };
  const join = async code => {
    code = code.trim().toUpperCase();
    if (!code) { err.textContent = "Enter a table code."; joinCode.focus(); return; }
    const r = await api(`/api/games/${code}/join`, { name: name.value.trim(), token: store.get(tokenKey(code)) || undefined, nonce: myNonce() });
    if (!r.ok) { err.textContent = r.error || "Could not join that table."; return; }
    store.set(tokenKey(code), r.token);
    location.href = `/?game=${code}`;
  };
  const tables = h("div", { class: "tablelist" });
  const form = h("div", {},
    h("h1", {}, "Charter"),
    tagline,
    h("div", { class: "numerals", role: "group", "aria-label": "The constitution's ten promises", onkeydown: numeralKeys }, CONSTITUTION.promises.map((p, i) =>
      h("button", { tabindex: i ? "-1" : "0", title: `The constitution: ${p.line}`, "aria-label": `Promise ${p.n}: ${p.line}`, onclick: e => openPromise(p.n, e.currentTarget) }, p.n))),
    h("label", { class: "field signature" }, name, h("span", { class: "signlabel" }, "Sign your name")),
    seg, packList, packNote,
    h("button", { class: "act gold", onclick: async () => {
      if (!nameOk()) return;
      const r = await api("/api/games", { seats, game: game ?? undefined });
      if (!r.ok) { err.textContent = r.error; return; }
      await join(r.code);
    } }, "Found a table"),
    h("div", { class: "joinline" }, joinCode, h("button", { class: "act", onclick: () => nameOk() && join(joinCode.value) }, "Join")),
    err, tables);
  const page = scrollSheet(form, shelf, promises);
  app.replaceChildren(stage, page);
  name.addEventListener("keydown", e => { if (e.key === "Enter") e.target.closest(".titlepage").querySelector(".act.gold").click(); });
  // The signature font loads before it is needed, so the first letter typed is already in ink.
  document.fonts?.load('32px "Mrs Saint Delafield"').catch(() => {});
  // A person with a mouse can start signing at once. A phone keeps its keyboard down until asked.
  if (!name.value && matchMedia("(pointer: fine)").matches) name.focus({ preventScroll: true });
  const whole = !params.has("join") && !store.get("charter.opened");
  const release = reduced() ? () => {} : openScroll(page, whole);
  if (whole && !reduced()) { store.set("charter.opened", "1"); setTimeout(release, 1200); }
  loadPlayer(stage.querySelector("canvas")).then(async p => {
    if (!p) { release(); return; }
    p.setInsets({ l: innerWidth <= 560 ? 16 : Math.min(innerWidth * .46, 480), r: 16, t: 16, b: 16 });
    stagePlayer = p;
    await defsLoaded;
    const d = defs.find(x => x.id === game);
    if (d) await showBackdrop(d);
    release();
  });
  // Only the tables this browser holds a seat at. No route lists every table, because a code is what
  // lets a person reach one. Any table lost from the server is left out.
  let codes = [];
  try { codes = Object.keys(localStorage).filter(k => k.startsWith("charter.token.")).map(k => k.slice("charter.token.".length)); } catch {}
  const mine = (await Promise.all(codes.slice(-6).reverse().map(c => api(`/api/games/${c}`).catch(() => null)))).filter(g => g?.code);
  fill(tables, mine.map(g => h("div", { class: "t" }, h("span", { class: "code" }, g.code),
    h("span", { class: "state" }, g.started ? (g.phase === "ended" ? "Finished" : "In play") : `${g.filled} of ${g.seats} seated`),
    h("a", { class: "link", href: `/?game=${g.code}` }, "Return"))));
}

// ---------------------------------------------------------------- game state
const G = {
  code: null, token: null, view: null, version: -1, player: null, use3d: true,
  sceneBusy: false, sceneDirty: false, polling: null, ui: null,
  selected: null,       // the piece kind being placed, in the actions phase
  dock: null,           // what is open in the dock: {t:"draft"} {t:"vote",id} {t:"laws"} {t:"chronicle"} {t:"moment"}
  menu: false, everyEvent: false,
  seenProposals: null, stampsSeen: new Set(), seenDecisions: null, moment: null,
  prev: null, holdScene: false, draft: null, draftPolling: null, errTimer: null, captionTimer: null,
  talk: [], talkCount: -1, talkSeen: 0, talkAll: false,
  inFlight: {},         // cards of each good on their way to the hand, not yet counted there
  replay: null,         // {at, total, playing, marks, timer}: watching a game from its log
};
const you = () => G.view?.you;
const seat = i => G.view?.seats?.find(s => s.seat === i);
const nameOf = i => (i === you() ? "You" : seat(i)?.name ?? `Seat ${i}`);

async function post(path, body) {
  let r;
  try { r = await api(`/api/games/${G.code}/${path}`, { token: G.token, ...body }); }
  catch { r = { ok: false, error: "The server cannot be reached." }; }
  if (r && r.ok === false) say(r.error || "Refused.");
  poke();
  return r;
}
const postMove = move => post("move", { move });
function poke() { G.version = -1; clearTimeout(G.polling); G.polling = setTimeout(poll, 40); }

/** Say something where the eye already is: the prompt line above the ledge. */
function say(msg) {
  G.errMsg = msg;
  clearTimeout(G.errTimer);
  G.errTimer = setTimeout(() => { G.errMsg = null; renderPrompt(); }, 6000);
  renderPrompt();
}

// ---------------------------------------------------------------- scene
function sceneQuery() {
  const v = G.view, q = new URLSearchParams();
  if (G.replay) { q.set("at", G.replay.at); q.set("markers", "none"); return q; }
  if (v?.phase === "setup") q.set("markers", "all");
  else q.set("markers", G.selected ? G.selected : "none");
  return q;
}
async function refreshScene() {
  if (!G.player || !G.use3d || G.holdScene) return;
  if (G.sceneBusy) { G.sceneDirty = true; return; }
  G.sceneBusy = true;
  try {
    const buf = await api(`/api/games/${G.code}/scene?${sceneQuery()}`);
    if (buf.byteLength > 4) G.player.render(buf);
  } catch (e) { console.warn("scene", e); }
  G.sceneBusy = false;
  if (G.sceneDirty) { G.sceneDirty = false; refreshScene(); }
}
function updateInsets() {
  if (!G.player) return;
  const dockOpen = !!G.dock;
  const dockW = dockOpen ? (innerWidth <= 860 ? 300 : 372) : 0;
  document.documentElement.style.setProperty("--dockw", `${dockW}px`);
  const ledge = parseInt(getComputedStyle(document.documentElement).getPropertyValue("--ledge"));
  const lobby = G.view?.phase === "lobby";
  G.player.setInsets(lobby ? { l: Math.min(innerWidth * .46, 480), r: 16, t: 16, b: 16 } : { l: 0, r: 52 + dockW, t: 44, b: ledge + 8 });
}

// ---------------------------------------------------------------- picking on the board
function onPick(id, cx, cy) {
  const v = G.view; if (!v) return;
  if (id === 8999) return;
  if (id >= 9000) { openDock({ t: "laws", focus: id }); return; }
  if (id >= 3000) return;
  let moves = (v.legalMoves || []).filter(m => m.pick === id);
  if (G.selected) moves = moves.filter(m => m.kind === G.selected);
  if (moves.length === 1) { place(moves[0]); return; }
  if (moves.length > 1) showPickMenu(moves, cx, cy);
}
function place(m) {
  closePickMenu();
  postMove(m.move).then(r => {
    if (r?.ok && G.selected) {
      // Stay in the mode only while more of the piece can really be placed.
      setTimeout(() => {
        const def = (G.view?.pieceDefs || []).find(d => d.name === G.selected);
        if (!def || !def.spots) { G.selected = null; renderLedge(); renderPrompt(); refreshScene(); }
      }, 120);
    }
  });
}
function closePickMenu() { G.ui?.pickmenu.replaceChildren(); G.ui && (G.ui.pickmenu.hidden = true); }
function showPickMenu(moves, cx, cy) {
  const m = G.ui.pickmenu;
  fill(m, moves.map(x => h("button", { class: "act", onclick: () => place(x) }, capital(x.kind), x.cost?.length ? costOf(x.cost) : null)));
  m.hidden = false;
  m.style.left = `${Math.min(cx + 12, innerWidth - 200)}px`;
  m.style.top = `${Math.max(cy - 40, 8)}px`;
}

/** What a hover on the board shows. Details stay here until asked for. */
function tipFor(id) {
  const v = G.view; if (!v || !id) return null;
  if (id === 8999) {
    const held = Object.entries(v.treasury || {}).filter(([r, n]) => n > 0 && v.resources.includes(r));
    return [h("h4", {}, "The treasury"), held.length ? h("div", { class: "row" }, held.map(([r, n]) => h("span", {}, String(n), " ", resIcon(r, "res small")))) : h("div", {}, "Empty. Only a law can fill it or pay it out.")];
  }
  if (id >= 9000) {
    const l = (v.laws || []).find(x => x.pick === id);
    return l ? [h("h4", {}, `Law ${l.id}: ${l.title}`), l.description?.text ? h("div", { class: "english" }, l.description.text) : h("pre", { class: "sexp" }, sourceLines(l.text))] : null;
  }
  if (id >= 7000) {
    const t = v.board?.tiles?.[id - 7000];
    if (!t) return null;
    if (!t.res) return [h("h4", {}, "The square"), h("div", {}, "Each law in force stands here.")];
    return [h("h4", {}, h("span", {}, resIcon(t.res, "res small"), " ", capital(t.res))), h("div", { class: "row" }, `Pays on a ${t.number}`, h("span", { class: "pips" }, "•".repeat(t.pips)))];
  }
  if (id >= 3000) {
    const here = (v.pieces || []).filter(p => p.spot === id - 3000);
    if (!here.length) return null;
    const def = k => (v.pieceDefs || []).find(d => d.name === k);
    const owner = here[0].owner;
    return [h("h4", {}, shield(owner, seatColor(owner)), " ", here.map(p => capital(p.kind)).join(" and ")),
      h("div", {}, owner === v.you ? "Yours" : seat(owner)?.name),
      h("div", { class: "row" }, `Collects ${here.reduce((a, p) => a + (def(p.kind)?.yield || 0), 0)} at each harvest`)];
  }
  let moves = (v.legalMoves || []).filter(m => m.pick === id);
  if (G.selected) moves = moves.filter(m => m.kind === G.selected);
  if (!moves.length) return null;
  const m = moves[0];
  return [h("h4", {}, `${capital(m.kind)}${moves.length > 1 ? " and more" : ""}`),
    m.cost?.length ? h("div", { class: "row" }, "Costs ", costOf(m.cost)) : null,
    m.yields?.length ? h("div", { class: "row" }, m.yields.map(y => h("span", {}, resIcon(y.res, "res small"), ` ${y.number} `, h("span", { class: "pips" }, "•".repeat(y.pips))))) : null];
}
function onHover(id, x, y) {
  const tip = G.ui?.tip; if (!tip) return;
  if (id !== G.tipId) { G.tipId = id; const kids = tipFor(id); tip.hidden = !kids; if (kids) fill(tip, kids); }
  if (!tip.hidden) {
    const w = tip.offsetWidth, ht = tip.offsetHeight;
    tip.style.left = `${Math.min(x + 16, innerWidth - w - 8)}px`;
    tip.style.top = `${Math.max(Math.min(y - ht - 12, innerHeight - ht - 8), 8)}px`;
  }
}

// ---------------------------------------------------------------- game screen
async function gameScreen(code) {
  G.code = code;
  G.token = params.has("replay") ? null : store.get(tokenKey(code));
  seatToken = G.token;
  const canvas = h("canvas"), svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.setAttribute("class", "board2d");
  const U = G.ui = {
    canvas, svg,
    houses: h("div", { class: "houses" }),
    herald: h("div", { class: "herald" }),
    clock: h("div", { "data-key": "clock", class: "clock", hidden: true }),
    caption: h("div", { class: "caption", role: "status" }),
    ledge: h("div", { class: "ledge" }),
    declared: h("div", { class: "declared vellum", hidden: true }),
    replayBar: h("div", { class: "replaybar", hidden: true }),
    prompt: h("div", { class: "prompt", role: "status", hidden: true }),
    slips: h("div", { class: "slips" }),
    pickmenu: h("div", { class: "pickmenu vellum", hidden: true }),
    tip: h("div", { class: "tip vellum", hidden: true }),
    rail: h("div", { class: "rail" }),
    dock: h("div", { class: "dock vellum", "aria-live": "polite" }),
    menu: h("div", { class: "menu vellum", hidden: true }),
    center: h("div"),
  };
  U.sheet = h("div", { class: "sheet", onscroll: () => { if (U.sheet.firstChild === U.constitution) G.constitutionTop = U.sheet.scrollTop; } });
  U.dock.append(h("button", { class: "x", title: "Close (Esc)", "aria-label": "Close", onclick: () => closeDock(true) }, uiIcon("close")), U.sheet);
  buildDraftDesk();
  buildLedge();
  app.replaceChildren(h("div", { class: "stage" }, canvas, svg, h("div", { class: "vignette" })),
    h("div", { class: "crown" }, U.houses, h("div", { class: "heraldry" }, U.herald, U.caption)), U.slips, U.prompt, U.declared, U.ledge, U.replayBar, U.dock, U.rail, U.menu, U.pickmenu, U.tip, U.center);
  G.player = await loadPlayer(canvas);
  if (G.player) { G.player.onPick = onPick; G.player.onHover = onHover; } else G.use3d = false;
  applyMode();
  addEventListener("resize", updateInsets);
  addEventListener("keydown", onKey);
  setInterval(renderClock, 1000);
  // A draft that was running before a reload is still running on the server.
  G.words = store.get(`charter.words.${code}`) || "";
  U.words.value = G.words;
  if (G.token) checkDraft();
  if (params.has("replay")) { startReplay(true); return; }
  poll();
}
function applyMode() {
  const U = G.ui;
  U.canvas.style.display = G.use3d ? "block" : "none";
  U.svg.style.display = G.use3d ? "none" : "block";
  updateInsets();
  if (G.view) { if (G.use3d) refreshScene(); else renderBoard2D(U.svg, G.view, seatColor, onPick); }
}

async function poll() {
  clearTimeout(G.polling);
  try {
    const q = new URLSearchParams({ since: G.version, described: G.view?.described ?? 0 });
    const v = await api(`/api/games/${G.code}/view?${q}`);
    if (G.lost) { G.lost = false; caption(""); }
    if (v && v.talkCount != null && v.talkCount !== G.talkCount) fetchTalk();
    if (v && "turnLeftMs" in v) { G.turnEnd = v.turnLeftMs == null ? null : performance.now() + v.turnLeftMs; renderClock(); }
    if (v && "resting" in v && v.resting !== G.resting) { G.resting = v.resting; if (v.resting) caption(v.resting); }
    // Only someone watching can see a paused table. A player who comes back has already ended the pause.
    if (v && "paused" in v && !G.token && !!v.paused !== !!G.paused) { G.paused = v.paused; caption(v.paused ? "This table is paused until one of its players comes back." : "", v.paused); }
    if (v && v.drafting && G.view && JSON.stringify(v.drafting) !== JSON.stringify(G.view.drafting)) { G.view.drafting = v.drafting; renderHouses(); }
    if (v && !v.unchanged && v.code) {
      const prev = G.view;
      G.view = v; G.version = v.version;
      // A description came in, and nothing else changed.
      if (prev?.version === v.version) renderDock();
      else afterView(prev, v);
      if (v.phase === "ended" && !G.token && !G.replay) { startReplay(false); return; }
    }
  } catch (e) { if (!G.lost) { G.lost = true; caption("Lost contact with the table. Trying again.", true); } }
  const wait = pollWait(700);
  if (wait != null) G.polling = setTimeout(poll, wait);
}
// A hidden tab is someone who may come straight back, so it polls slowly and still counts as a person at
// the table (the server's limit is CHARTER_TABLE_AWAY_MS, 3 minutes). After 10 minutes hidden it stops, so
// a forgotten tab lets the table pause and the server sleep. Showing the tab again gets the whole view.
const HIDDEN_POLL_MS = 30000, HIDDEN_STOP_MS = 600000;
let hiddenSince = document.hidden ? performance.now() : null;
function pollWait(visibleMs) {
  if (hiddenSince == null) return visibleMs;
  return performance.now() - hiddenSince > HIDDEN_STOP_MS ? null : Math.max(visibleMs, HIDDEN_POLL_MS);
}
document.addEventListener("visibilitychange", () => {
  if (document.hidden) { hiddenSince ??= performance.now(); return; }
  hiddenSince = null;
  if (!G.code || G.replay) return;
  poke();
  if (G.draft && !G.draft.outcome && !G.draft.optimistic) pollDraft();
});

/** Everything that follows a new view. */
function afterView(prev, v) {
  if (G.selected && !(v.pieceDefs || []).some(d => d.name === G.selected && d.spots > 0)) G.selected = null;
  if (v.turn !== prev?.turn) closePickMenu();
  const newLaw = trackDecisions(v);
  trackProposals(prev, v);
  renderAll();
  showFoundingLaws(prev, v);
  if (!newLaw) refreshScene();
  else if (!G.player) refreshScene();
  animateChanges(prev, v);
  if (G.dock?.t === "draft" && G.draft?.outcome === "ready") refreshDraftReview();
  if (v.phase === "lobby" && prev?.phase !== "lobby") refreshScene();
}
/** A pack's founding laws are the first thing a seated player reads at its table, once. */
function showFoundingLaws(prev, v) {
  if (v.you == null || G.replay || v.phase !== "setup" || !(v.laws || []).length || G.dock) return;
  const key = `charter.founding.${v.code}`;
  if (store.get(key)) return;
  store.set(key, "1");
  openDock({ t: "laws" });
}
function renderAll() {
  if (!G.view) return;
  applyLook(G.view.look);
  renderHouses(); renderHerald(); renderLedge(); renderPrompt(); renderSlips(); renderRail(); renderDock(); renderCenter();
  if (!G.use3d) renderBoard2D(G.ui.svg, G.view, seatColor, onPick);
  updateInsets();
}

// ---------------------------------------------------------------- houses
function bannerCloth(s) {
  const cloth = h("span", { class: "cloth", style: { background: seatColor(s) } });
  const art = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  art.setAttribute("viewBox", "0 0 60 84"); art.setAttribute("preserveAspectRatio", "none");
  art.innerHTML = chargeOf(s);
  cloth.append(art);
  return cloth;
}
function renderHouses() {
  const v = G.view, U = G.ui;
  if (v.phase === "lobby") { fill(U.houses); return; }
  morphKids(U.houses, v.seats.map(s => {
    const cloth = bannerCloth(s.seat);
    cloth.append(h("span", { class: "score" }, String(s.points)));
    const held = Object.entries(s.hand || {}).filter(([r, n]) => n > 0 && v.resources.includes(r));
    const built = Object.entries(s.pieces || {}).filter(([, n]) => n > 0);
    const drafting = (v.drafting || []).includes(s.seat);
    return h("div", { "data-key": s.seat, class: "banner" + (v.turn === s.seat && v.phase !== "ended" ? " turn" : "") + (v.winner === s.seat ? " won" : "") + (s.seat === v.you ? " you" : ""), tabindex: 0, "aria-label": `${s.name}, ${plural(s.points, "point")}` },
      cloth,
      drafting ? h("span", { class: "quillmark", title: "Drafting a rule" }, uiIcon("quill")) : null,
      h("span", { class: "name" }, s.seat === v.you ? "You" : s.name.replace(/^Bot /, "")),
      h("div", { class: "card-tip vellum" },
        h("div", {}, h("strong", {}, s.name), ` · ${plural(s.points, "point")} of ${v.target}`),
        s.tokenPoints ? h("div", { class: "row" }, `${plural(s.tokenPoints, "point")} from what they hold`) : null,
        s.persona ? h("div", { class: "row" }, `Plays as a ${s.persona}: ${s.voice}.`) : null,
        held.length ? h("div", { class: "row" }, held.map(([r, n]) => h("span", {}, String(n), " ", resIcon(r, "res small")))) : h("div", { class: "row" }, "Holds nothing"),
        built.length ? h("div", { class: "row" }, built.map(([k, n]) => h("span", {}, plural(n, k)))) : null));
  }));
}
/** What every seat has declared this round, plainly. It shows only while a law reads declarations. */
function renderDeclared() {
  const v = G.view, U = G.ui, d = v.declarations;
  const show = !!d?.inUse && v.phase === "actions";
  U.declared.hidden = !show;
  if (!show) return;
  const bySeat = new Map();
  for (const r of d.rows) { if (!bySeat.has(r.seat)) bySeat.set(r.seat, []); bySeat.get(r.seat).push(r); }
  fill(U.declared, h("div", { class: "lbl" }, "Declared this round"),
    d.rows.length ? [...bySeat.entries()].map(([s, rows]) => h("div", { class: "line" },
      h("b", {}, s === v.you ? "You" : nameOf(s)),
      rows.map(r => h("span", { class: "chg" }, String(r.n), " ", resIcon(r.res, "res small"), ` ${r.res}`))))
      : h("div", { class: "line none" }, "Nobody yet."));
}
function renderHerald() {
  const v = G.view, U = G.ui;
  renderDeclared();
  if (v.phase === "lobby") { fill(U.herald); return; }
  const die = v.lastRoll != null ? h("div", { "data-key": "die", class: "die", title: "The last roll" }, String(v.lastRoll)) : null;
  morphKids(U.herald, [h("div", { "data-key": "tab", class: "tab" }, v.phase === "setup" ? "The founding" : v.phase === "ended" ? "The end" : `Round ${v.round}`), die, U.clock]);
}
/** The time left in this turn, quietly. It comes from the server, which keeps the real clock. */
function renderClock() {
  const c = G.ui?.clock, v = G.view; if (!c) return;
  const who = v?.turn != null ? seat(v.turn) : null;
  if (G.turnEnd == null || !who || who.kind === "bot" || G.replay || v.phase === "ended") { c.hidden = true; return; }
  const left = Math.max(0, Math.ceil((G.turnEnd - performance.now()) / 1000));
  c.hidden = false;
  c.textContent = `${Math.floor(left / 60)}:${String(left % 60).padStart(2, "0")}`;
  c.title = `Time left in ${v.turn === v.you ? "your" : `${who.name}'s`} turn`;
  c.classList.toggle("soon", left <= 30 && v.turn === v.you);
}
function caption(text, sticky) {
  const c = G.ui?.caption; if (!c) return;
  c.textContent = text; c.classList.toggle("on", !!text);
  clearTimeout(G.captionTimer);
  if (text && !sticky) G.captionTimer = setTimeout(() => c.classList.remove("on"), 5000);
}

// ---------------------------------------------------------------- the ledge
function buildLedge() {
  const U = G.ui;
  U.hand = h("div", { class: "hand", role: "group", "aria-label": "Your hand" });
  U.tray = h("div", { class: "tray" });
  U.endTurn = h("button", { class: "act endturn", onclick: () => endTurn() });
  fill(U.ledge, U.hand, U.tray, U.endTurn);
}
function endTurn() {
  const end = (G.view?.legalMoves || []).find(m => m.move.t === "endTurn");
  if (!end) return;
  G.selected = null;
  if (G.dock?.t === "trade") closeDock();
  postMove(end.move);
}
/** A good no hex pays, such as a laurel, stays off the screen until someone holds it. */
function goodsInPlay(v) {
  const paid = new Set((v.board?.tiles || []).map(t => t.res));
  return (v.resources || []).filter(r => paid.has(r) || (v.seats || []).some(s => s.hand?.[r] > 0));
}
function renderLedge() {
  const v = G.view, U = G.ui;
  const seated = v.you != null && v.phase !== "lobby" && v.phase !== "ended";
  U.ledge.hidden = !seated;
  if (!seated) return;
  const inPlay = goodsInPlay(v);
  renderHand();
  // A game can have 16 goods, and the hand was drawn for five. Past six, the cards shrink into two rows.
  U.hand.classList.toggle("many", goodsInPlay(v).length > 6);
  const moves = v.legalMoves || [];
  const end = moves.find(m => m.move.t === "endTurn");
  const mine = v.turn === v.you;
  const building = mine && v.phase === "actions";
  const tools = [];
  if (building) {
    (v.pieceDefs || []).forEach((d, i) => {
      // A piece paid for in a good that is not in play yet is not an option yet.
      if (d.cost.some(x => !inPlay.includes(x.res))) return;
      const enabled = d.spots > 0, sel = G.selected === d.name, made = d.made;
      const why = !enabled && d.short?.length ? `Need ${costText(d.short)}` : !enabled ? (d.owned >= d.limit ? `All ${d.limit} built` : "No place for one") : `${capital(d.name)}: ${costText(d.cost)}. ${plural(d.spots, "place")}.`;
      tools.push(h("button", { "data-key": d.name, class: "tool" + (sel ? " selected" : ""), disabled: !enabled, title: why, "aria-pressed": sel ? "true" : "false", "aria-label": why,
        onclick: () => selectPiece(d.name), onpointerenter: e => { if (e.pointerType === "mouse") previewCost(d.name); }, onpointerleave: () => previewCost(null), onfocus: () => previewCost(d.name), onblur: () => previewCost(null) },
        pieceIcon(made ? "made" : d.name),
        h("span", { class: "nm" }, capital(d.name)),
        !enabled && d.short?.length ? h("span", { class: "need" }, d.short.map(x => h("span", {}, `${x.n}`, resIcon(x.res, "res")))) : null));
      void i;
    });
    tools.push(h("button", { "data-key": "trade", class: "tool sep" + (G.dock?.t === "trade" ? " selected" : ""), title: "Trade with the bank or the table (T)", onclick: () => toggleDock({ t: "trade" }) }, uiIcon("trade"), h("span", { class: "nm" }, "Trade")));
    if (v.declarations?.inUse) tools.push(h("button", { "data-key": "declare", class: "tool" + (G.dock?.t === "declare" ? " selected" : ""), title: "Declare a public number. A law reads these.", onclick: () => toggleDock({ t: "declare" }) }, uiIcon("declare"), h("span", { class: "nm" }, "Declare")));
  }
  morphKids(U.tray, tools);
  U.tray.classList.toggle("many", tools.length > 5);
  U.endTurn.hidden = !end;
  fill(U.endTurn, "End turn");
  U.endTurn.title = "End your turn (E)";
  // The strongest accent goes to the next action, and only when that is clearly this button.
  const placedAll = v.phase === "setup" && !moves.some(m => m.move.t === "place");
  const nothingBuildable = v.phase === "actions" && !moves.some(m => m.move.t === "place") && !G.selected;
  U.endTurn.classList.toggle("gold", !!end && !G.dock && (placedAll || nothingBuildable));
}
/** The hand, as a fan of stacks. A card on its way here does not count until it lands. The cards a piece
 *  would take rise while that piece is pointed at or being placed. */
function renderHand() {
  const v = G.view, U = G.ui, hand = seat(v.you)?.hand || {}, inPlay = goodsInPlay(v);
  const building = v.turn === v.you && v.phase === "actions";
  if (!building) G.pointedPiece = null; // a pointer on a tool that went away tells nobody it left
  const piece = (v.pieceDefs || []).find(d => d.name === (G.selected || G.pointedPiece) && d.spots > 0);
  morphKids(U.hand, inPlay.map((r, i) => {
    const n = hand[r] || 0, shown = Math.max(0, n - (G.inFlight[r] || 0));
    const pay = piece?.cost.find(x => x.res === r)?.n;
    const fan = i - (inPlay.length - 1) / 2;
    return h("div", { "data-key": r, class: "rcard" + (shown ? "" : " none") + (pay ? " pays" : ""), "data-res": r, "data-depth": Math.min(shown, 4), "data-pay": pay ? `−${pay}` : null, title: `${n} ${r}`,
      style: `--fan:${fan};--dip:${(fan * fan * .7).toFixed(1)}px` }, resIcon(r), h("b", {}, String(shown)));
  }));
}
function previewCost(name) {
  if (G.pointedPiece === name || (!name && !G.pointedPiece)) return;
  G.pointedPiece = name;
  if (G.view) renderHand();
}
function selectPiece(k) {
  G.selected = G.selected === k ? null : k;
  if (G.dock?.t === "trade") closeDock();
  closePickMenu();
  renderLedge(); renderPrompt(); refreshScene();
}
function renderPrompt() {
  const v = G.view, p = G.ui?.prompt; if (!p) return;
  p.className = "prompt" + (G.dock ? " dock-open" : "");
  if (G.errMsg) { p.classList.add("err"); p.textContent = G.errMsg; p.hidden = false; return; }
  if (!v || v.phase === "lobby" || v.phase === "ended") { p.hidden = true; return; }
  // A harvest can put a seat at the target by what it holds. It wins at the next move or vote by anyone.
  const atTarget = v.phase === "actions" && (v.seats || []).find(s => s.points >= v.target);
  if (atTarget && !G.selected) { p.textContent = `${nameOf(atTarget.seat)} reached the target. The next move or vote ends the game.`; p.hidden = false; return; }
  if (G.selected) {
    const d = (v.pieceDefs || []).find(x => x.name === G.selected);
    fill(p, `${capital(G.selected)}: `, costOf(d?.cost), `. Pick a glowing place, or Esc.`);
    p.hidden = false; return;
  }
  if (v.turn === v.you && v.prompt) {
    // Setup needs telling. Later a reminder earns its place only in the first rounds.
    if (v.phase !== "setup" && v.round > 2) { p.hidden = true; return; }
    p.textContent = v.prompt; p.hidden = false;
    // Gold goes to what to do next. When that is the End turn button, the words stay quiet.
    if (v.phase !== "setup" || !(v.legalMoves || []).some(m => m.move.t === "place")) p.classList.add("quiet");
    return;
  }
  p.hidden = true;
}

// ---------------------------------------------------------------- slips: offers
function renderSlips() {
  const v = G.view, U = G.ui;
  const offers = (v.offers || []).filter(o => o.canAccept || o.canCancel || o.to == null || o.to === v.you);
  fill(U.slips, offers.map(o => h("div", { class: "slip vellum" },
    h("div", {}, o.from === v.you ? "Your offer" : `${seat(o.from)?.name} offers`, o.to != null && o.from === v.you ? ` to ${nameOf(o.to)}` : ""),
    h("div", { class: "terms" }, costOf(o.give), h("span", {}, "for"), costOf(o.get)),
    h("div", { class: "row" },
      o.canAccept ? h("button", { class: "act gold", onclick: () => postMove({ t: "accept", id: o.id }) }, "Accept") : null,
      o.canCancel ? h("button", { class: "act", onclick: () => postMove({ t: "cancel", id: o.id }) }, "Take back") : null))));
}

// ---------------------------------------------------------------- the rail
function renderRail() {
  const v = G.view, U = G.ui, d = G.dock;
  if (v.phase === "lobby") { fill(U.rail); return; }
  const open = (v.proposals || []);
  const inForce = (v.laws || []).length + (v.deals || []).length;
  const waiting = open.filter(p => p.canVote || p.canSign);
  const onVote = d?.t === "vote" || d?.t === "moment";
  const canDraft = v.you != null && v.phase === "actions";
  const draftActive = G.draft && !G.draft.outcome;
  fill(U.rail,
    canDraft ? h("button", { class: (d?.t === "draft" ? "on " : "") + (draftActive && d?.t !== "draft" ? "attention" : ""), title: "Propose a rule (R)", "aria-label": "Propose a rule", onclick: () => toggleDock({ t: "draft" }) }, uiIcon("quill")) : null,
    open.length ? h("button", { class: (onVote ? "on " : "") + (waiting.length && !onVote ? "attention" : ""), title: "Before the table (V)", "aria-label": `${plural(open.length, "proposal")} before the table`, onclick: () => toggleDock({ t: "vote", id: (waiting[0] || open[0]).id }) }, uiIcon("seal"), h("span", { class: "count" }, String(open.length))) : null,
    h("button", { class: d?.t === "laws" ? "on" : "", title: "In force (L)", "aria-label": `${plural(inForce, "law and deal")} in force`, onclick: () => toggleDock({ t: "laws" }) }, uiIcon("book"), inForce ? h("span", { class: "count" }, String(inForce)) : null),
    h("button", { class: d?.t === "chronicle" ? "on" : "", title: "Chronicle (C)", "aria-label": "Chronicle", onclick: () => toggleDock({ t: "chronicle" }) }, uiIcon("scroll")),
    v.phase !== "lobby" ? h("button", { class: d?.t === "talk" ? "on" : "", title: "Table talk (M)", "aria-label": "Table talk", onclick: () => toggleDock({ t: "talk" }) }, uiIcon("talk"), G.talk.length > G.talkSeen && d?.t !== "talk" ? h("span", { class: "count" }, String(G.talk.length - G.talkSeen)) : null) : null,
    v.phase === "ended" ? h("button", { class: d?.t === "end" ? "on" : "", title: "The result", "aria-label": "The result", onclick: () => toggleDock({ t: "end" }) }, uiIcon("seal")) : null,
    h("div", { class: "spacer" }),
    h("button", { class: "numeralsmark" + (d?.t === "constitution" ? " on" : ""), title: "The constitution", "aria-label": "The constitution", onclick: () => toggleDock({ t: "constitution" }) }, "I–X"),
    h("button", { class: G.menu ? "on" : "", title: "This table", "aria-label": "This table", onclick: () => { G.menu = !G.menu; renderMenu(); renderRail(); } }, uiIcon("dots")));
}
function renderMenu() {
  const U = G.ui, v = G.view;
  U.menu.hidden = !G.menu;
  if (!G.menu || !v) return;
  fill(U.menu,
    h("div", {}, h("div", { class: "smallcaps" }, "Table"), h("div", { class: "code" }, v.code)),
    v.game?.name ? h("div", {}, h("strong", {}, v.game.name), `. ${v.game.blurb}`) : null,
    h("div", {}, `First to ${v.target ?? 10} points, within ${v.rounds ?? 30} rounds.`),
    !G.replay && v.phase !== "lobby" && v.seats.every(x => x.kind !== "human") ? h("a", { class: "link", href: `/?game=${v.code}&replay=1` }, "Replay from the start") : null,
    G.player ? h("button", { class: "link", style: { textAlign: "left" }, onclick: () => { G.use3d = !G.use3d; applyMode(); renderMenu(); } }, G.use3d ? "Use the 2D board" : "Use the 3D table") : null,
    h("details", { class: "formal" }, h("summary", {}, "Dice fingerprint"), h("div", { class: "fine" }, v.fingerprint)),
    h("a", { class: "link", href: "/" }, "Leave for the title page"));
}

// ---------------------------------------------------------------- the dock
function openDock(d) {
  G.dock = d;
  G.menu = false; renderMenu();
  renderDock(); renderRail(); renderPrompt(); renderLedge(); updateInsets();
  if (d.t === "draft") setTimeout(() => G.ui.words.focus(), 60);
}
function toggleDock(d) {
  if (G.dock?.t === d.t && (d.id == null || G.dock.id === d.id)) closeDock(true); else openDock(d);
}
function closeDock(byHand) {
  if (byHand && G.dock?.t === "vote") G.dismissed = G.dock.id;
  G.dock = null;
  G.ui.dock.classList.remove("open");
  renderRail(); renderPrompt(); renderLedge(); updateInsets();
}
function renderDock() {
  const U = G.ui, d = G.dock;
  U.dock.classList.toggle("open", !!d);
  if (!d) return;
  const keep = U.sheet.scrollTop;
  if (d.t === "draft") { if (U.sheet.firstChild !== U.desk) { fill(U.sheet, U.desk); U.growWords(); } renderDraft(); return; }
  if (d.t === "vote") {
    const p = (G.view.proposals || []).find(x => x.id === d.id);
    if (!p) { closeDock(); return; }
    fill(U.sheet, voteDoc(p));
    U.sheet.scrollTop = keep;
    settleHopeless();
    return;
  }
  // One document, kept for the whole game, so that a poll or a passing moment leaves it as it was.
  if (d.t === "constitution") {
    U.constitution ??= constitutionDoc();
    if (U.sheet.firstChild !== U.constitution) { fill(U.sheet, U.constitution); U.sheet.scrollTop = G.constitutionTop || 0; }
    return;
  }
  if (d.t === "moment") { fill(U.sheet, momentDoc(G.moment)); return; }
  if (d.t === "laws") { fill(U.sheet, lawsDoc()); U.sheet.scrollTop = keep; flashFocus(); return; }
  if (d.t === "chronicle") { renderChronicle(); return; }
  if (d.t === "talk") { renderTalk(); return; }
  if (d.t === "end") { fill(U.sheet, proclamation(G.view)); return; }
  if (d.t === "declare") {
    if (!G.view.declarations?.can) { closeDock(); return; }
    // Keep typing in the box alive across polls.
    if (!U.sheet.contains(document.activeElement) || !U.sheet.querySelector(".declaresheet")) fill(U.sheet, declareDoc());
    return;
  }
  if (d.t === "trade") {
    if (G.view.turn !== G.view.you || G.view.phase !== "actions") { closeDock(); return; }
    // Keep typing in the amount boxes alive across polls.
    if (!U.sheet.contains(document.activeElement) || !U.sheet.querySelector(".tradesheet")) renderTrade();
    return;
  }
}
/** The control for one public number per good. Each change is one action. */
function declareDoc() {
  const v = G.view, d = v.declarations;
  const mine = r => (d.rows.find(x => x.seat === v.you && x.res === r)?.n) || 0;
  const row = r => {
    const box = h("input", { type: "number", min: "0", max: String(d.max), value: String(mine(r)), "aria-label": `Number to declare for ${r}` });
    const send = () => {
      const n = Math.max(0, Math.min(d.max, Math.floor(Number(box.value) || 0)));
      postMove({ t: "declare", res: r, n });
    };
    box.addEventListener("keydown", e => { if (e.key === "Enter") { e.preventDefault(); send(); } });
    return h("div", { class: "drow" }, resIcon(r), h("span", { class: "nm" }, capital(r)), box, h("button", { class: "act", onclick: send }, "Declare"));
  };
  return h("div", { class: "declaresheet" },
    h("h3", {}, "Declare a number"),
    h("p", { class: "note-line" }, "Everyone can see it. It moves nothing by itself, and only laws read it. You can change it on your turn. It clears when the round ends."),
    goodsInPlay(v).map(row));
}
function flashFocus() {
  if (G.dock?.focus == null) return;
  const row = G.ui.sheet.querySelector(`[data-pick="${G.dock.focus}"]`);
  if (row) { row.scrollIntoView({ block: "center" }); row.classList.add("flash"); }
  G.dock.focus = null;
}

/** A deal's statement from Lean, a line for each thing it does. */
function statementOf(text) {
  return h("p", { class: "statement" }, text.split("\n").map(line => h("span", { class: "line" }, line)));
}

/** Consequences: who gains and who pays at this table. Empty cases are not shown. */
function consequences(pv) {
  if (!pv) return null;
  if (pv.nothing) return h("p", { class: "note-line" }, "Nothing changes at this table yet.");
  const whoName = s => s == null ? "Treasury" : nameOf(s);
  const rows = rows => {
    const groups = new Map();
    for (const r of rows) { const k = r.seat == null ? "t" : r.seat; if (!groups.has(k)) groups.set(k, { seat: r.seat, list: [] }); groups.get(k).list.push(r); }
    return [...groups.values()].map(g => h("div", { class: "who" }, h("b", {}, whoName(g.seat)),
      g.list.map(r => h("span", { class: "chg " + (r.delta > 0 ? "up" : "down") }, `${r.delta > 0 ? "+" : "−"}${Math.abs(r.delta)}`, resIcon(r.res, "res small")))));
  };
  return h("div", { class: "conseq" },
    (pv.points || []).map(x => h("div", { class: "note" + (x.wins ? " win" : "") }, `${nameOf(x.seat)}: ${x.from} → ${plural(x.to, "point")}.${x.wins ? ` ${x.seat === you() ? "You would win" : nameOf(x.seat) + " would win"} at once.` : ""}`)),
    (pv.notes || []).map(n => h("div", { class: "note" }, n)),
    (pv.sections || []).map(s => h("div", { class: "case" }, h("div", { class: "when" }, s.when), rows(s.rows))),
    pv.moreRolls ? h("div", { class: "note" }, `And on ${plural(pv.moreRolls, "other roll")}.`) : null);
}
const formalText = text => h("details", { class: "formal" }, h("summary", {}, "Formal text"), h("pre", { class: "sexp" }, text));

/** A law's description, which is someone's words. The rule source below it is what counts. Space is
 *  kept for it while it is written, so nothing on the sheet moves when it arrives. */
function describedOf(d, badge = null) {
  const st = d?.status || "none";
  const line = st === "pack" ? `${d.pack}'s own words` : "Claude's description";
  if (st === "none" || st === "failed") return h("div", { class: "described" + (st === "failed" ? " held" : "") }, badge ? h("div", { class: "byline" }, badge) : null,
    h("p", { class: "nowords" }, "Claude has not described this law. The rule source below is what counts."));
  return h("div", { class: "described held" }, h("div", { class: "byline" }, h("span", {}, line), badge),
    st === "writing"
      ? h("div", { class: "ghost", role: "status", "aria-label": "Claude is writing a description" }, h("i"), h("i"), h("i"))
      : h("p", { class: "saying" }, d.text));
}
/** The rule source, as it prints, with line breaks added so that it can be read. */
const SOURCE_LINES = new Set(["new-piece", "repeal", "for-each-player", "if", "transfer"]);
function laidOut(text) {
  let out = "", depth = 0, quoted = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (quoted) { out += c; if (c === "\\") out += text[++i] ?? ""; else if (c === '"') quoted = false; continue; }
    if (c === '"') quoted = true;
    else if (c === "(") {
      const head = /^[^\s()"]*/.exec(text.slice(i + 1))[0];
      if (depth > 0 && (head.startsWith("on-") || head.startsWith("set-") || SOURCE_LINES.has(head))) out = out.trimEnd() + "\n" + "  ".repeat(depth);
      depth++;
    } else if (c === ")") depth--;
    out += c;
  }
  return out;
}
/** The source on the screen. A long line wraps with an indent, so the shape of the law stays clear. */
const sourceLines = text => laidOut(text).split("\n").map(line => {
  const indent = line.length - line.trimStart().length;
  return h("span", { class: "srcline", style: { paddingLeft: `${indent + 2}ch`, textIndent: "-2ch" } }, line.trimStart());
});
const sourceOf = text => h("div", { class: "source" }, h("div", { class: "byline" }, h("span", {}, "Rule source")), h("pre", { class: "sexp" }, sourceLines(text)));

/** The charter at a vote: the description, consequences and source the proposer saw, then the signatures. */
function voteDoc(p) {
  const v = G.view;
  const byYou = p.by === v.you;
  if (p.kind === "deal") return dealDoc(p);
  const votes = new Map(p.votes.map(x => [x.seat, x.yes]));
  const lines = v.seats.map(s => {
    const has = votes.has(s.seat);
    const key = `${p.id}:${s.seat}`;
    const fresh = has && !G.stampsSeen.has(key);
    if (has) G.stampsSeen.add(key);
    return h("div", { class: "sigline" }, shield(s.seat, seatColor(s.seat)), h("span", { class: "nm" }, nameOf(s.seat)),
      has ? h("span", { class: "stamp " + (votes.get(s.seat) ? "yes" : "no") + (fresh && !reduced() ? " fresh" : "") }, votes.get(s.seat) ? "YES" : "NO") : null);
  });
  return h("div", {},
    h("div", { class: "smallcaps" }, `${byYou ? "Your rule" : `${seat(p.by)?.name}'s rule`} · ${p.title}`),
    describedOf(p.description),
    consequences(p.preview),
    p.stale ? h("p", { class: "note-line" }, "Moves since it was proposed changed these figures.") : null,
    sourceOf(p.text),
    h("div", { class: "signatures" }, lines),
    h("div", { class: "tally" }, p.canPass ? (p.yesNeeded ? `${plural(p.yesNeeded, "more yes vote")} needed.` : "") : "It can no longer pass."),
    p.canVote ? h("div", { class: "votebar" },
      h("button", { class: "act", onclick: () => castVote(p.id, true), title: "Y" }, "Yes"),
      h("button", { class: "act", onclick: () => castVote(p.id, false), title: "N" }, "No")) : null);
}
function settleHopeless() {
  const p = (G.view?.proposals || []).find(x => x.id === G.dock?.id);
  if (G.dock?.t !== "vote" || !p || p.kind !== "law" || p.canPass || p.canVote) return;
  if (G.hopeless === p.id) return;
  G.hopeless = p.id;
  // A quiet ending: it stays open by the rules until its proposer's turn, but nothing can change it.
  setTimeout(() => { if (G.dock?.t === "vote" && G.dock.id === p.id) { closeDock(); caption(`"${p.title}" cannot pass now.`); } }, 3000);
}
function castVote(id, yes) { post("vote", { id, yes }); }
function dealDoc(p) {
  const v = G.view;
  const signed = new Set(p.signed);
  return h("div", {},
    h("div", { class: "smallcaps" }, `${p.by === v.you ? "Your deal" : `${seat(p.by)?.name}'s deal`} · ${p.title}`),
    statementOf(p.english),
    formalText(p.text),
    h("div", { class: "signatures" }, p.signers.map(s => h("div", { class: "sigline" }, shield(s, seatColor(s)), h("span", { class: "nm" }, nameOf(s)),
      signed.has(s) ? h("span", { class: "stamp yes" }, "SIGNED") : null))),
    p.canSign ? h("div", { class: "votebar" }, h("button", { class: "act gold", onclick: () => post("sign", { id: p.id }) }, "Sign")) : null);
}

const constitutionLink = words => h("button", { class: "link constitutionlink", onclick: () => openDock({ t: "constitution" }) }, words);
/** Laws and running deals: a compact home, with the terms one line each. */
function lawsDoc() {
  const v = G.view;
  const laws = v.laws || [], deals = v.deals || [];
  return h("div", {},
    h("div", { class: "lawshead" }, h("h2", {}, "In force"), laws.length || deals.length ? constitutionLink("Under the constitution") : null),
    v.game?.blurb && (v.laws || []).some(l => l.by == null) ? h("p", { class: "note-line" }, `${v.game.name}: ${v.game.blurb}`) : null,
    !laws.length && !deals.length ? h("p", { class: "empty" }, "Only ", constitutionLink("the constitution"), ".") : null,
    laws.map(l => h("div", { class: "lawrow" + (l.by == null ? " founding" : ""), "data-pick": l.pick },
      h("div", { class: "head" }, h("span", { class: "ttl" }, l.title), h("span", { class: "num" }, `Law ${l.id}`)),
      describedOf(l.description),
      sourceOf(l.text),
      l.by != null ? h("div", { class: "meta" }, `${nameOf(l.by)} proposed it in round ${l.round}. ${l.votes.filter(x => x.yes).length} yes, ${l.votes.filter(x => !x.yes).length} no.`) : h("div", { class: "meta" }, "In force from the founding. A majority can repeal it."))),
    deals.map(d => h("details", { class: "lawrow" },
      h("summary", {},
        h("div", { class: "head" }, h("span", { class: "ttl" }, `Deal until round ${d.lastRound}`)),
        h("p", { class: "english" }, d.english)),
      d.canExit ? h("button", { class: "link", onclick: () => post("exit", { dealId: d.id }) }, "Give notice") : null,
      h("pre", { class: "sexp" }, d.text))));
}

/** The chronicle tells only what the log holds, by round, newest at the bottom. */
function renderChronicle() {
  const U = G.ui, v = G.view;
  const sheet = U.sheet;
  const atEnd = !sheet.firstChild?.classList?.contains("chron") || sheet.scrollTop + sheet.clientHeight >= sheet.scrollHeight - 24;
  const lines = (v.chronicle || []).filter(l => G.everyEvent || l.major);
  const groups = [];
  for (const l of lines) {
    const r = l.round ?? 0;
    if (!groups.length || groups[groups.length - 1].r !== r) groups.push({ r, lines: [] });
    groups[groups.length - 1].lines.push(l);
  }
  const heading = r => r === 0 ? "The founding" : ROUND_WORDS[r] ? `The ${ROUND_WORDS[r]} round` : `Round ${r}`;
  fill(sheet, h("div", { class: "chron" },
    h("h2", {}, "Chronicle"),
    h("button", { class: "link toggleline", onclick: () => { G.everyEvent = !G.everyEvent; renderChronicle(); } }, G.everyEvent ? "Only what matters" : "Every event"),
    !lines.length ? h("p", { class: "empty" }, "Nothing has happened yet.") : null,
    groups.map(g => [h("h3", {}, heading(g.r)), g.lines.map(l => h("p", { class: (l.major ? "" : "minor") + (/The law passed|The deal started|The game ended/.test(l.text) ? " law" : "") }, l.actor != null ? shield(l.actor, seatColor(l.actor)) : null, l.text))])));
  if (atEnd) sheet.scrollTop = sheet.scrollHeight;
}

// ---------------------------------------------------------------- table talk
// What the server sends is what this viewer may read: the filter is on the server.
async function fetchTalk() {
  const q = new URLSearchParams();
  if (G.replay) q.set("at", G.replay.at);
  let r;
  try { r = await api(`/api/games/${G.code}/talk?${q}`); } catch { return; }
  if (!r?.ok) return;
  const before = G.talk.length, first = G.talkCount < 0;
  G.talk = r.lines; G.talkCount = r.count;
  if (first) G.talkSeen = G.replay ? 0 : r.lines.length;
  const fresh = r.lines.slice(before).filter(l => l.kind === "public" && l.by !== you());
  if (fresh.length && G.dock?.t !== "talk" && !G.moment) caption(`${seat(fresh[fresh.length - 1].by)?.name}: ${fresh[fresh.length - 1].text}`);
  if (G.dock?.t === "talk") renderTalk();
  renderRail();
}
function renderTalk() {
  const U = G.ui, v = G.view, sheet = U.sheet;
  const box = sheet.querySelector(".talkinput input");
  const typed = box?.value || "", focused = box && document.activeElement === box;
  const toWas = sheet.querySelector(".talkinput select")?.value ?? "";
  const atEnd = !sheet.querySelector(".talk") || sheet.scrollTop + sheet.clientHeight >= sheet.scrollHeight - 24;
  G.talkSeen = G.talk.length;
  const secret = G.talk.some(l => l.kind === "confession" || l.kind === "interview");
  const lines = G.talk.filter(l => G.talkAll || !secret || l.kind === "public" || l.kind === "private");
  const line = l => {
    const who = l.by === v.you ? "You" : seat(l.by)?.name ?? `Seat ${l.by}`;
    if (l.kind === "public") return h("p", {}, shield(l.by, seatColor(l.by)), h("b", {}, who), " ", l.text);
    if (l.kind === "private") return h("p", { class: "aside" }, shield(l.by, seatColor(l.by)), h("b", {}, who), ` to ${nameOf(l.to)}: `, l.text);
    return h("p", { class: "inner" }, shield(l.by, seatColor(l.by)), h("span", { class: "smallcaps" }, l.kind === "interview" ? "After the game" : "Confessional"), " ", h("b", {}, who), " ", l.text);
  };
  const seated = v.you != null && v.phase !== "ended" && !G.replay;
  const input = seated ? h("form", { class: "talkinput", onsubmit: e => { e.preventDefault(); sendTalk(e.currentTarget); } },
    h("input", { class: "input", "aria-label": "Say something", placeholder: "Say something", maxlength: 500, value: typed }),
    h("select", { "aria-label": "To" }, h("option", { value: "" }, "All"), v.seats.filter(x => x.seat !== v.you).map(x => h("option", { value: x.seat, selected: String(x.seat) === toWas ? true : null }, x.name))),
    h("button", { class: "act" }, "Say")) : null;
  fill(sheet, h("div", { class: "talk" },
    h("h2", {}, "Table talk"),
    secret ? h("button", { class: "link toggleline", onclick: () => { G.talkAll = !G.talkAll; renderTalk(); } }, G.talkAll ? "Only what was said at the table" : "With confessionals") : null,
    h("div", { class: "talklines" }, !lines.length ? h("p", { class: "empty" }, "Nobody has said anything yet.") : null, lines.map(line)),
    input));
  if (atEnd) sheet.scrollTop = sheet.scrollHeight;
  if (focused) sheet.querySelector(".talkinput input").focus();
}
async function sendTalk(form) {
  const box = form.querySelector("input"), to = form.querySelector("select").value;
  const text = box.value.trim();
  if (!text) return;
  box.value = "";
  await post("talk", to === "" ? { text } : { text, to: Number(to) });
  fetchTalk();
}

// ---------------------------------------------------------------- watching a game from its log
// A replay asks the server for the game after each log entry. It holds no game rules either.
async function startReplay(fromStart) {
  clearTimeout(G.polling);
  const last = await api(`/api/games/${G.code}/view?at=999999`);
  if (!last?.replay) return;
  const marks = (last.chronicle || []).filter(l => l.major).map(l => l.event + 1);
  const total = last.replay.total;
  G.replay = { at: total, total, playing: false, marks, timer: null };
  G.token = null;
  seatToken = null;
  G.talk = []; G.talkCount = -1;
  gotoEvent(fromStart ? (marks[0] || 1) : total, false);
}
async function gotoEvent(n, smooth) {
  const r = G.replay;
  r.at = Math.max(1, Math.min(n, r.total));
  const v = await api(`/api/games/${G.code}/view?at=${r.at}`);
  if (!v?.code || !G.replay) return;
  if (!smooth) {
    G.seenDecisions = null; G.seenProposals = null; G.endShown = false;
    (G.momentTimers || []).forEach(clearTimeout);
    G.inFlight = {};
    G.moment = null; G.holdScene = false; document.querySelectorAll(".flying").forEach(x => x.remove());
    if (G.dock?.t === "moment" || G.dock?.t === "vote" || G.dock?.t === "end") G.dock = null;
    G.talk = [];
  }
  const prev = smooth ? G.view : null;
  G.view = v; G.version = v.version;
  afterView(prev, v);
  fetchTalk();
  renderReplay();
}
function replayTick() {
  const r = G.replay; if (!r?.playing) return;
  if (r.at >= r.total) { r.playing = false; renderReplay(); return; }
  // A law's moment takes the screen for a while. Wait for it.
  if (!G.moment && !document.hidden) gotoEvent(r.at + 1, true);
  r.timer = setTimeout(replayTick, 650);
}
function renderReplay() {
  const r = G.replay, U = G.ui;
  U.replayBar.hidden = !r;
  if (!r) return;
  const next = r.marks.find(m => m > r.at);
  fill(U.replayBar,
    h("button", { class: "act", title: "Back one event", "aria-label": "Back one event", onclick: () => { r.playing = false; gotoEvent(r.at - 1, false); } }, "‹"),
    h("button", { class: "act gold", title: r.playing ? "Pause" : "Play", onclick: () => { r.playing = !r.playing; clearTimeout(r.timer); renderReplay(); if (r.playing) replayTick(); } }, r.playing ? "Pause" : "Play"),
    h("button", { class: "act", title: "Forward one event", "aria-label": "Forward one event", onclick: () => { r.playing = false; gotoEvent(r.at + 1, true); } }, "›"),
    h("button", { class: "act", disabled: !next, title: "To the next thing worth telling", onclick: () => { r.playing = false; gotoEvent(next, true); } }, "Next moment"),
    h("input", { class: "scrub", type: "range", min: 1, max: r.total, value: r.at, "aria-label": "Event", onchange: e => { r.playing = false; gotoEvent(Number(e.target.value), false); } }),
    h("span", { class: "fine" }, `Event ${r.at} of ${r.total}`));
}

// ---------------------------------------------------------------- the moment a law ends
function trackDecisions(v) {
  const list = v.decisions || [];
  if (G.seenDecisions == null) { G.seenDecisions = list.length; return false; }
  if (list.length <= G.seenDecisions) return false;
  const fresh = list.slice(G.seenDecisions);
  G.seenDecisions = list.length;
  const d = fresh[fresh.length - 1];
  if (d.outcome === "lapsed") { caption(`"${d.title}" lapsed without a majority.`); return false; }
  startMoment(d);
  return d.outcome === "passed";
}
function trackProposals(prev, v) {
  const open = (v.proposals || []).map(p => p.id);
  if (G.seenProposals == null) { G.seenProposals = new Set(open); return; }
  for (const p of v.proposals || []) {
    if (G.seenProposals.has(p.id)) continue;
    G.seenProposals.add(p.id);
    if (p.kind === "law") for (const x of p.votes) G.stampsSeen.add(`${p.id}:${x.seat}`);
    const busy = G.moment || G.dock?.t === "constitution" || (G.dock?.t === "draft" && (document.activeElement === G.ui.words || (G.draft && !G.draft.outcome)));
    if (!busy && (p.kind === "law" || p.canSign)) { G.dock = { t: "vote", id: p.id }; }
    else caption(`${seat(p.by)?.name} proposed: ${p.kind === "deal" ? p.english : p.description?.text || `"${p.title}"`}`);
  }
  // Move on to the next open document when one closes.
  if (G.dock?.t === "vote" && !open.includes(G.dock.id) && !G.moment) {
    const next = (v.proposals || []).find(p => p.canVote || p.canSign);
    G.dock = next ? { t: "vote", id: next.id } : null;
  }
}
const SEAL_FALL_MS = 240; // when the seal in .sealmark.fresh meets the page, in app.css
function startMoment(d) {
  // A new outcome replaces one still on screen.
  (G.momentTimers || []).forEach(clearTimeout);
  document.querySelectorAll(".flying").forEach(n => n.remove());
  const dockBefore = G.moment ? G.moment.prior : G.dock;
  const prior = dockBefore && dockBefore.t !== "vote" && dockBefore.t !== "moment" ? dockBefore : null;
  G.moment = { d, prior };
  G.dock = { t: "moment" };
  if (d.outcome === "passed") {
    G.holdScene = true;
    const seal = reduced() ? 200 : 900, carry = reduced() ? 400 : 2000;
    G.momentTimers = [
      setTimeout(() => { if (G.moment) G.moment.sealed = true; renderDock(); thump(G.ui.dock, 3, SEAL_FALL_MS); }, seal),
      setTimeout(() => carryToMonument(d), carry)];
  } else {
    G.holdScene = false;
    G.momentTimers = [setTimeout(() => endMoment(), reduced() ? 1500 : 2600)];
  }
}
function momentDoc(m) {
  if (!m) return null;
  const d = m.d;
  // This document is drawn again on every poll. Its outcome and its seal land only the first time.
  const landing = (m.sealed ? "sealed" : "open") !== m.told;
  m.told = m.sealed ? "sealed" : "open";
  const votes = new Map(d.votes.map(x => [x.seat, x.yes]));
  const lines = G.view.seats.map(s => {
    const has = votes.has(s.seat), key = `${d.id}:${s.seat}`, fresh = has && !G.stampsSeen.has(key);
    if (has) G.stampsSeen.add(key);
    return h("div", { class: "sigline" }, shield(s.seat, seatColor(s.seat)), h("span", { class: "nm" }, nameOf(s.seat)),
      has ? h("span", { class: "stamp " + (votes.get(s.seat) ? "yes" : "no") + (fresh && !reduced() ? " fresh" : "") }, votes.get(s.seat) ? "YES" : "NO") : null);
  });
  const passed = d.outcome === "passed";
  const yes = d.votes.filter(x => x.yes).length, no = d.votes.length - yes;
  return h("div", { class: "momentdoc" },
    h("div", { class: "smallcaps" }, d.title),
    describedOf(d.description),
    sourceOf(d.text),
    h("div", { class: "signatures" }, lines),
    h("div", { class: "outcome " + (passed ? "passed" : "failed") + (landing && (m.sealed || !passed) ? " fresh" : "") }, passed ? (m.sealed ? `Enacted, ${yes} to ${no}.` : `${yes} to ${no}.`) : "It did not take effect."),
    passed && m.sealed ? h("div", { class: "sealmark" + (landing ? " fresh" : "") }, waxSeal()) : null);
}
function carryToMonument(d) {
  const sheet = G.ui.dock;
  const from = sheet.getBoundingClientRect();
  // Open the world first: the scene shows the new monument as the charter arrives.
  const finish = () => {
    G.holdScene = false;
    endMoment();
    refreshScene().then(() => {
      // The monument drops in. The ring marks where it lands, once the camera has settled.
      setTimeout(() => {
        const at = G.player?.screenOf?.(d.pick);
        if (at && !reduced()) {
          spawn(h("div", { class: "ripple law", style: { left: `${at.x}px`, top: `${at.y}px` } }), 950);
          thump(G.ui.canvas, 3);
        }
        caption(`"${d.title}" stands in the square.`);
      }, 320);
    });
  };
  if (reduced() || !G.player) { finish(); return; }
  // Where the square is: the first tile is the middle of the board.
  const t = G.view.board?.tiles?.[0];
  const to = t ? G.player.worldToScreen(t.x, 0.4, t.y) : { x: innerWidth / 2, y: innerHeight / 2 };
  const ghost = sheet.cloneNode(true);
  ghost.className = "flying vellum";
  ghost.style.cssText = `left:${from.left}px;top:${from.top}px;width:${from.width}px;height:${from.height}px;transform-origin:center;`;
  document.body.append(ghost);
  G.dock = null; sheet.classList.remove("open");
  sheet.style.transition = "none";
  requestAnimationFrame(() => (sheet.style.transition = ""));
  const dx = to.x - (from.left + from.width / 2), dy = to.y - (from.top + from.height / 2);
  ghost.animate([
    { transform: "none", opacity: 1 },
    { transform: `translate(${dx * .5}px, ${dy * .5}px) scale(.42) rotate(-3deg)`, opacity: 1, offset: .55 },
    { transform: `translate(${dx}px, ${dy}px) scale(.04) rotate(-6deg)`, opacity: .2 },
  ], { duration: 760, easing: "cubic-bezier(.5,0,.4,1)", fill: "forwards" }).onfinish = () => { if (ghost.isConnected) { ghost.remove(); finish(); } };
}
function endMoment() {
  const m = G.moment; G.moment = null;
  G.dock = m?.prior || null;
  if (!G.dock) {
    const next = (G.view?.proposals || []).find(p => p.canVote || p.canSign);
    if (next) G.dock = { t: "vote", id: next.id };
  }
  renderDock(); renderRail(); renderPrompt(); renderLedge(); renderCenter(); updateInsets();
}

// ---------------------------------------------------------------- what changed: feedback in the world
// This runs once per real change, comparing the last view with the new one. The new view is already on
// the screen and its moves can already be made. These motions only tell the eye what happened.
const DIE_MS = 360;      // a roll tumbles this long, and then the harvest flies
const FLIGHT_MS = 620;   // a card's way from the table to its seat
const CARD_GAP_MS = 70;  // between one card and the next
const LAND_MS = 300;     // a new piece's fall in the 3D table, from the view until it meets the board
const MANY_CARDS = 4;    // a payout this big is a payday

const boardEl = () => G.use3d ? G.ui.canvas : G.ui.svg;
/** Where a point on the board is on the screen, on either board. */
function boardPoint(at, height = 0.35) {
  if (G.use3d) return G.player?.worldToScreen(at.x, height, at.y);
  const m = G.ui.svg.getScreenCTM();
  return m && { x: m.a * at.x * SCALE + m.e, y: m.d * at.y * SCALE + m.f };
}
const squareOf = v => (v.board?.tiles || []).find(t => !t.res) || v.board?.tiles?.[0];
const cardOf = r => G.ui.ledge.hidden ? null : G.ui.hand.querySelector(`[data-key="${CSS.escape(r)}"]`);
const bannerOf = s => G.ui.houses.querySelector(`[data-key="${s}"]`);

function animateChanges(prev, v) {
  if (!prev || prev.phase === "lobby" || !v.seats) return;
  const lines = (v.chronicle || []).slice((prev.chronicle || []).length);
  const byLaw = lines.filter(l => l.kind === "money" && l.text.startsWith("By law"));
  // A caption for what the other seats just did, so their turns can be watched without the log.
  // What a law just did always gets one: otherwise the cards seem to move by themselves.
  const told = lines.filter(l => l.major && l.actor !== v.you && l.kind !== "law");
  if (byLaw.length) caption(byLaw[0].text + (byLaw.length > 1 ? ` And ${byLaw.length - 1} more.` : ""));
  else if (told.length) caption(told[told.length - 1].text);

  const rolled = v.rollsMade !== prev.rollsMade;
  const hit = rolled ? (v.board?.tiles || []).filter(t => t.number === v.lastRoll) : [];
  const changes = v.seats.flatMap(s => {
    const was = prev.seats?.find(x => x.seat === s.seat);
    return !was?.hand ? [] : v.resources.map(r => ({ seat: s.seat, r, d: (s.hand[r] || 0) - (was.hand[r] || 0) })).filter(c => c.d);
  });
  const gained = changes.filter(c => c.seat === v.you && c.d > 0).reduce((a, c) => a + c.d, 0);

  if (rolled) rollDie(!hit.length, gained >= MANY_CARDS);
  if (rolled && !reduced()) for (const t of hit) setTimeout(() => ring(boardPoint(t), "small"), DIE_MS);
  if (byLaw.length) lawFires(v, rolled ? DIE_MS : 0);

  // Pieces. The ring finds where someone built. Your own piece has some weight.
  const was = new Set((prev.pieces || []).map(p => JSON.stringify(p)));
  const built = (v.pieces || []).filter(p => !was.has(JSON.stringify(p))).map(p => ({ ...p, at: pieceAt(p, v) }));
  const mineBuilt = built.find(p => p.owner === v.you && p.at);
  if (!G.holdScene && !reduced()) for (const p of built) {
    if (!p.at) continue;
    setTimeout(() => {
      ring(boardPoint(p.at), "small");
      if (p.owner === v.you) thump(boardEl(), (v.pieceDefs || []).find(d => d.name === p.kind)?.points ? 3 : 1.5);
    }, LAND_MS);
  }

  // Cards. Those that come from the table fly. A trade drops them in from above the hand.
  let wait = rolled ? DIE_MS : byLaw.length ? 120 : 0;
  for (const { seat: s, r, d } of changes) {
    const earned = rolled || byLaw.length;
    const tile = hit.find(t => t.res === r);
    const from = () => earned ? boardPoint(tile || squareOf(v)) : null;
    if (s === v.you && cardOf(r)) {
      if (d < 0) takeCards(r, -d, mineBuilt && boardPoint(mineBuilt.at));
      else wait += payCards(r, d, from(), wait) * CARD_GAP_MS;
    } else if (d > 0 && earned && !reduced()) {
      const banner = bannerOf(s);
      if (banner) flight(h("div", { class: "flight chip" }, resIcon(r, "res small"), `+${d}`), from(), middleOf(banner), wait);
    }
  }
  if (gained >= MANY_CARDS && !reduced()) setTimeout(() => thump(G.ui.hand, 4), wait + FLIGHT_MS);

  // Scores, then what is yours to do.
  for (const s of v.seats) {
    const was = prev.seats?.find(x => x.seat === s.seat);
    if (was && was.points !== s.points) scoreMoved(s.seat, s.points - was.points);
  }
  const yourTurn = v.turn === v.you && v.phase !== "ended";
  if (yourTurn && prev.turn !== v.you) yourMove();
  else if (yourTurn) for (const d of v.pieceDefs || []) {
    // Something you could not build, you now can.
    if (d.spots > 0 && !(prev.pieceDefs || []).find(x => x.name === d.name)?.spots)
      anim(G.ui.tray.querySelector(`[data-key="${CSS.escape(d.name)}"]`), [{ scale: 1.12, boxShadow: "0 0 0 3px var(--gold)" }, { scale: 1, boxShadow: "0 0 0 0 var(--gold)" }], { duration: 520 });
  }
  if (v.winner != null && prev.winner == null) thump(boardEl(), 4);
}

function pieceAt(p, v) {
  const spots = v.board?.spots || [];
  if (p.spot != null) return spots[p.spot];
  const [a, b] = (p.link || []).map(i => spots[i]);
  return a && b ? { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 } : null;
}
function ring(at, kind = "") {
  if (at) spawn(h("div", { class: `ripple ${kind}`, style: { left: `${at.x}px`, top: `${at.y}px` } }), 950);
}

/** The die tumbles, and its number settles on the true one. A number no hex pays lands harder, as does a payday. */
function rollDie(hard, payday) {
  const die = G.ui.herald.querySelector(".die");
  if (!die || reduced()) return;
  clearInterval(G.dieTimer);
  let flips = 0;
  G.dieTimer = setInterval(() => {
    if (++flips < 6) die.textContent = String(2 + Math.floor(Math.random() * 11));
    else { clearInterval(G.dieTimer); die.textContent = String(G.view.lastRoll); }
  }, DIE_MS / 6);
  const drop = hard || payday ? 1.3 : 1;
  die.animate([
    { translate: "0 -40px", rotate: "-200deg", scale: .8 },
    { translate: "0 -14px", rotate: "-40deg", scale: 1, offset: .62 },
    { translate: `0 ${5 * drop}px`, rotate: "4deg", scale: `${1 + .14 * drop} ${1 - .12 * drop}`, offset: .82 },
    { translate: "0 0", rotate: "0deg", scale: 1 },
  ], { duration: DIE_MS * 1.3, easing: "cubic-bezier(.3,.2,.6,1)" });
  if (hard) {
    die.animate([{ background: "var(--ink)", color: "var(--vellum)" }, { background: "var(--ink)", color: "var(--vellum)", offset: .6 }, { background: "var(--vellum)", color: "var(--ink)" }], { duration: 1100, delay: DIE_MS });
    thump(boardEl(), 3, DIE_MS);
  }
}

/** A law just moved goods: its seal strikes the square, where the laws stand. */
function lawFires(v, delay) {
  if (reduced() || !squareOf(v)) return;
  setTimeout(() => {
    const at = boardPoint(squareOf(v), 0.4);
    if (!at) return;
    ring(at, "law small");
    anim(spawn(h("div", { class: "lawfire", style: { left: `${at.x}px`, top: `${at.y}px` } }, waxSeal("fired")), 900),
      [{ scale: 2.2, opacity: 0 }, { scale: 1, opacity: 1, offset: .22 }, { scale: 1, opacity: 1, offset: .72 }, { scale: 1, opacity: 0 }], { duration: 900 });
  }, delay);
}

/** Something flies over the table to where it belongs, in a short arc. */
function flight(node, from, to, delay, landed) {
  if (!from || !to) { landed?.(); return; }
  const dx = to.x - from.x, dy = to.y - from.y, lift = Math.min(70, Math.hypot(dx, dy) * .16);
  Object.assign(node.style, { left: `${from.x}px`, top: `${from.y}px` });
  spawn(node, delay + FLIGHT_MS).animate([
    { transform: "translate(-50%,-50%) scale(.5) rotate(-10deg)", opacity: 0 },
    { transform: `translate(calc(-50% + ${dx * .42}px), calc(-50% + ${dy * .42 - lift}px)) scale(1.1) rotate(-4deg)`, opacity: 1, offset: .42 },
    { transform: `translate(calc(-50% + ${dx}px), calc(-50% + ${dy}px)) scale(.92)`, opacity: 1 },
  ], { duration: FLIGHT_MS, delay, fill: "both", easing: "cubic-bezier(.35,.1,.45,1)" });
  setTimeout(() => landed?.(), delay + FLIGHT_MS);
}
const looseCard = r => h("div", { class: "flight card" }, resIcon(r));

/** Cards land in the hand one at a time, and the count goes up as each one lands. Past a few, the last one
 *  stands for the rest. Returns how many flew. Without motion, the hand has already changed. */
function payCards(r, n, from, delay) {
  const card = cardOf(r);
  if (reduced()) { markCard(card, `+${n}`, true); return 0; }
  const start = from || { x: middleOf(card).x, y: card.getBoundingClientRect().top - 90 };
  const flying = Math.min(n, 4);
  G.inFlight[r] = (G.inFlight[r] || 0) + n;
  renderHand();
  for (let i = 0; i < flying; i++) {
    flight(looseCard(r), start, middleOf(card), delay + i * CARD_GAP_MS, () => {
      const last = i === flying - 1;
      G.inFlight[r] = Math.max(0, (G.inFlight[r] || 0) - (last ? n - flying + 1 : 1));
      renderHand();
      anim(cardOf(r), [{ translate: "0 -7px", scale: 1.07 }, { translate: "0 2px", scale: .99, offset: .55 }, { translate: "0 0", scale: 1 }], { duration: 200 });
      if (last) markCard(cardOf(r), `+${n}`, true);
    });
  }
  return flying;
}
/** Cards leave the hand: toward the piece they paid for, or just up and away. */
function takeCards(r, n, toward) {
  const card = cardOf(r);
  markCard(card, `−${n}`, false);
  if (reduced()) return;
  const from = card.getBoundingClientRect(), mid = middleOf(card);
  for (let i = 0; i < Math.min(n, 3); i++) {
    const c = looseCard(r);
    Object.assign(c.style, { left: `${mid.x}px`, top: `${mid.y}px`, width: `${from.width}px`, height: `${from.height}px` });
    const dx = toward ? toward.x - mid.x : (i - 1) * 10, dy = toward ? toward.y - mid.y : -70;
    spawn(c, 460 + i * CARD_GAP_MS).animate([
      { transform: "translate(-50%,-50%)", opacity: 1 },
      { transform: `translate(calc(-50% + ${dx}px), calc(-50% + ${dy}px)) scale(.4) rotate(${toward ? 8 : -8}deg)`, opacity: .15 },
    ], { duration: 440, delay: i * CARD_GAP_MS, fill: "both", easing: "cubic-bezier(.4,0,.7,.6)" });
  }
}
/** A small tag beside a card or a banner, which says how much just changed. */
function markCard(el, text, up, below) {
  if (!el) return;
  const r = el.getBoundingClientRect();
  const tag = spawn(h("span", { class: "delta" + (up ? " up" : ""), style: { left: `${r.right}px`, top: `${below ? r.bottom + 12 : r.top}px` } }, text), 1400);
  anim(tag, [{ translate: "-50% -30%", opacity: 0 }, { translate: "-50% -70%", opacity: 1, offset: .12 }, { translate: "-50% -70%", opacity: 1, offset: .75 }, { translate: "-50% -110%", opacity: 0 }], { duration: 1400, easing: "ease-out" });
}

function scoreMoved(s, d) {
  const b = bannerOf(s);
  if (!b) return;
  markCard(b.querySelector(".cloth"), `${d > 0 ? "+" : "−"}${Math.abs(d)}`, d > 0, true);
  thump(b.querySelector(".cloth"), 8);
  anim(b.querySelector(".score"), [{ scale: 1 }, { scale: 1.45, offset: .3 }, { scale: 1 }], { duration: 460 });
}

/** It has become your turn. The line that says what to do, or a pennant if none shows, and your tools come up. */
function yourMove() {
  const U = G.ui;
  anim(U.ledge, { transform: ["scaleX(0)", "scaleX(1)"], opacity: [1, 1, 0] }, { pseudoElement: "::before", duration: 760 });
  [...U.tray.children].forEach((t, i) => anim(t, [{ translate: "0 18px", opacity: 0 }, { translate: "0 0", opacity: 1 }], { duration: 240, delay: i * 30, fill: "backwards" }));
  if (!U.prompt.hidden) { anim(U.prompt, [{ scale: ".5 1", opacity: 0 }, { scale: "1.05 1", opacity: 1, offset: .6 }, { scale: 1, opacity: 1 }], { duration: 300 }); return; }
  const pennant = spawn(h("div", { class: "pennant" + (G.dock ? " dock-open" : "") }, "Your move"), 1200);
  anim(pennant, [
    { scale: ".3 1", opacity: 0 }, { scale: "1.06 1", opacity: 1, offset: .18 }, { scale: 1, opacity: 1, offset: .26 },
    { scale: 1, opacity: 1, offset: .78 }, { scale: 1, opacity: 0 },
  ], { duration: 1200, easing: "ease-out" });
}

// ---------------------------------------------------------------- the trade sheet
function renderTrade() {
  const v = G.view, U = G.ui;
  if (!G.tf) G.tf = { give: null, giveN: 1, get: null, getN: 1, to: "", rounds: 1 };
  const f = G.tf;
  const trades = (v.legalMoves || []).filter(m => m.move.t === "bankTrade");
  const byGive = new Map();
  for (const m of trades) { if (!byGive.has(m.move.give)) byGive.set(m.move.give, []); byGive.get(m.move.give).push(m); }
  const others = v.seats.filter(s => s.seat !== v.you);
  const pick = (key, label) => h("div", { class: "pickrow" }, h("span", { class: "lbl" }, label),
    goodsInPlay(v).map(r => h("button", { class: f[key] === r ? "on" : "", title: capital(r), "aria-label": r, onclick: () => { f[key] = r; renderTrade(); } }, resIcon(r, "res"))),
    h("input", { class: "num", type: "number", min: 1, value: f[key + "N"], "aria-label": `${label} amount`, onchange: e => { f[key + "N"] = Number(e.target.value) || 1; } }));
  const repeat = Number(f.rounds) > 1;
  const canOffer = f.give && f.get && f.give !== f.get || (f.give && f.get && repeat);
  fill(U.sheet, h("div", { class: "tradesheet" },
    h("h3", {}, `The bank takes ${v.bankRate} for 1`),
    byGive.size ? [...byGive.entries()].map(([give, ms]) => h("div", { class: "bankrow" },
      h("span", { class: "pay" }, String(v.bankRate), resIcon(give, "res small")), h("span", { class: "arrow" }, "→"),
      ms.map(m => h("button", { title: m.label, "aria-label": m.label, onclick: () => postMove(m.move) }, resIcon(m.move.get, "res"))))) :
      h("div", { class: "note-line" }, `You hold less than ${v.bankRate} of everything.`),
    h("div", { class: "offerform" },
      h("h3", {}, "Offer the table"),
      pick("give", "Give"), pick("get", "Get"),
      h("div", { class: "selectline" },
        h("select", { "aria-label": "To", onchange: e => { f.to = e.target.value; renderTrade(); } },
          repeat ? null : h("option", { value: "", selected: f.to === "" ? true : null }, "To anyone"),
          others.map(s => h("option", { value: s.seat, selected: String(f.to) === String(s.seat) ? true : null }, `To ${s.name}`))),
        h("span", {}, "Rounds"), h("input", { class: "num", type: "number", min: 1, value: f.rounds, title: "1 is a single trade. More is a deal, paid each round from a deposit.", onchange: e => { f.rounds = Math.max(1, Number(e.target.value) || 1); if (f.rounds > 1 && f.to === "") f.to = others[0]?.seat ?? ""; renderTrade(); } })),
      repeat ? h("div", { class: "note-line", style: { margin: 0 } }, "A deal. It binds only those who sign, and pays each round from a deposit.") : null,
      h("button", { class: "act gold", disabled: !canOffer, onclick: () => submitOffer() }, repeat ? "Propose the deal" : "Make the offer"))));
}
function submitOffer() {
  const f = G.tf;
  if (Number(f.rounds) > 1) {
    post("propose", { dealForm: { with: Number(f.to), give: f.give, giveN: f.giveN, get: f.get, getN: f.getN, rounds: Number(f.rounds), exitNotice: 1 } }).then(r => { if (r.ok) closeDock(); });
  } else {
    postMove({ t: "offer", to: f.to === "" ? null : Number(f.to), give: [{ res: f.give, n: f.giveN }], get: [{ res: f.get, n: f.getN }] }).then(r => { if (r.ok) closeDock(); });
  }
}

// ---------------------------------------------------------------- the drafting desk
// One document, from the player's words to the table. The words stay editable through every stage.
function buildDraftDesk() {
  const U = G.ui;
  U.words = h("textarea", { class: "words", "aria-label": "The rule you want", placeholder: "Write the rule you want, in your own words." });
  const grow = () => { U.words.style.height = "auto"; U.words.style.height = `${Math.min(U.words.scrollHeight + 2, 200)}px`; };
  U.growWords = grow;
  U.words.addEventListener("input", () => { store.set(`charter.words.${G.code}`, U.words.value); grow(); renderDraft(); });
  U.words.addEventListener("keydown", e => { if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); submitDraft(); } });
  U.draftBtn = h("button", { class: "act gold", onclick: () => submitDraft() }, "Draft it");
  U.cancelBtn = h("button", { class: "act", onclick: () => cancelDraft() }, "Cancel");
  U.suggestBtn = h("button", { class: "link", onclick: () => askSuggestion() }, "Suggest a rule");
  U.samplesBox = h("div", { class: "samples" });
  U.draftBody = h("div", {});
  U.proposeBar = h("div", { class: "proposebar", hidden: true });
  U.draftBar = h("div", { class: "draftbar" }, U.draftBtn, U.cancelBtn, U.suggestBtn);
  U.desk = h("div", {}, h("h2", {}, "A new rule"), U.words, U.draftBar, U.samplesBox, U.draftBody, U.proposeBar);
}
async function submitDraft(sample) {
  const words = G.ui.words.value.trim();
  if (!sample && !words) { G.ui.words.focus(); return; }
  G.draftGen = (G.draftGen || 0) + 1;
  const gen = G.draftGen;
  G.draft = { stage: "sent", words, elapsedMs: 0, quietMs: 0, text: "", thinking: "", attempt: 1, optimistic: true };
  renderDraft(); renderRail();
  const r = await api(`/api/games/${G.code}/draft`, sample ? { token: G.token, sample } : { token: G.token, words });
  if (gen !== G.draftGen) return;
  if (r.ok === false) { G.draft = { outcome: "failed", reason: r.error, words }; renderDraft(); return; }
  G.draft = r;
  if (sample && r.words != null) { G.ui.words.value = r.words; store.set(`charter.words.${G.code}`, r.words); }
  renderDraft(); renderRail();
  pollDraft();
}
// The clerk suggests a rule. It comes back as an ordinary draft, and its words go in the box.
async function askSuggestion() {
  G.draftGen = (G.draftGen || 0) + 1;
  const gen = G.draftGen;
  G.wordsBefore = G.ui.words.value;
  setWords("");
  G.draft = { stage: "sent", mode: "suggest", words: "", elapsedMs: 0, quietMs: 0, text: "", thinking: "", attempt: 1, optimistic: true };
  renderDraft(); renderRail();
  const r = await api(`/api/games/${G.code}/suggest`, { token: G.token });
  if (gen !== G.draftGen) return;
  if (r.ok === false) { G.draft = { outcome: "failed", mode: "suggest", reason: r.error, words: "" }; renderDraft(); return; }
  G.draft = r;
  renderDraft(); renderRail();
  pollDraft();
}
function setWords(text) {
  G.ui.words.value = text;
  if (text) store.set(`charter.words.${G.code}`, text); else store.del(`charter.words.${G.code}`);
  G.ui.growWords();
}
// A finished suggestion goes in the box, unless the player has started to write there.
function placeSuggestion(d) {
  if (d.mode !== "suggest" || d.outcome !== "ready" || G.suggestPlaced === d.id) return;
  G.suggestPlaced = d.id;
  if (!G.ui.words.value.trim()) setWords(d.words);
}
async function pollDraft() {
  clearTimeout(G.draftPolling);
  const gen = G.draftGen;
  let d;
  try { d = await api(`/api/games/${G.code}/draft`); }
  catch { if (gen === G.draftGen) G.draftPolling = setTimeout(pollDraft, 1000); return; }
  if (gen !== G.draftGen) return;
  if (d?.id == null) { if (G.draft && !G.draft.outcome && !G.draft.optimistic) { G.draft = { outcome: "failed", reason: "The server lost this draft. Try again.", words: G.ui.words.value }; renderDraft(); } return; }
  const beat = G.draft && (d.text !== G.draft.text || d.thinking !== G.draft.thinking || d.stage !== G.draft.stage);
  G.draft = d; G.draftBeat = beat;
  placeSuggestion(d);
  renderDraft(); renderRail();
  // A law's description fills in after the review is on screen.
  const wait = !d.outcome || d.review?.description?.status === "writing" ? pollWait(220) : null;
  if (wait != null) G.draftPolling = setTimeout(pollDraft, wait);
}
async function checkDraft() {
  try {
    const d = await api(`/api/games/${G.code}/draft`);
    if (d?.id != null && d.outcome !== "cancelled") {
      G.draft = d;
      if (!G.ui.words.value && d.words) G.ui.words.value = d.words;
      if (d.outcome) G.suggestPlaced = d.id;
      if (!d.outcome) pollDraft();
    }
  } catch {}
}
async function refreshDraftReview() {
  // Keep the consequences true to the table as it moves on.
  try {
    const d = await api(`/api/games/${G.code}/draft`);
    if (d?.id != null && d.outcome === "ready" && G.draft?.outcome === "ready") { G.draft = d; renderDraft(); }
  } catch {}
}
async function cancelDraft() {
  G.draftGen = (G.draftGen || 0) + 1;
  clearTimeout(G.draftPolling);
  if (G.draft?.mode === "suggest" && !G.ui.words.value.trim()) setWords(G.wordsBefore || "");
  G.draft = null;
  api(`/api/games/${G.code}/draft-cancel`, { token: G.token });
  renderDraft(); renderRail();
  G.ui.words.focus();
}
const STAGE_TEXT = {
  sent: "Sent to Claude. Waiting for a reply.", connected: "Claude has it.", thinking: "Claude is thinking.", drafting: "Claude is writing it out.",
  parsing: "Reading the draft.", checking: "Checking it against the constitution.", previewing: "Working out who gains and who pays.", done: "Finished.",
};
function renderDraft() {
  const U = G.ui, d = G.draft, v = G.view;
  if (!U.desk) return;
  const running = d && !d.outcome;
  const typed = U.words.value.trim();
  const same = d && (d.words || "").trim() === typed;
  const suggesting = d?.mode === "suggest";
  // Asking never takes away words the player wrote: it shows on an empty box, or on the clerk's own words.
  const canSuggest = !running && (!typed || (suggesting && same));
  U.cancelBtn.hidden = !running;
  U.draftBtn.hidden = running;
  U.draftBtn.disabled = !typed;
  fill(U.draftBtn, d?.outcome === "ready" && !same ? "Redraft" : !suggesting && (d?.outcome === "refused" || d?.outcome === "failed") ? "Draft again" : "Draft it");
  U.draftBtn.classList.toggle("gold", !(d?.outcome === "ready" && same));
  U.draftBtn.hidden = running || (d?.outcome === "ready" && same);
  U.suggestBtn.hidden = !canSuggest;
  fill(U.suggestBtn, suggesting && d?.outcome === "ready" ? "Suggest another" : "Suggest a rule");
  U.draftBar.hidden = !running && d?.outcome === "ready" && same && !canSuggest;
  // Ready-made laws, one click away, while the desk is empty.
  U.samplesBox.hidden = !!d || !!typed;
  if (!d && !typed) fill(U.samplesBox, (v?.samples || []).slice(0, 5).map(s => h("button", { class: "link", title: s.text, onclick: () => submitDraft(s.id) }, s.title)));
  U.proposeBar.hidden = true;
  if (!d) { fill(U.draftBody); return; }
  if (running) { fill(U.draftBody, draftingView(d)); return; }
  if (suggesting && (d.outcome === "refused" || d.outcome === "failed")) {
    fill(U.draftBody, h("p", { class: "fail" }, d.reason));
    return;
  }
  if (d.outcome === "refused") {
    const landing = G.refusedShown !== d.id;
    G.refusedShown = d.id;
    fill(U.draftBody, h("div", { class: "refusal" }, h("div", { class: "stampword" + (landing ? " fresh" : "") }, "REFUSED"), h("p", {}, d.reason)));
    return;
  }
  if (d.outcome === "failed") {
    fill(U.draftBody, h("p", { class: "fail" }, d.reason),
      h("details", { class: "formal" }, h("summary", {}, "Write it in formal text"), h("pre", { class: "sexp" }, '(law "A title" (set-bank-rate 3))')));
    return;
  }
  if (d.outcome === "cancelled") { fill(U.draftBody); return; }
  const rv = d.review;
  if (!rv) { fill(U.draftBody, h("p", { class: "fail" }, "This rule no longer reads against the table. Draft it again.")); return; }
  fill(U.draftBody, h("div", { class: same ? "" : "dim" },
    d.why ? h("div", { class: "advice" }, h("div", { class: "advicehead" }, d.whyStale ? "The clerk's advice, before the table last changed" : "The clerk's advice"), h("p", {}, d.why)) : null,
    h("div", { class: "titleline" }, rv.title),
    rv.kind === "deal" ? statementOf(rv.statement) : describedOf(rv.description, rv.difference ? h("span", { class: "notasked", title: "The clerk compared this rule with your words. This says nothing about the description." }, "Not exactly what you asked") : null),
    rv.difference ? h("p", { class: "diff" }, h("span", { class: "diffby" }, "The clerk, on your request: "), rv.difference) : null,
    consequences(rv.preview),
    rv.kind === "deal" ? formalText(rv.text) : sourceOf(rv.text)));
  const bar = U.proposeBar;
  bar.hidden = !same;
  if (same) {
    fill(bar, h("button", { class: "act gold", disabled: !rv.canPropose, onclick: () => proposeDraft(rv.text) }, "Propose"));
  }
}
function draftingView(d) {
  const stalled = d.quietMs > 15000;
  const secs = Math.floor((d.elapsedMs || 0) / 1000);
  const tick = h("span", { class: "tick" + (G.draftBeat ? " beat" : "") });
  // A suggestion's reply has labelled lines. While it comes in, show only the words it proposes.
  const shown = d.mode === "suggest" ? (/^WORDS:\s*(.*)$/m.exec(d.text || "")?.[1] || "") : d.text;
  const statusText = stalled ? `Nothing from Claude for ${Math.floor(d.quietMs / 1000)} s.` : (d.optimistic ? "Sending to Claude." : STAGE_TEXT[d.stage] || d.stage);
  return h("div", {},
    h("div", { class: "status" + (stalled ? " stalled" : "") }, stalled ? null : tick, h("span", {}, statusText), h("span", { class: "elapsed" }, `${secs} s`)),
    d.attempt > 1 ? h("p", { class: "retryline" }, `The last draft was sent back. ${d.retryReason} Trying again.`) : null,
    d.thinking && d.stage === "thinking" ? h("p", { class: "thought" }, lastSentences(d.thinking)) : null,
    shown ? h("div", { class: "clerk" }, shown, d.stage === "drafting" ? h("span", { class: "nib" }) : null) : null);
}
function lastSentences(t) {
  const clean = t.replace(/\s+/g, " ").trim();
  const start = clean.indexOf(" ", 0);
  return clean.length >= 240 ? clean.slice(start + 1) : clean;
}
async function proposeDraft(text) {
  const r = await post("propose", { text });
  if (!r?.ok) return;
  await api(`/api/games/${G.code}/draft-clear`, { token: G.token });
  G.draft = null;
  G.ui.words.value = "";
  store.del(`charter.words.${G.code}`);
  renderDraft();
  G.dock = null; G.dismissed = null;
  renderDock(); renderRail(); updateInsets();
  poke();
}

// ---------------------------------------------------------------- the gathering and the end
function renderCenter() {
  const v = G.view, U = G.ui;
  if (v.phase === "lobby") { fill(U.center, gathering(v)); return; }
  if (v.phase === "ended" && !G.endShown && !G.moment) { G.endShown = true; G.dock = { t: "end" }; renderDock(); renderRail(); updateInsets(); }
  fill(U.center);
}
function gathering(v) {
  const slots = [];
  for (let i = 0; i < v.maxSeats; i++) {
    const s = v.seats.find(x => x.seat === i);
    slots.push(h("div", { class: "seatbanner" + (s ? "" : " empty") }, s ? bannerCloth(i) : h("span", { class: "cloth" }), h("span", {}, s ? (s.seat === v.you ? "You" : s.name) : "")));
  }
  const open = v.maxSeats - v.filled;
  const invite = `${location.origin}/?join=${v.code}`;
  return scrollSheet(
    h("div", { class: "smallcaps" }, "The table"),
    h("div", { class: "bigcode", title: invite }, v.code),
    h("p", { class: "packnote" }, h("b", {}, v.game?.name), `. ${v.game?.blurb || ""}`),
    h("button", { class: "link", onclick: e => { navigator.clipboard?.writeText(invite); e.currentTarget.textContent = "Copied"; } }, "Copy the invitation"),
    h("div", { class: "seats" }, slots),
    v.you == null ? h("p", { class: "note-line" }, "You are watching. Join from the title page.") : null,
    h("div", { class: "gatherbar" },
      open > 0 ? h("button", { class: "act", onclick: () => post("bot", {}) }, "Add a bot") : null,
      open > 0 ? h("button", { class: "act", onclick: () => post("claude", {}) }, "Add Claude") : null,
      v.you != null && v.filled >= v.minSeats && open > 0 ? h("button", { class: "act gold", onclick: () => post("start", {}) }, `Begin with ${v.filled}`) : null));
}
function proclamation(v) {
  const w = seat(v.winner);
  const order = [...v.seats].sort((a, b) => b.points - a.points);
  const pieces = s => Object.entries(s.pieces || {}).filter(([k, n]) => n > 0 && !(v.look?.quietPieces || []).includes(k)).map(([k, n]) => plural(n, k))
    .concat(s.tokenPoints ? [`${plural(s.tokenPoints, "point")} from what they held`] : []).join(", ");
  const nLaws = (v.laws || []).length;
  // The result is sealed, and the seal lands only the first time it is drawn.
  const landing = !G.endSealed;
  G.endSealed = true;
  return h("div", { class: "proclaim" },
    h("div", { class: "sealmark" + (landing ? " fresh" : "") }, waxSeal()),
    h("div", { class: "smallcaps" }, v.round >= v.rounds && w?.points < v.target ? `All ${v.rounds} rounds played` : `Round ${v.round}`),
    h("h2", {}, v.winner === v.you ? `${capital(v.game?.word || "the island")} is yours.` : `${capital(v.game?.word || "the island")} is ${w?.name}'s.`),
    order.map(s => h("div", { class: "standing" }, shield(s.seat, seatColor(s.seat)), h("span", {}, nameOf(s.seat)), h("span", { class: "fine" }, pieces(s)), h("b", {}, String(s.points)))),
    h("p", { class: "note-line", style: { marginTop: "12px" } }, nLaws ? `${plural(nLaws, "law")} in force at the end.` : "It ended under the constitution alone."),
    v.realTokens ? h("p", { class: "note-line" }, `The Claude seats at this table spent ${v.realTokens.toLocaleString("en-US")} real tokens.`) : null,
    h("details", { class: "formal" }, h("summary", {}, "Check the dice"), h("div", { class: "fine", style: { fontFamily: "var(--mono)", fontSize: "12px", wordBreak: "break-all" } }, `Seed ${v.serverSeed}. Fingerprint published at the start: ${v.fingerprint}.`)),
    h("div", { class: "bar" }, h("button", { class: "act", onclick: () => openDock({ t: "chronicle" }) }, "Read the chronicle")));
}

// ---------------------------------------------------------------- keys
function onKey(e) {
  const tag = document.activeElement?.tagName;
  const typing = tag === "TEXTAREA" || tag === "INPUT" || tag === "SELECT";
  if (e.key === "Escape") {
    if (G.ui.pickmenu && !G.ui.pickmenu.hidden) { closePickMenu(); return; }
    if (G.selected) { selectPiece(G.selected); return; }
    if (G.menu) { G.menu = false; renderMenu(); renderRail(); return; }
    if (typing) { document.activeElement.blur(); return; }
    if (G.dock) { closeDock(true); return; }
    return;
  }
  if (typing || e.metaKey || e.ctrlKey || e.altKey) return;
  const v = G.view; if (!v) return;
  const k = e.key.toLowerCase();
  if (k === "e") endTurn();
  else if (k === "r" && v.you != null && v.phase === "actions") { e.preventDefault(); toggleDock({ t: "draft" }); }
  else if (k === "l") toggleDock({ t: "laws" });
  else if (k === "c") toggleDock({ t: "chronicle" });
  else if (k === "m" && v.phase !== "lobby") toggleDock({ t: "talk" });
  else if (k === "t" && v.turn === v.you && v.phase === "actions") toggleDock({ t: "trade" });
  else if (k === "v" && (v.proposals || []).length) toggleDock({ t: "vote", id: (v.proposals.find(p => p.canVote || p.canSign) || v.proposals[0]).id });
  else if ((k === "y" || k === "n") && G.dock?.t === "vote") {
    const p = (v.proposals || []).find(x => x.id === G.dock.id);
    if (p?.canVote) castVote(p.id, k === "y");
  } else if (/^[1-9]$/.test(k) && v.turn === v.you && v.phase === "actions") {
    const d = (v.pieceDefs || [])[Number(k) - 1];
    if (d?.spots) selectPiece(d.name);
  }
}

if (params.has("debug")) window.G = G;
const code = params.get("game");
if (code) gameScreen(code.toUpperCase()); else lobby();
