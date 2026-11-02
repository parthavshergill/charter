// The table's sounds and each world's music. This is screen code and nothing depends on it: if a file does not
// load, or a browser has no Web Audio, every call here does nothing and the game goes on.
//
// Sounds are decoded in advance, so that one starts on the next audio block after the call. A sound that cannot
// start now is dropped, never queued, so nothing comes out in a burst later. The files are made by
// scripts/sound/render.py. It normalises them all, and SOUNDS below sets how loud each one plays.

const params = new URLSearchParams(location.search);
const OVERHANG = .25;       // seconds of a loop repeated at each end of its file, as in scripts/sound/render.py
const DEFAULT_TRACK = "table";
const CROSSFADE = 1.2;      // seconds between one world's music and the next
const MUSIC_LEVEL = .35;    // the music plays this far under the effects, on files made to -20 LUFS
const TABLE_DB = -12;       // another seat's routine sound, compared with the same sound of your own
const TABLE_MS = 400;       // and at most one of those in this long
const TABLE_BURST = 2;      // after a quiet spell, this many can come together
const MAX_VOICES = 14;
const RETURN_QUIET_MS = 1500; // after a hidden tab comes back, what it missed stays silent

// How each sound plays. n: its recorded takes. db: its level at full volume. vary: random pitch, in cents.
// gap: the least ms between two of it. big: it ignores the quiet after a hidden tab comes back, and it is not
// made quieter by repeats. always: it also plays in a hidden tab. duck: the music dips for this many ms.
const SOUNDS = {
  // your turn: the one cue that must always get through, and always the same, so that it is known at once
  "your-turn": { n: 1, db: -8, vary: 0, gap: 400, big: true, always: true, duck: 900 },
  // your hands
  tap: { n: 3, db: -27, vary: 60, gap: 30 }, tool: { n: 2, db: -20, vary: 25, gap: 30 }, "tool-off": { n: 1, db: -24, vary: 25, gap: 30 },
  "place-spot": { n: 3, db: -12, vary: 40, gap: 60 }, "place-link": { n: 3, db: -15, vary: 50, gap: 60 }, "place-up": { n: 2, db: -9, vary: 20, gap: 60 },
  refuse: { n: 2, db: -19, vary: 20, gap: 250 }, "end-turn": { n: 2, db: -19, vary: 30, gap: 200 },
  page: { n: 4, db: -27, vary: 120, gap: 80 }, "card-out": { n: 3, db: -27, vary: 120, gap: 50 },
  // dice
  "dice-rattle": { n: 3, db: -22, vary: 60, gap: 300 }, "dice-land": { n: 3, db: -16, vary: 50, gap: 300 }, "dice-hard": { n: 2, db: -13, vary: 40, gap: 300 },
  // goods
  coin: { n: 5, db: -21, vary: 30, gap: 40 }, payday: { n: 2, db: -15, vary: 0, gap: 900 },
  // trades
  "offer-in": { n: 1, db: -14, vary: 15, gap: 300, duck: 300 }, deal: { n: 1, db: -13, vary: 0, gap: 300 }, bank: { n: 2, db: -16, vary: 30, gap: 200 },
  // laws
  quill: { n: 4, db: -36, vary: 150, gap: 70 }, "draft-ready": { n: 1, db: -19, vary: 0, gap: 500 },
  "stamp-yes": { n: 3, db: -16, vary: 40, gap: 60 }, "stamp-no": { n: 3, db: -16, vary: 40, gap: 60 },
  "vote-call": { n: 1, db: -16, vary: 0, gap: 500, duck: 300 },
  seal: { n: 2, db: -8, vary: 20, gap: 400, big: true, duck: 700 }, "law-fail": { n: 1, db: -14, vary: 0, gap: 400 }, repeal: { n: 1, db: -10, vary: 0, gap: 400, big: true, duck: 700 },
  monument: { n: 1, db: -11, vary: 0, gap: 500 }, "law-fire": { n: 2, db: -20, vary: 30, gap: 700 },
  // big moments
  crash: { n: 1, db: -4, vary: 0, gap: 1000, big: true, duck: 1600 }, rumble: { n: 1, db: -7, vary: 0, gap: 800, big: true, duck: 1000 }, fall: { n: 2, db: -12, vary: 40, gap: 150 },
  rare: { n: 1, db: -10, vary: 0, gap: 500, big: true, duck: 800 }, lead: { n: 1, db: -11, vary: 0, gap: 3000, big: true, duck: 800 }, "lead-lost": { n: 1, db: -20, vary: 0, gap: 3000 },
  "score-up": { n: 2, db: -16, vary: 0, gap: 120 }, "score-down": { n: 1, db: -19, vary: 0, gap: 120 },
  win: { n: 1, db: -4, vary: 0, gap: 3000, big: true, duck: 3800 }, lose: { n: 1, db: -9, vary: 0, gap: 3000, big: true, duck: 2600 }, end: { n: 1, db: -9, vary: 0, gap: 3000, big: true, duck: 2200 },
  begin: { n: 1, db: -10, vary: 0, gap: 3000, big: true, duck: 1200 }, talk: { n: 2, db: -30, vary: 100, gap: 1500 },
};

const stored = k => { try { return localStorage.getItem(k); } catch { return null; } };
const keep = (k, v) => { try { localStorage.setItem(k, v); } catch { /* it is only a preference */ } };
const dB = d => 10 ** (d / 20);

let ctx = null, master = null, fxBus = null, musicBus = null;
let fxOn = stored("charter.sound.fx") !== "0";
// A person who asked to save data has the music off until they turn it on.
let musicOn = stored("charter.sound.music") ? stored("charter.sound.music") !== "0" : !navigator.connection?.saveData;
const takes = new Map();      // a sound's name to its decoded takes, as they arrive
const lastTake = new Map(), lastAt = new Map(), heat = new Map();
let voices = 0, plays = 0, quietUntil = 0, tableBudget = TABLE_BURST, tableAt = 0, preloading = false;
const log = params.has("debug") ? [] : null;
const note = (name, result, extra) => { if (log) { log.push({ name, result, t: performance.now(), ...extra }); if (log.length > 4000) log.shift(); } };

/** The context, once the browser allows it. It is made at the first press, or at page load for someone who
 *  has pressed something here before, since a browser may then let it start without asking again. */
function ensureContext() {
  if (ctx) return ctx;
  const Ctx = window.AudioContext || window.webkitAudioContext;
  if (!Ctx) return null;
  try {
    ctx = new Ctx({ latencyHint: "interactive" });
    master = ctx.createDynamicsCompressor(); // a soft top for when several sounds land together
    master.threshold.value = -5; master.knee.value = 6; master.ratio.value = 6; master.attack.value = .002; master.release.value = .12;
    fxBus = ctx.createGain(); fxBus.gain.value = fxOn ? 1 : 0;
    musicBus = ctx.createGain(); musicBus.gain.value = musicOn && !document.hidden ? MUSIC_LEVEL : 0;
    fxBus.connect(master); musicBus.connect(master); master.connect(ctx.destination);
    ctx.onstatechange = started;
  } catch (e) { console.warn("sound: no audio", e); ctx = null; }
  return ctx;
}
function started() {
  if (ctx?.state !== "running") return;
  keep("charter.sound.pressed", "1");
  for (const g of GESTURES) removeEventListener(g, unlock, true);
  preload();
  startWanted();
}
const GESTURES = ["pointerdown", "pointerup", "touchend", "click", "keydown"];
function unlock() {
  if (!ensureContext()) return;
  if (ctx.state === "running") started();
  else ctx.resume().catch(() => {});
}

const decode = bytes => new Promise((done, fail) => ctx.decodeAudioData(bytes, done, fail));
async function fetchAudio(path) {
  const r = await fetch(path);
  if (!r.ok) throw new Error(`${path}: ${r.status}`);
  return decode(await r.arrayBuffer());
}
/** Where a take's sound really starts. An MP3 decoder may leave some silence first, and that would be latency. */
function soundStart(buffer) {
  const x = buffer.getChannelData(0), limit = Math.min(x.length, Math.round(buffer.sampleRate * .15));
  for (let i = 0; i < limit; i++) if (Math.abs(x[i]) > .004) return Math.max(0, i - 24) / buffer.sampleRate;
  return 0;
}
async function preload() {
  if (preloading) return;
  preloading = true;
  const jobs = Object.entries(SOUNDS).flatMap(([name, s]) => Array.from({ length: s.n }, (_, i) => [name, i + 1]));
  let failed = 0;
  const worker = async () => {
    for (let job; (job = jobs.shift());) {
      const [name, i] = job;
      try {
        const buffer = await fetchAudio(`audio/fx/${name}-${i}.mp3`);
        if (!takes.has(name)) takes.set(name, []);
        takes.get(name).push({ buffer, offset: soundStart(buffer) });
      } catch (e) { if (!failed++) console.warn("sound: a file did not load, so that sound is left out", e); }
    }
  };
  await Promise.all([1, 2, 3, 4, 5, 6].map(worker));
  note("preloaded", "done", { files: [...takes.values()].reduce((a, t) => a + t.length, 0), failed });
}

/** Play a sound now, or `delay` ms from now on the audio clock. `table` makes it another seat's routine sound:
 *  much quieter, and limited to a few each second. `rate` changes its pitch, as a run of coins climbs. `gain`
 *  adds dB. Returns whether it will sound. */
export function play(name, { delay = 0, table = false, rate = 1, gain = 0 } = {}) {
  const s = SOUNDS[name];
  try {
    if (!s) { console.warn(`sound: no sound called ${name}`); return false; }
    if (!fxOn) { note(name, "off"); return false; }
    if (!ctx || ctx.state !== "running") { if (ctx?.state === "suspended") ctx.resume().catch(() => {}); note(name, "locked"); return false; }
    const list = takes.get(name);
    if (!list?.length) { note(name, "not loaded"); return false; }
    const now = performance.now();
    if (document.hidden && !s.always) { note(name, "hidden"); return false; }
    if (now < quietUntil && !s.big) { note(name, "returning"); return false; }
    // The same sound too soon after itself. Your own sounds do not give way to another seat's, which give way to anything.
    const landsAt = now + delay, tableKey = `${name}|table`;
    const near = key => Math.abs(landsAt - (lastAt.get(key) ?? -1e9));
    if (table ? Math.min(near(name), near(tableKey)) < Math.max(s.gap, TABLE_MS) : near(name) < s.gap) { note(name, "gap", { table }); return false; }
    if (table) {
      tableBudget = Math.min(TABLE_BURST, tableBudget + (now - tableAt) / TABLE_MS);
      tableAt = now;
      if (tableBudget < 1) { note(name, "table limit", { table }); return false; }
      tableBudget -= 1;
    }
    if (voices >= MAX_VOICES && !s.big) { note(name, "voices"); return false; }
    // A repeat in the same few seconds comes out a little quieter, so a run of the same thing fades back.
    const was = heat.get(name) || { v: 0, t: now };
    const warm = Math.max(0, was.v - (now - was.t) / 1000);
    heat.set(name, { v: warm + 1, t: now });
    const tired = s.big ? 0 : Math.min(6, Math.max(0, warm - 2) * .8);
    // A different take from the last, a slightly different pitch, a slightly different level.
    let i = Math.floor(Math.random() * list.length);
    if (list.length > 1 && i === lastTake.get(name)) i = (i + 1) % list.length;
    lastTake.set(name, i);
    const take = list[i];
    const src = ctx.createBufferSource(), level = ctx.createGain();
    src.buffer = take.buffer;
    src.playbackRate.value = rate * 2 ** ((Math.random() * 2 - 1) * s.vary / 1200);
    const db = s.db + gain + (table ? TABLE_DB : 0) - tired + (s.vary ? Math.random() * 2 - 1 : 0);
    level.gain.value = dB(db);
    src.connect(level);
    level.connect(fxBus);
    const when = ctx.currentTime + delay / 1000;
    src.start(when, take.offset);
    voices++;
    src.onended = () => { voices--; try { src.disconnect(); level.disconnect(); } catch { /* it has gone */ } };
    lastAt.set(table ? tableKey : name, landsAt);
    plays++;
    if (s.duck) duck(s.duck, delay);
    note(name, "played", { table, take: i, db, delay, when, audioNow: ctx.currentTime, rate: src.playbackRate.value, tired });
    return true;
  } catch (e) { console.warn("sound:", e); return false; }
}

/** A hidden tab has come back, or the table has moved a long way at once: what it missed stays silent. */
export function quietFor(ms) { quietUntil = Math.max(quietUntil, performance.now() + ms); }

function duck(ms, delay = 0) {
  if (!musicOn || !musicBus || document.hidden) return;
  const g = musicBus.gain, at = ctx.currentTime + delay / 1000;
  g.cancelScheduledValues(ctx.currentTime);
  g.setValueAtTime(g.value, ctx.currentTime);
  g.linearRampToValueAtTime(MUSIC_LEVEL * .5, at + .04);
  g.setValueAtTime(MUSIC_LEVEL * .5, at + ms / 1000);
  g.linearRampToValueAtTime(MUSIC_LEVEL, at + ms / 1000 + .7);
}
function setMusicLevel(to, seconds) {
  if (!musicBus) return;
  const g = musicBus.gain, now = ctx.currentTime;
  g.cancelScheduledValues(now);
  g.setValueAtTime(g.value, now);
  g.linearRampToValueAtTime(to, now + seconds);
}

// ---------------------------------------------------------------- music
let lengths = null, wanted = DEFAULT_TRACK, playing = null, waitTimer = null, gaveUp = null;
const decoded = new Map(); // the last two loops, so that going back and forth does not decode them again
/** A track's name comes from a pack's look, which arrives as data. It goes into an address only in this form. */
const trackName = t => typeof t === "string" && /^[a-z0-9-]{1,32}$/.test(t) ? t : DEFAULT_TRACK;

function loadTrack(track) {
  if (!decoded.has(track)) {
    decoded.set(track, fetchAudio(`audio/music/${track}.mp3`));
    while (decoded.size > 2) decoded.delete(decoded.keys().next().value);
  }
  return decoded.get(track).catch(e => { decoded.delete(track); throw e; });
}
async function startWanted() {
  if (!ctx || ctx.state !== "running" || !musicOn) return;
  const track = wanted;
  if (playing?.track === track) return;
  try {
    lengths ??= await fetch("audio/music/tracks.json").then(r => r.json());
    if (!lengths[track]) throw new Error(`no track called ${track}`);
    const buffer = await loadTrack(track);
    if (track !== wanted || !musicOn || playing?.track === track) return;
    const src = ctx.createBufferSource(), level = ctx.createGain(), now = ctx.currentTime;
    src.buffer = buffer;
    src.loop = true;
    src.loopStart = OVERHANG;
    src.loopEnd = OVERHANG + lengths[track];
    level.gain.setValueAtTime(0, now);
    level.gain.linearRampToValueAtTime(1, now + CROSSFADE);
    src.connect(level);
    level.connect(musicBus);
    src.start(now, OVERHANG);
    stopPlaying(CROSSFADE);
    playing = { track, src, level };
    note(`music:${track}`, "played", { seconds: lengths[track] });
  } catch (e) {
    // Once. The views keep coming, and each one asks for this world's music again.
    console.warn("sound: no music", e);
    gaveUp = track;
    if (track !== DEFAULT_TRACK && track === wanted) { wanted = DEFAULT_TRACK; startWanted(); }
  }
}
function stopPlaying(seconds) {
  if (!playing) return;
  const { src, level } = playing, now = ctx.currentTime;
  level.gain.cancelScheduledValues(now);
  level.gain.setValueAtTime(level.gain.value, now);
  level.gain.linearRampToValueAtTime(0, now + seconds);
  try { src.stop(now + seconds + .05); } catch { /* it has stopped */ }
  src.onended = () => { try { src.disconnect(); level.disconnect(); } catch { /* it has gone */ } };
  playing = null;
}
/** Show this world's music. Going quickly through the list of worlds loads only the one it stops at. */
export function setMusic(track) {
  const next = trackName(track);
  if (next === wanted && (playing?.track === next || !musicOn)) return;
  if (next === gaveUp) return;
  wanted = next;
  clearTimeout(waitTimer);
  waitTimer = setTimeout(startWanted, playing ? 180 : 0);
}

// ---------------------------------------------------------------- the switches
export const isOn = kind => kind === "music" ? musicOn : fxOn;
export function toggle(kind) {
  unlock();
  if (kind === "music") {
    musicOn = !musicOn;
    keep("charter.sound.music", musicOn ? "1" : "0");
    if (ctx) {
      if (musicOn) { gaveUp = null; setMusicLevel(document.hidden ? 0 : MUSIC_LEVEL, .1); startWanted(); }
      else { stopPlaying(.4); decoded.clear(); }
    }
  } else {
    fxOn = !fxOn;
    keep("charter.sound.fx", fxOn ? "1" : "0");
    if (fxBus) fxBus.gain.value = fxOn ? 1 : 0;
    if (fxOn) play("tool");
  }
  return isOn(kind);
}

// ---------------------------------------------------------------- starting
function start() {
  for (const g of GESTURES) addEventListener(g, unlock, { capture: true, passive: true });
  if (stored("charter.sound.pressed")) ensureContext();
  if (ctx?.state === "running") started();
  document.addEventListener("visibilitychange", () => {
    if (!ctx) return;
    if (document.hidden) { setMusicLevel(0, .3); return; }
    quietFor(RETURN_QUIET_MS);
    if (ctx.state !== "running") ctx.resume().catch(() => {});
    if (musicOn) setMusicLevel(MUSIC_LEVEL, .8);
  });
  // A button with no sound of its own gets a soft tap. Hovering makes no sound at all.
  let before = 0;
  addEventListener("click", () => { before = plays; }, true);
  addEventListener("click", e => {
    if (plays === before && e.target.closest?.("button:not(:disabled), a, summary")) play("tap");
  });
}
try { start(); } catch (e) { console.warn("sound: off", e); }

if (log) window.SOUND = { log, SOUNDS, play, setMusic, isOn, toggle, quietFor, state: () => ({ ctx: ctx?.state, baseLatency: ctx?.baseLatency, outputLatency: ctx?.outputLatency, sampleRate: ctx?.sampleRate, voices, loaded: [...takes.values()].reduce((a, t) => a + t.length, 0), wanted, playing: playing?.track, musicLevel: musicBus?.gain.value, fxOn, musicOn }), internals: () => ({ ctx, master, fxBus, musicBus, playing, decoded, takes, lengths }) };
