// Decodes scene streams with the same decoder the browser's player uses, and checks them.
import { readFileSync } from "node:fs";
import { decodeStream } from "../web/vendor/player.js";

const list = JSON.parse(readFileSync(process.argv[2], "utf8"));
let draws = 0;
for (const { file, picks, labels } of list) {
  const bytes = readFileSync(file);
  const buf = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
  const cmds = decodeStream(buf);
  const found = new Set(cmds.filter(c => (c.pick ?? 0) !== 0).map(c => c.pick));
  for (const p of picks) {
    if (!found.has(p)) throw new Error(`${file}: legal pick ${p} has no marker`);
  }
  const texts = cmds.filter(c => c.op === "label").map(c => c.text);
  for (const l of labels) {
    if (!texts.includes(l)) throw new Error(`${file}: the label "${l}" is missing`);
  }
  if (!cmds.some(c => c.op === "draw")) throw new Error(`${file}: nothing is drawn`);
  draws += cmds.length;
}
console.log(`decoded ${list.length} scenes, ${draws} commands`);
