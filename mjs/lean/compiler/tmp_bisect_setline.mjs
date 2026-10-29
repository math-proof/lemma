import fs from "fs";
import { homedir } from "os";
import path from "path";
import { compile } from "../../../js/parser/lean.js";
import "../../../js/py.js";

const abs = path.join(homedir(), "src/lean/Lemma/Int/WeightSubspace/eq/ToSubmoduleWeightSpace.lean");
const src = fs.readFileSync(abs, "utf8");
const lines = src.split("\n");
const starts = [];
for (let i = 0; i < lines.length; i++) if (lines[i] === "@[path]") starts.push(i);

function sliceFirstN(n) {
  if (n >= starts.length) return src;
  let cutLine = starts[n];
  while (cutLine > 0 && lines[cutLine] !== "/--") cutLine--;
  return lines.slice(0, cutLine).join("\n") + "\n\n\n-- created on 2026-10-23\n";
}

function trySetLine(n) {
  try {
    const tree = compile(sliceFirstN(n));
    tree.set_line();
    return true;
  } catch (e) {
    return e.message.split("\n")[0];
  }
}

let lo = 0, hi = starts.length;
while (lo < hi) {
  const mid = Math.floor((lo + hi) / 2);
  const r = trySetLine(mid + 1);
  console.log(`first ${mid + 1}:`, r === true ? "OK" : r);
  if (r === true) lo = mid + 1;
  else hi = mid;
}
console.log("failing lemma index", lo, "line", starts[lo] + 1);
console.log(lines.slice(starts[lo] - 3, starts[lo] + 50).join("\n"));
