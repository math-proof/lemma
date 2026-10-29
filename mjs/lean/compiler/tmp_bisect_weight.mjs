import { compile } from "../../../js/parser/lean.js";
import "../../../js/py.js";
import fs from "fs";
import { homedir } from "os";
import path from "path";

const src = fs.readFileSync(path.join(homedir(), "src/lean/Lemma/Int/WeightLE/of/BruhatLE.lean"), "utf8");
const lines = src.split("\n");

// find lemma starts
const starts = [];
for (let i = 0; i < lines.length; i++) {
  if (/^private lemma |^lemma /.test(lines[i]) || (/^\/--/.test(lines[i]) && i+3 < lines.length && /@\[path\]/.test(lines[i+3]||"") )) {
    // better: @[path] lines
  }
  if (lines[i] === "@[path]") starts.push(i);
}
console.log("path attrs at lines", starts.map(i => i+1).slice(0,10), "... total", starts.length);

// binary search by keeping first N path-lemmas (cut before next @[path] or at created)
function sliceFirstN(n) {
  if (n >= starts.length) return src;
  const cut = starts[n]; // 0-based line index of next @[path] to exclude
  // include up to line before the docstring of that lemma - go back to /--
  let cutLine = cut;
  while (cutLine > 0 && lines[cutLine] !== "/--") cutLine--;
  const head = lines.slice(0, cutLine).join("\n");
  return head + "\n\n\n-- created on 2026-10-23\n";
}

function tryN(n) {
  try {
    compile(sliceFirstN(n));
    return true;
  } catch (e) {
    return e.message.split("\n")[0];
  }
}

let lo = 0, hi = starts.length;
while (lo < hi) {
  const mid = Math.floor((lo + hi) / 2);
  const r = tryN(mid + 1); // first mid+1 lemmas
  console.log(`first ${mid+1}:`, r === true ? "OK" : r);
  if (r === true) lo = mid + 1;
  else hi = mid;
}
console.log("first failing lemma index", lo, "at line", starts[lo] + 1);
// show context
const i = starts[lo];
console.log(lines.slice(Math.max(0,i-5), i+40).join("\n"));
