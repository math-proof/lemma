import fs from "fs";
import { createRequire } from "module";
import { pathToFileURL } from "url";
import { compile } from "./js/parser/lean.js";
const full = fs.readFileSync("Lemma/Real/Ramanujan/Part1Ch5Entry2iEuleriangf.lean","utf8");
const lines = full.split(/\n/);
const headerN = 25;
function ok(n) {
  const src = lines.slice(0, n).join("\n") + "\n";
  try { compile(src); return true; } catch { return false; }
}
let lo = headerN, hi = lines.length;
console.log("total", lines.length, "full_ok", ok(lines.length));
while (lo + 1 < hi) {
  const mid = Math.floor((lo + hi) / 2);
  if (ok(mid)) lo = mid; else hi = mid;
}
console.log("first failing line number:", hi);
console.log("context:");
for (let i = Math.max(0, hi-15); i < Math.min(lines.length, hi+5); i++) {
  console.log(String(i+1).padStart(4), lines[i]);
}
