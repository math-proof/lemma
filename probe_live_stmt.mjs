
import { readFileSync } from "fs";
import { compile } from "./js/parser/lean.js";

const path = "Lemma/Random/ExpectFunPowDot/eq/Integral_Ext_FunPowDot/of/GtInftySup/All_Differentiable_Prob/All_NeProb_0/All_LeNormFunPowDot/All_MeasurableFun/IsPolicyTrajectory/In_Ico0.lean";
let src = readFileSync(path, "utf8");
// Cut at first `:= by` after private lemma main to avoid walking the huge proof
const marker = "private lemma main";
const i = src.indexOf(marker);
const j = src.indexOf(":= by", i);
if (i < 0 || j < 0) throw new Error("markers");
const head = src.slice(0, j) + ":= by\n  trivial\n";
const tree = compile(head);
function findInts(n, acc=[], seen=new Set()) {
  if (!n || typeof n !== "object" || seen.has(n)) return acc;
  seen.add(n);
  if (n.constructor?.name === "Lean_int") acc.push(n);
  for (const k of Object.keys(n)) {
    const v = n[k];
    if (Array.isArray(v)) v.forEach(c => findInts(c, acc, seen));
    else if (v && typeof v === "object" && String(v.constructor?.name||"").startsWith("Lean")) findInts(v, acc, seen);
  }
  return acc;
}
const ints = findInts(tree);
console.log("ints", ints.length);
for (const [idx, n] of ints.entries()) {
  const mp = n.measurePartial();
  console.log(idx, "scope", n.scope?.constructor?.name, "mp", !!mp);
  let out = n.latexFormat();
  for (const a of n.latexArgs({})) out = out.replace("%s", a);
  const both = /\\partial/.test(out) && /mathrm\{d\}/.test(out);
  console.log(" both partial+d?", both);
  console.log(" TAIL", out.slice(-200));
}
