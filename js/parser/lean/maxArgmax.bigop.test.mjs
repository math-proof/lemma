/**
 * max / min / sup / inf / max⁻¹ / min⁻¹ promote to LeanLimitsBigOp (bound+scope).
 * Bare `max` and ordinary `x[i]` stay Token / GetElem.
 * Run: `node js/parser/lean/maxArgmax.bigop.test.mjs`
 */
import { compile } from "../lean.js";

let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

function find(n, pred) {
  if (!n || typeof n !== "object") return null;
  if (pred(n)) return n;
  if (Array.isArray(n.args)) for (const a of n.args) {
    const r = find(a, pred);
    if (r) return r;
  }
  return null;
}

{
  const mod = compile("lemma m : max⁻¹[i:Fin n] (P : ℝ) = 0 := by sorry");
  const am = find(mod, (n) => n.constructor?.name === "Lean_argmax");
  check("argmax is Lean_argmax", !!am);
  check("argmax bound is Colon", am && am.bound?.constructor?.name === "LeanColon");
  check("argmax scope is Parenthesis", am && am.scope?.constructor?.name === "LeanParenthesis");
  check("argmax pathChoices has ArgMax", am?.pathChoices?.().includes("ArgMax"));
  const lx = mod.render2vue(false).lemma[0].imply.latex;
  check("argmax underset latex", lx.includes("\\underset{") && lx.includes("\\operatorname{max}^{-1}"));
  check("argmax no limits on ^{-1}", !/max\^{-1}\\limits/.test(lx) && !/operatorname\{max\}\^{-1}\\limits/.test(lx));
}

{
  const mod = compile("lemma m : min⁻¹[i:Fin n] f = 0 := by sorry");
  const am = find(mod, (n) => n.constructor?.name === "Lean_argmin");
  check("argmin is Lean_argmin", !!am);
  check("argmin scope is Token", am?.scope?.constructor?.name === "LeanToken");
  const lx = mod.render2vue(false).lemma[0].imply.latex;
  check("argmin underset latex", lx.includes("\\underset{") && lx.includes("\\operatorname{min}^{-1}"));
}

{
  const mod = compile("lemma m : max[i:Fin n] f = 0 := by sorry");
  const mx = find(mod, (n) => n.constructor?.name === "Lean_max");
  check("max is Lean_max", !!mx);
  check("max bound Colon", mx?.bound?.constructor?.name === "LeanColon");
  check("max pathChoices has Max", mx?.pathChoices?.().includes("Max"));
  const lx = mod.render2vue(false).lemma[0].imply.latex;
  check("max limits latex", lx.includes("\\max\\limits_"));
}

{
  const mod = compile("lemma m : min[i:Fin n] f = 0 := by sorry");
  check("min is Lean_min", !!find(mod, (n) => n.constructor?.name === "Lean_min"));
  check("min limits latex", mod.render2vue(false).lemma[0].imply.latex.includes("\\min\\limits_"));
}

{
  const mod = compile("lemma m : sup[i:Fin n] f = 0 := by sorry");
  check("sup is Lean_sup", !!find(mod, (n) => n.constructor?.name === "Lean_sup"));
  check("sup limits latex", mod.render2vue(false).lemma[0].imply.latex.includes("\\sup\\limits_"));
}

{
  const mod = compile("lemma m : inf[i:Fin n] f = 0 := by sorry");
  check("inf is Lean_inf", !!find(mod, (n) => n.constructor?.name === "Lean_inf"));
  check("inf limits latex", mod.render2vue(false).lemma[0].imply.latex.includes("\\inf\\limits_"));
}

{
  const mod = compile("lemma m : x[i] = 0 := by sorry");
  check("ordinary x[i] stays GetElem", !!find(mod, (n) => n.constructor?.name === "LeanGetElem"));
  check("ordinary x[i] not limits bigop", !find(mod, (n) => n.constructor?.name === "Lean_max"));
}

{
  const mod = compile("lemma m : max = 0 := by sorry");
  check("bare max stays Token", !!find(mod, (n) => n.constructor?.name === "LeanToken" && n.text === "max"));
  check("bare max not Lean_max", !find(mod, (n) => n.constructor?.name === "Lean_max"));
}

{
  const mod = compile("lemma m : max⁻¹[i:Fin n] (ℙ[π](x) : ℝ) = 0 := by sorry");
  const am = find(mod, (n) => n.constructor?.name === "Lean_argmax");
  const pr = find(mod, (n) => n.constructor?.name === "Lean_Prob");
  check("nested outer Lean_argmax", !!am);
  check("nested inner Lean_Prob", !!pr);
  check("ArgMaxProb path", am?.pathChoices?.().includes("ArgMaxProb"));
}

{
  const mod = compile("lemma m : max[y : T] f y = 0 := by sorry");
  const mx = find(mod, (n) => n.constructor?.name === "Lean_max");
  check("juxta body grows as SpaceSeparated scope", mx?.scope?.constructor?.name === "LeanArgsSpaceSeparated");
  check("echo glued brackets", String(mx).startsWith("max[y:T] "));
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log("all ok");
