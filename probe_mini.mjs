
import { readFileSync, writeFileSync } from "fs";
import { compile } from "./js/parser/lean.js";
import { render2vueFromSource } from "./mjs/lean/compiler/index.mjs";

// Minimal statement mirroring the live leaf shape (𝔼 = ∫ ω,\n  (f) ∂μ)
const mini = `
lemma probe
  {M : Type} {θ : M} {γ : ℝ} {ω : Type} {X : Type} {r s a : Type} :
  𝔼[r, s, a : M θ](
    (γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X r s a (t + k))) •
        ∇[θ] Real.log (ℙ[M θ](a[t] | s[t])).toReal)) =
  ∫ ω,
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X (r · ω) (s · ω) (a · ω) (t + k))) •
        ∇[θ] Real.log (ℙ[M θ](a[t] = (a t ω) | s[t] = (s t ω))).toReal) ∂(M θ) := by
  trivial
`;

const tree = compile(mini);
function findInts(n, acc=[], seen=new Set()) {
  if (!n || typeof n !== "object" || seen.has(n)) return acc;
  seen.add(n);
  if (n.constructor?.name === "Lean_int") acc.push(n);
  for (const k of Object.keys(n)) {
    const v = n[k];
    if (Array.isArray(v)) v.forEach(c => findInts(c, acc, seen));
    else if (v && typeof v === "object" && v.constructor?.name?.startsWith?.("Lean")) findInts(v, acc, seen);
  }
  return acc;
}
const ints = findInts(tree);
console.log("found Lean_int count", ints.length);
for (const [i, n] of ints.entries()) {
  const s = n.scope;
  console.log("--- int", i);
  console.log("  scope", s?.constructor?.name);
  if (s) {
    console.log("  scope.lhs", s.lhs?.constructor?.name);
    console.log("  scope.rhs", s.rhs?.constructor?.name);
    if (s.args) console.log("  scope.args", s.args.map(a => a?.constructor?.name));
    if (s.lhs?.args) console.log("  lhs.args", s.lhs.args.map(a => a?.constructor?.name));
    if (s.rhs?.args) console.log("  rhs.args", s.rhs.args.map(a => a?.constructor?.name));
  }
  const mp = n.measurePartial();
  console.log("  measurePartial", mp ? mp.constructor.name : null, mp?.arg?.constructor?.name);
  console.log("  latexFormat", n.latexFormat());
  try {
    const args = n.latexArgs({});
    console.log("  latexArgs tails", args.map(a => String(a).slice(-80)));
    // reconstruct roughly
    let fmt = n.latexFormat();
    let out = fmt;
    for (const a of args) out = out.replace("%s", a);
    console.log("  RECON", out.slice(-200));
  } catch (e) { console.log("  latexArgs ERR", e.message); }
}

const code = render2vueFromSource(mini, {});
const L = code.lemma?.[0];
console.log("lemma keys", L && Object.keys(L));
const imply = L?.imply ?? L?.statement ?? L?.latex;
const text = typeof imply === "string" ? imply : JSON.stringify(imply);
console.log("IMPLY_TAIL", text.slice(-400));
writeFileSync("/mnt/c/Users/Administrator/probe_mini_out.txt", text);
console.log("has both partial and mathrm{d}?", /\\\\partial/.test(text) && /\\\\mathrm\{d\}/.test(text));
console.log("partial count", (text.match(/\\\\partial/g)||[]).length, "d count", (text.match(/\\\\mathrm\{d\}/g)||[]).length);
