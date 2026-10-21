
import { compile } from "./js/parser/lean.js";
import { render2vueFromSource } from "./mjs/lean/compiler/index.mjs";

function check(label, lean) {
  const mini = `lemma probe :\n${lean}\n := by trivial\n`;
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
  console.log("===", label, "ints", ints.length);
  for (const [i, n] of ints.entries()) {
    const mp = n.measurePartial();
    console.log(" int", i, "scope", n.scope?.constructor?.name, "mp", mp ? "YES "+mp.arg?.constructor?.name : "null");
    let fmt = n.latexFormat();
    const args = n.latexArgs({});
    let out = fmt;
    for (const a of args) out = out.replace("%s", a);
    const hasD = /mathrm\{d\}/.test(out);
    const hasP = /\\partial/.test(out);
    console.log("  has partial", hasP, "has mathrm{d}", hasD);
    console.log("  TAIL", out.slice(-180));
  }
  const code = render2vueFromSource(mini, {});
  const imply = code.lemma?.[0]?.imply;
  const text = typeof imply === "string" ? imply : JSON.stringify(imply);
  const both = /\\partial/.test(text) && /\\mathrm\{d\}/.test(text);
  console.log(" imply both partial+d?", both);
  console.log(" imply tail", text.slice(-220));
  return !both;
}

const ok1 = check("Expect=Integral newline partial", `
  𝔼[r, s, a : M θ](
    (γ ^ (id : ℕ → ℕ)) @ fun t ↦ X) =
  ∫ ω,
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X (r · ω))) • Y) ∂(M θ)
`);

const ok2 = check("Integral=g multiline partial then eq", `
  ∫ ω, f ω
    ∂(M θ) =
  g
`);

const ok3 = check("plain dx integral", `
  ∫ x, x ^ 2
`);

console.log("RESULTS", {ok1, ok2, ok3});
