
import { readFileSync, writeFileSync } from "fs";
import { render2vueFromSource } from "./mjs/lean/compiler/index.mjs";
import { compile } from "./js/parser/lean.js";

const path = "Lemma/Random/ExpectFunPowDot/eq/Integral_Ext_FunPowDot/of/GtInftySup/All_Differentiable_Prob/All_NeProb_0/All_LeNormFunPowDot/All_MeasurableFun/IsPolicyTrajectory/In_Ico0.lean";
const src = readFileSync(path, "utf8");

// Also dump AST shape of the imply integral
const tree = compile(src);
function walk(n, depth=0, path="") {
  if (!n || typeof n !== "object") return;
  const name = n.constructor?.name || "?";
  if (name === "Lean_int" || name === "Lean_partial" || name === "LeanEq" || name.includes("Expect") || name === "LeanArgsIndented" || name === "LeanArgsSpaceSeparated") {
    const indent = "  ".repeat(depth);
    let extra = "";
    if (name === "Lean_int") {
      try {
        const mp = n.measurePartial?.();
        extra = ` measurePartial=${mp ? mp.constructor.name + "(" + (mp.arg?.constructor?.name) + ")" : null}`;
      } catch (e) { extra = " measurePartialERR=" + e.message; }
    }
    console.log(indent + name + extra + " @" + path);
  }
  if (depth > 25) return;
  for (const k of ["args","bound","scope","lhs","rhs","arg","imply","statement"]) {
    const v = n[k];
    if (Array.isArray(v)) v.forEach((c,i) => walk(c, depth+1, path+"."+k+"["+i+"]"));
    else if (v && typeof v === "object") walk(v, depth+1, path+"."+k);
  }
  // lemma list
  if (Array.isArray(n.lemmas)) n.lemmas.forEach((c,i)=>walk(c, depth+1, path+".lemmas["+i+"]"));
}

console.log("=== AST walk (filtered) ===");
walk(tree);

const code = render2vueFromSource(src, {});
writeFileSync("/tmp/probe_out.json", JSON.stringify(code, null, 2));
console.log("keys", Object.keys(code));
console.log("error", code.error);
const lemmas = code.lemma;
console.log("lemma", Array.isArray(lemmas) ? "array"+lemmas.length : typeof lemmas);
if (Array.isArray(lemmas)) {
  for (let i=0;i<lemmas.length;i++) {
    const L = lemmas[i];
    console.log("lemma", i, "keys", Object.keys(L));
    for (const f of ["imply","statement","latex","name","title"]) {
      if (L[f] == null) continue;
      const v = typeof L[f] === "string" ? L[f] : JSON.stringify(L[f]);
      console.log("---", f, "len", v.length);
      // find dω / partial near end
      const markers = ["mathrm{d}", "partial", "int"];
      for (const m of markers) {
        const idx = v.lastIndexOf(m);
        if (idx >= 0) console.log("  last", m, "at", idx);
      }
      console.log(v.slice(Math.max(0, v.length-900)));
    }
  }
}
