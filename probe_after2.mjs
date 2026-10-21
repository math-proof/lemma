
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
    console.log(" int", i, "scope", n.scope?.constructor?.name,
      "parent", n.parent?.constructor?.name,
      "mp", mp ? "YES" : "null");
    let out = n.latexFormat();
    for (const a of n.latexArgs({})) out = out.replace("%s", a);
    console.log("  has partial", /\\partial/.test(out), "has d", /mathrm\{d\}/.test(out));
    console.log("  TAIL", out.slice(-160).replace(/\n/g,"\\n"));
  }
  // Is the root imply an Eq with int on lhs?
  const code = render2vueFromSource(mini, {});
  const L = code.lemma?.[0];
  let text = L?.imply ?? L?.statement ?? "";
  if (typeof text !== "string") text = JSON.stringify(text) || "";
  console.log(" imply both?", /\\partial/.test(text) && /\\mathrm\{d\}/.test(text));
  console.log(" imply has = outside?", text.includes("=") || text.includes("\\eq"));
  console.log(" imply tail", String(text).slice(-200).replace(/\n/g,"\\n"));
}

check("multiline partial then eq", `
  ∫ ω, f ω
    ∂(M θ) =
  g
`);

check("plain dx", `∫ x, x ^ 2`);

check("space-separated same line", `∫ ω, f ω ∂(M θ)`);
