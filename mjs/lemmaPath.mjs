
import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import { compile } from "../static/js/parser/lean.js";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const LEMMA_ROOT = path.join(REPO, "Lemma");

const TYPE_TO_SECTION = {
  AbsoluteValue: "AbsoluteValue",
  IsNontrivial: "AbsoluteValue",
  IsEquiv: "AbsoluteValue",
  ProbabilityMeasure: "Random",
  IsProbabilityMeasure: "Random",
  MeasureSpace: "Random",
  AEMeasurable: "Random",
  PSpace: "Random",
  Measurable: "Measure",
  Measure: "Measure",
  Kernel: "Kernel",
  ENNReal: "ENNReal",
  NNReal: "ENNReal",
  Real: "Real",
  "ℝ": "Real",
  Complex: "Complex",
  "ℂ": "Complex",
  Nat: "Nat",
  "ℕ": "Nat",
  Int: "Int",
  "ℤ": "Int",
  Rat: "Rat",
  "ℚ": "Rat",
  Fin: "Fin",
  Finset: "Finset",
  Multiset: "Multiset",
  List: "List",
  Set: "Set",
  Filter: "Filter",
  Matrix: "Matrix",
  Tensor: "Tensor",
  Vector: "Vector",
  // PiLp-based sequence spaces live with Matrix in this repository.
  l1Space: "Matrix",
  L1Space: "Matrix",
  l2Space: "Matrix",
  lpSpace: "Matrix",
  WithLp: "Matrix",
  PiLp: "Matrix",
  Bool: "Bool",
  Hyperreal: "Hyperreal",
  "ℝ*": "Hyperreal",
  ZMod: "ZMod",
  // Markov-chain / simplex vocabulary lives under Matrix in this repository.
  StochasticVec: "Matrix",
  RowStochastic: "Matrix",
  StochasticIrreducible: "Matrix",
  Stationary: "Matrix",
  Aperiodic: "Matrix",
  DoeblinMinorization: "Matrix",
  Simplex: "Matrix",
  broadcast: "Matrix",
};

/** Section-score weight of domain predicates (beats the scalar field token, e.g. ℝ → Real). */
const SECTION_WEIGHT = {
  StochasticVec: 2, RowStochastic: 2, StochasticIrreducible: 2, Stationary: 2,
  Aperiodic: 2, DoeblinMinorization: 2, Simplex: 2, broadcast: 2,
};

const DATA_TYPE_SECTIONS = new Set(Object.values(TYPE_TO_SECTION));

const CLASS_TOKEN = {
  Lean_exists: "Any",
  Lean_forall: "All",
  LeanEq: "Eq",
  Lean_ne: "Ne",
  LeanNe: "Ne",
  Lean_lt: "Lt",
  Lean_gt: "Gt",
  Lean_le: "Le",
  Lean_ge: "Ge",
  Lean_leftrightarrow: "Iff",
  Lean_land: "And",
  Lean_lor: "Or",
  Lean_lnot: "Not",
  LeanSub: "Sub",
  LeanAdd: "Add",
  LeanMul: "Mul",
  LeanDiv: "Div",
  LeanNeg: "Neg",
  LeanPow: "Pow",
  LeanDvd: "Dvd",
  Lean_in: "In",
  LeanIn: "In",
  LeanInf: "Inf",
  Lean_cdotp: "Dot", // x ⬝ᵥ y → Dot (FiniteMRP/DotVecMul_D)
  Lean_subseteq: "Subset", // A ⊆ B → A/sub/B, Subset_B (AbsorbingSet/Subset_PhaseSpace, Random/Quantile/sub/QuantileLower)
};

function cls(n) { return n?.constructor?.name || ""; }

/** Declarations of the repo's sympy/**.lean modules: structure fields and type abbreviations. */
let SYMPY_DECLS = null;
function sympyDecls() {
  if (SYMPY_DECLS) return SYMPY_DECLS;
  const structs = new Map(); // structure → Map(field → type head)
  const typeAbbrevs = new Set(); // `abbrev EuclideanVec (d : ℕ) := EuclideanSpace ℝ (Fin d)` (not set-builder / Prop)
  const scan = (text) => {
    const lines = text.replace(/\r\n/g, "\n").split("\n");
    for (let i = 0; i < lines.length; i++) {
      const ab = /^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?abbrev\s+([^\s({\[:]+)(.*)$/.exec(lines[i]);
      if (ab) {
        const k = ab[2].indexOf(":=");
        let rhs = k >= 0 ? ab[2].slice(k + 2).trim() : "";
        if (k >= 0 && !rhs) rhs = (lines[i + 1] || "").trim();
        const head = k >= 0 ? ab[2].slice(0, k) : ab[2];
        if (rhs && !/^[{]|^Set\b/.test(rhs) && !/:\s*Prop\s*$/.test(head.trim())) typeAbbrevs.add(ab[1]);
        continue;
      }
      const st = /^structure\s+([^\s({\[]+)/.exec(lines[i]);
      if (!st) continue;
      let j = i;
      while (j < lines.length && !/\bwhere\s*$/.test(lines[j])) j++;
      const fields = new Map();
      // structure parameters are projections too: `structure Anchors (α : ℕ → ℝ)` → `anc.α`
      const header = lines.slice(i, j + 1).join(" ").replace(/^structure\s+\S+/, "");
      for (const pm of header.matchAll(/[({]\s*([^:(){}\[\]]+?)\s*:\s*([^\s(){}]*)/g)) for (const nm of pm[1].split(/\s+/)) if (nm) fields.set(nm, pm[2]);
      for (j = j + 1; j < lines.length; j++) {
        const l = lines[j];
        if (!l.trim() || /^\s*--/.test(l)) continue;
        if (!/^\s/.test(l)) break;
        const f = /^\s{2}([^\s:()]+(?:\s+[^\s:()]+)*)\s*:\s*(\S*)/.exec(l);
        if (f) for (const nm of f[1].split(/\s+/)) fields.set(nm, f[2].replace(/[()]/g, ""));
      }
      structs.set(st[1], fields);
    }
  };
  const walk = (d) => {
    let es = [];
    try { es = fs.readdirSync(d, { withFileTypes: true }); } catch { return; }
    for (const e of es) {
      const q = path.join(d, e.name);
      if (e.isDirectory()) walk(q);
      else if (q.endsWith(".lean")) { try { scan(fs.readFileSync(q, "utf8")); } catch {} }
    }
  };
  walk(path.join(REPO, "sympy"));
  SYMPY_DECLS = { structs, typeAbbrevs };
  return SYMPY_DECLS;
}

/** `{sk : Skeleton S d}` → Map(sk → Skeleton) for binders typed by a repo structure. */
function bundleVars(indented, explicitOnly = false) {
  const { structs } = sympyDecls();
  const out = new Map();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    const c = cls(n);
    if (c === "LeanStatements") return;
    if ((c === "LeanBrace" || c === "LeanParenthesis") && cls(n.args?.[0]) === "LeanColon") {
      if (explicitOnly && c !== "LeanParenthesis") return;
      const [b, t] = n.args[0].args || [];
      let h = t;
      if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
      if (cls(h) === "LeanToken" && structs.has(h.text)) {
        for (const x of cls(b) === "LeanToken" ? [b] : b?.args || []) if (cls(x) === "LeanToken") out.set(x.text, h.text);
      }
      return;
    }
    for (const a of n.args || []) walk(a);
  })(indented);
  if (explicitOnly) out.__explicit = true;
  return out;
}

/** `a.b.c` → ["a", "b", "c"] when every part is a plain token. */
function propertyParts(n) {
  if (cls(n) === "LeanToken") return [n.text];
  if (cls(n) !== "LeanProperty") return null;
  const l = propertyParts(n.args?.[0]);
  const r = propertyParts(n.args?.[1]);
  return l && r ? [...l, ...r] : null;
}

/**
 * Parser workaround: Mathlib's `ᵥ*` / `*ᵥ` (73) bind tighter than `⬝ᵥ` (72), so `x ᵥ* D ⬝ᵥ x` is
 * `(x ᵥ* D) ⬝ᵥ x`; lean.js currently yields `x ᵥ* (D ⬝ᵥ x)`. Re-associate before naming.
 */
function reassociateDotProduct(root) {
  (function walk(n, parent, idx) {
    if (!n || typeof n !== "object") return;
    const args = n.args || [];
    if (cls(n) === "LeanMul" && n.subscript === "ᵥ" && cls(args[1]) === "Lean_cdotp" && args[1].subscript === "ᵥ" && parent) {
      const dot = args[1];
      const [b, c] = dot.args || [];
      n.args = [args[0], b];
      if (b) b.parent = n;
      dot.args = [n, c];
      n.parent = dot;
      dot.parent = parent;
      parent.args[idx] = dot;
      walk(dot, parent, idx);
      return;
    }
    for (let i = 0; i < args.length; i++) walk(args[i], n, i);
  })(root, null, -1);
}

/**
 * Projections of a structure-typed binder that play the role of variables (`sk.x`, `sk.anc.t`, `sk.f`,
 * `sk.e₁` passed unapplied) become binder holes, like the plain variables of the generic lemma
 * (Skeleton/Iterates, not Iterates_X_TAncXFEEAnc). Uppercase or multi-letter parts (`MRP.D`, `MDP.pi`)
 * and applied definitions (`sk.g w`, `sk.G w p`) keep their names.
 */
function holeBundleProjections(root, bundles, leaves) {
  if (!bundles.size) return;
  const { structs } = sympyDecls();
  const varLike = (s) => (KEEP_GREEK ? /^[a-z][₀-₉ᵢⱼₖₙ'′]*$/u : /^[a-zα-ωϑϕ][₀-₉ᵢⱼₖₙ'′]*$/u).test(s || "");
  let k = 0;
  (function walk(n, parent, idx) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty" && parent) {
      const parts = propertyParts(n);
      if (parts && parts.length >= 2 && bundles.has(parts[0])) {
        let type = bundles.get(parts[0]);
        let ok = true;
        for (const p of parts.slice(1, -1)) {
          const t = structs.get(type)?.get(p);
          if (!t || !structs.has(t)) { ok = false; break; }
          type = t;
        }
        const last = parts[parts.length - 1];
        const applied = cls(parent) === "LeanArgsSpaceSeparated" && idx === 0 && (parent.args || []).length > 1;
        // a coercion of a variable-like projection is that variable: `spec.γ.toNNReal` → hole
        if (parts.length === 3 && /^(toNNReal|toReal|toENNReal|val|toLp|ofLp)$/.test(last) && varLike(parts[1]) && !applied) {
          let tok = n;
          while (cls(tok) === "LeanProperty") tok = tok.args?.[0];
          const hole = Object.assign(Object.create(Object.getPrototypeOf(tok)), tok, { text: "\u00b7bundle" + k++, parent });
          parent.args[idx] = hole;
          leaves.add(hole.text);
          return;
        }
        if (ok && varLike(last) && (structs.get(type)?.has(last) || !applied)) {
          let tok = n;
          while (cls(tok) === "LeanProperty") tok = tok.args?.[0];
          const hole = Object.assign(Object.create(Object.getPrototypeOf(tok)), tok, { text: "\u00b7bundle" + k++, parent });
          parent.args[idx] = hole;
          leaves.add(hole.text);
          return;
        }
        if (ok && parts.length >= 3 && !KEEP_GREEK) {
          // intermediate structure fields carry no meaning: `sk.anc.β n` → β, `sk.mrp.P` → P
          let tok = n;
          while (cls(tok) === "LeanProperty") tok = tok.args?.[0];
          parent.args[idx] = Object.assign(Object.create(Object.getPrototypeOf(tok)), tok, { text: last, parent });
          return;
        }
      }
    }
    const args = n.args || [];
    for (let i = 0; i < args.length; i++) walk(args[i], n, i);
  })(root, null, -1);
}

function uniq(xs) {
  return [...new Set((xs || []).filter(Boolean))];
}

function sameChildS(name) {
  if (!name) return "";
  return name + "S";
}

function pluralMidS(name) {
  if (!name) return "";
  const m = /^([A-Z][a-z0-9]*)([\s\S]*)$/.exec(name);
  if (!m) return name + "S";
  return m[1] + "S" + m[2];
}

/** Plural S after the leading word even before digits: Mul2Square → MulS2Square. */
function pluralLetterS(name) {
  const m = /^([A-Z][a-z]*)([^a-z][\s\S]*)$/.exec(name || "");
  return m ? m[1] + "S" + m[2] : "";
}

function pluralSnakeS(name) {
  if (!name) return "";
  const i = name.indexOf("_");
  if (i <= 0) return "";
  return name.slice(0, i) + "S" + name.slice(i);
}

function subscriptedMulAtom(node) {
  if (cls(node) !== "LeanMul" || node.subscript !== "ᵥ") return null;
  return node.isLeftSubscript ? "VecMul" : "MulVec";
}

function cartJoin(leftAlts, rightAlts, joiner) {
  const L = leftAlts?.length ? leftAlts : [""];
  const R = rightAlts?.length ? rightAlts : [""];
  const out = [];
  for (const l of L) {
    for (const r of R) {
      if (l && r) out.push(joiner(l, r));
      else out.push(l || r);
    }
  }
  return uniq(out);
}

function existingSections() {
  if (!fs.existsSync(LEMMA_ROOT)) return [];
  return fs.readdirSync(LEMMA_ROOT, { withFileTypes: true })
    .filter((d) => d.isDirectory()).map((d) => d.name).sort();
}

function collectTokens(node, out = new Set()) {
  if (!node || typeof node !== "object") return out;
  if (cls(node) === "LeanToken" && typeof node.text === "string") {
    const t = node.text;
    if (/^[A-Z]/.test(t) || TYPE_TO_SECTION[t]) out.add(t);
  }
  if (Array.isArray(node.args)) for (const c of node.args) collectTokens(c, out);
  return out;
}

function sectionDepths(node, depth = 0, out = new Map()) {
  if (!node || typeof node !== "object") return out;
  if (cls(node) === "LeanToken" && typeof node.text === "string") {
    const sec = TYPE_TO_SECTION[node.text];
    if (sec) out.set(sec, Math.max(out.get(sec) ?? -1, depth));
  }
  if (Array.isArray(node.args)) for (const c of node.args) sectionDepths(c, depth + 1, out);
  return out;
}

/** True when signature has RV/PSpace probability structure (not bare Measure). */
function hasRandomAstCues(node) {
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "Lean_rightarrow") {
      const left = n.args?.[0];
      // Convention: sample-space RVs are binders {x : Ω → α}.
      if (cls(left) === "LeanToken" && (left.text === "Ω" || left.text === "Omega")) {
        found = true;
        return;
      }
    }
    if (cls(n) === "LeanToken") {
      const t = n.text;
      if (
        t === "PSpace" ||
        t === "ProbabilityMeasure" ||
        t === "IsProbabilityMeasure"
      ) {
        found = true;
        return;
      }
    }
    if (Array.isArray(n.args)) for (const c of n.args) walk(c);
  };
  walk(node);
  return found;
}

function conclusionLhsHeadToken(colonNode) {
  let type = colonNode?.args?.[colonNode.args.length - 1];
  while (type && (cls(type) === "LeanStatements" || cls(type) === "LeanArgsNewLineSeparated")) {
    type = (type.args || []).find((a) => cls(a) !== "LeanLineComment");
  }
  if (!type) return "";
  const REL = new Set(["LeanEq", "Lean_le", "Lean_lt", "Lean_ge", "Lean_gt", "LeanNe", "Lean_ne", "Lean_leftrightarrow"]);
  let lhs = REL.has(cls(type)) ? type.args?.[0] : type;
  while (cls(lhs) === "LeanParenthesis") lhs = lhs.args?.[0];
  if (cls(lhs) === "LeanArgsSpaceSeparated") lhs = lhs.args?.[0];
  while (cls(lhs) === "LeanParenthesis") lhs = lhs.args?.[0];
  if (cls(lhs) === "LeanToken") return lhs.text || "";
  if (cls(lhs) === "LeanProperty") {
    const prop = lhs.args?.[1];
    return cls(prop) === "LeanToken" ? prop.text || "" : "";
  }
  return "";
}

/**
 * Section tokens with a position weight: 0 in a function domain (`ℕ → ℝ` indices),
 * 2 in a codomain (value type), 1 elsewhere. Property names naming a section count
 * as `.Section` (`M.kernel` → Kernel); namespaced constants as `ns:Section`.
 */
function collectTokenWeights(node, w = 1, out = new Map()) {
  if (!node || typeof node !== "object") return out;
  const c = cls(node);
  const put = (t, x) => out.set(t, Math.max(out.get(t) ?? -1, x));
  if (c === "LeanToken" && typeof node.text === "string") {
    const t = node.text;
    if (/^[A-Z]/.test(t) || TYPE_TO_SECTION[t]) put(t, w);
    if (t.includes(".")) {
      const ns = t.slice(0, t.indexOf("."));
      if (TYPE_TO_SECTION[ns] === ns) put("ns:" + ns, w);
    }
  }
  if (c === "LeanProperty" && cls(node.args?.[1]) === "LeanToken") {
    const p = nameToken(node.args[1].text || "");
    if (TYPE_TO_SECTION[p] === p) put("." + p, w);
  }
  if (c === "Lean_rightarrow" && node.args?.length === 2) {
    const dom = node.args[0];
    const isType = cls(dom) === "LeanToken" || (cls(dom) === "LeanArgsSpaceSeparated" && cls(dom.args?.[0]) === "LeanToken" && /^[A-Z]/.test(dom.args[0].text || ""));
    if (isType) {
      collectTokenWeights(dom, 0, out);
      collectTokenWeights(node.args[1], w === 0 ? 0 : 2, out);
      return out;
    }
  }
  for (const a of node.args || []) collectTokenWeights(a, w, out);
  return out;
}

/**
 * Custom namespace sections (Lemma/<Section> folders that are not data types, e.g. Iterates,
 * LyapunovCandidate): a conclusion token or given head naming the folder (`Iterates …`,
 * `IteratesOfResidual …`) decides the section; conclusion first, then givens in Lean order.
 */
function customSection(sections, conclNode, givenTypes, importDecls = new Map(), binders = null) {
  const custom = sections.filter((s) => !DATA_TYPE_SECTIONS.has(s) && !TYPE_TO_SECTION[s]);
  // a normalized weight function among the hypotheses (`∀ θ, ∑ a, p θ a = 1`) makes it a probability lemma
  if (sections.includes("Random") && givenTypes.some((g) => {
    let h = unwrapParen(g);
    while (cls(h) === "Lean_forall") h = unwrapParen(h.args?.[h.args.length - 1]);
    return cls(h) === "LeanEq" && cls(unwrapParen(h.args?.[0])) === "Lean_sum" && cls(h.args?.[1]) === "LeanToken" && h.args[1].text === "1";
  })) return "Random";
  if (!custom.length) return null;
  // a statement about a structure value `sk : Skeleton S d` (conclusion uses `sk.…`) lives in Skeleton/
  // the conclusion's head predicate names a folder: IsGlobalAttractor Φ … → IsGlobalAttractor
  {
    let h = conclNode;
    while (h && (cls(h) === "LeanStatements" || cls(h) === "LeanParenthesis" || cls(h) === "Lean_land")) h = cls(h) === "LeanStatements" ? (h.args || []).find((a) => cls(a) !== "LeanLineComment") : h.args?.[0];
    // …unless its arguments are projections of a structure value (Iterates sk.x sk.T … stays in Skeleton/)
    const bundled = binders ? bundleVars(binders) : new Map();
    const projArg = (a) => { const p = propertyParts(unwrapParen(a)); return !!p && p.length >= 2 && bundled.has(p[0]); };
    if (cls(h) === "LeanArgsSpaceSeparated" && cls(h.args?.[0]) === "LeanToken" && custom.includes(h.args[0].text) && !h.args.slice(1).some(projArg)) return h.args[0].text;
  }
  // a structure type names its folder exactly, or extends it (FrozenInvariantLawWitness → FrozenInvariantLaw)
  const folderOf = (ty) => custom.includes(ty) ? ty : custom.filter((s) => ty.startsWith(s) && /[A-Z]/.test(ty.charAt(s.length))).sort((a, b) => b.length - a.length)[0] || null;
  if (binders) {
    // explicit structure arguments (`(w : FrozenInvariantLawWitness …)`) before implicit context bundles
    for (const bundles of [bundleVars(binders, true), bundleVars(binders)]) {
      let hit = null;
      (function walk(n) {
        if (hit || !n || typeof n !== "object") return;
        if (cls(n) === "LeanProperty") {
          const parts = propertyParts(n);
          if (parts && bundles.has(parts[0])) {
            const ty = bundles.get(parts[0]);
            const f = bundles.size && custom.includes(ty) ? ty : (explicitPass(bundles) ? folderOf(ty) : null);
            if (f) { hit = f; return; }
          }
        }
        // quantifier heads (`∀ᵐ ω ∂M.markov_samples`) only give context
        const q = cls(n) === "Lean_exists" || cls(n) === "Lean_forall";
        for (const a of q ? (n.args || []).slice(-1) : n.args || []) walk(a);
      })(conclNode);
      if (hit) return hit;
    }
  }
  function explicitPass(b) { return b.__explicit === true; }
  const match = (t) => {
    if (!t) return null;
    const parts = [t, t.split(".")[0]];
    for (const p of parts) for (const s of custom) if (p === s) return s;
    for (const p of parts) for (const s of custom) if (p.startsWith(s) && /[A-Z]/.test(p.charAt(s.length))) return s;
    return null;
  };
  const tokensOf = (n, out = []) => {
    if (!n || typeof n !== "object") return out;
    if (cls(n) === "LeanToken" && typeof n.text === "string") out.push(n.text);
    for (const a of n.args || []) tokensOf(a, out);
    return out;
  };
  // conclusion: exact folder names only, outside quantifier binder types (`∃ anc : Anchors …, P anc` stays in its section)
  const conclTokens = (n, out = []) => {
    if (!n || typeof n !== "object") return out;
    if (cls(n) === "LeanToken" && typeof n.text === "string") out.push(n.text);
    const kids = n.args || [];
    const q = cls(n) === "Lean_exists" || cls(n) === "Lean_forall";
    for (const a of q ? kids.slice(-1) : kids) conclTokens(a, out);
    return out;
  };
  for (const t of conclTokens(conclNode)) { if (custom.includes(t) || custom.includes(t.split(".")[0])) return custom.includes(t) ? t : t.split(".")[0]; }
  // a repo structure named in the conclusion extends a folder name: Nonempty (FrozenInvariantLawWitness …)
  for (const t of conclTokens(conclNode)) if (/^[A-Z]/.test(t) && sympyDecls().structs.has(t)) { const f = folderOf(t); if (f) return f; }
  for (const g of givenTypes) {
    let h = unwrapParen(g);
    if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
    if (cls(h) === "LeanGetElem") h = h.args?.[0];
    const s = cls(h) === "LeanToken" ? match(h.text) : null;
    if (s) return s;
    // a hypothesis about a notion declared in `sympy.….<folder>` (AdaptedOnSamplePath x → Iterates)
    if (cls(h) === "LeanToken") for (const [sec, names] of importDecls) if (custom.includes(sec) && names.has(h.text)) return sec;
  }
  // snake_case / lowerCamel definitions named like a folder: absorbing_set → AbsorbingSet, omegaLimit → OmegaLimit,
  // actor_box_projection → ActorBox
  for (const t of conclTokens(conclNode)) {
    const last = t.includes(".") ? t.slice(t.lastIndexOf(".") + 1) : t;
    if (!/^[a-z]/.test(last) || !(last.includes("_") || /[A-Z]/.test(last))) continue;
    const camel = nameTokenRaw(last);
    if (custom.includes(camel)) return camel;
    // a longer name (actor_box_projection → ActorBox) only when the folder's own notion also occurs in a hypothesis
    // (`θ ∈ actor_box d r`); iterates_update alone stays with its data section
    const f = folderOf(camel);
    if (f && givenTypes.some((g) => tokensOf(g).some((x) => /^[a-z]/.test(x) && nameTokenRaw(x) === f))) return f;
  }
  // the set of all X: `IsClosed {μ | StochasticVec μ}` → StochasticVec (also data-type-mapped folders)
  {
    let hit = null;
    (function walk(n) {
      if (hit || !n || typeof n !== "object") return;
      if (setBuilderCond(n)) {
        let b = unwrapParen(setBuilderCond(n));
        if (cls(b) === "LeanArgsSpaceSeparated") b = b.args?.[0];
        if (cls(b) === "LeanToken" && sections.includes(b.text) && b.text !== TYPE_TO_SECTION[b.text] && !["Set", "Finset", "List"].includes(b.text)) { hit = b.text; return; }
      }
      for (const a of n.args || []) walk(a);
    })(conclNode);
    if (hit) return hit;
  }
  // a variable typed by a custom notion: {x : LpSpace p d} → LpSpace
  for (const t of conclTokens(binders)) if (custom.includes(t)) return t;
  return null;
}

/** `import sympy.stats.iterates` → Iterates, when such a Lemma folder exists. */
function importSections(source, sections) {
  // folder → names declared (class/structure/def/…) in the imported sympy module of the same name
  const out = new Map();
  for (const m of String(source || "").matchAll(/^import\s+(sympy\.[\w.]*?(\w+))\s*$/gm)) {
    const camel = m[2].split("_").map((p) => p.charAt(0).toUpperCase() + p.slice(1)).join("");
    if (!sections.includes(camel)) continue;
    let text = "";
    try { text = fs.readFileSync(path.join(REPO, ...m[1].split(".")) + ".lean", "utf8"); } catch {}
    const names = new Set([...text.matchAll(/^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(?:class|structure|def|abbrev|inductive)\s+([^\s({\[:]+)/gm)].map((d) => d[1]));
    out.set(camel, names);
  }
  return out;
}

/**
 * Section for a generic typeclass lemma (no data-type token). Repo majorities for such files:
 * intervals → Set (93), |x| or additive groups/rings → Int (AddGroup 57, AddCommGroup 46, Ring 56, abs 38),
 * fields → Rat (Field 64, GroupWithZero 24, IsStrictOrderedRing 63), otherwise Nat.
 * Any data-type section stays accepted for consistency.
 */
function genericSection(sigNode, tokens, existing) {
  const pick = (s) => (existing.has(s) ? s : "Nat");
  if (hasNode(sigNode, (n) => cls(n) === "LeanToken" && /^(Set\.)?I(cc|co|oc|oo)$/.test(n.text || ""))) return pick("Set");
  if (["Field", "GroupWithZero", "DivisionRing", "IsStrictOrderedRing", "LinearOrderedField"].some((t) => tokens.has(t)) && !hasNode(sigNode, (n) => cls(n) === "LeanAbs")) return pick("Rat");
  if (hasNode(sigNode, (n) => cls(n) === "LeanAbs") || ["AddGroup", "AddCommGroup", "Ring", "CommRing", "LinearOrderedAddCommGroup"].some((t) => tokens.has(t))) return pick("Int");
  return "Nat";
}

function pickSection(sigNode, sections, extra = {}) {
  if (extra.custom) return { section: extra.custom, score: "custom", tokens: [...collectTokens(sigNode)].sort() };
  const tokens = collectTokens(sigNode);
  const weights = collectTokenWeights(sigNode);
  const depths = sectionDepths(sigNode);
  const candidates = [...new Set([...sections, ...DATA_TYPE_SECTIONS])];
  const scores = new Map(candidates.map((s) => [s, 0]));
  const add = (sec, x) => { if (sec && scores.has(sec)) scores.set(sec, scores.get(sec) + x); };
  for (const [t, w] of weights) {
    let sec;
    let raw;
    if (t.startsWith(".")) { sec = TYPE_TO_SECTION[t.slice(1)]; raw = 2; }
    else if (t.startsWith("ns:")) { sec = TYPE_TO_SECTION[t.slice(3)]; raw = 1; }
    else { sec = TYPE_TO_SECTION[t]; raw = t === sec ? 3 : SECTION_WEIGHT[t] ?? 1; }
    if (!sec) continue;
    const index = sec === "Nat" || sec === "Int";
    // ℕ/ℤ often only index or count; prefer the value type (Real sequences)
    if (index && tokens.size > 0) raw = Math.min(raw, 1) * 0.5;
    const x = w === 0 ? raw * 0.5 : w === 2 && !index ? raw + 0.5 : raw;
    add(sec, x);
  }
  if (hasNode(sigNode, (n) => cls(n) === "LeanNorm" || cls(n) === "Lean_sqrt" || (cls(n) === "LeanToken" && n.text === "π"))) add("Real", 1);
  for (const s of extra.imports || []) { if (!scores.has(s)) scores.set(s, 0); add(s, 1.5); }
  const concl = conclusionNode(sigNode);
  if (concl && (cls(concl) === "LeanEq" || cls(concl) === "Lean_le") && concl.superscript === "ᶠ") add("Filter", 3);
  if (concl && CLASS_TOKEN[cls(concl)] && (concl.args || []).length === 2 &&
      concl.args.every((a) => { const u = unwrapParen(a); return (cls(u) === "Lean_sum" || cls(u) === "Lean_prod") && (u.args || []).some((b) => cls(b) === "Lean_in"); })) {
    add("Finset", 2);
  }
  // `v ᵥ* M` / `M *ᵥ v` are Matrix operations.
  const hasVecMul = (n) => !!n && typeof n === "object" && (subscriptedMulAtom(n) !== null || (n.args || []).some(hasVecMul));
  if (hasVecMul(sigNode) && scores.has("Matrix")) scores.set("Matrix", scores.get("Matrix") + 2);
  const LP_EMBED = new Set(["ofL1", "ofLp", "toL1", "toLp"]);
  if (LP_EMBED.has(conclusionLhsHeadToken(sigNode)) && scores.has("Matrix"))
    scores.set("Matrix", scores.get("Matrix") + 2);
  if (tokens.has("AbsoluteValue") && scores.has("AbsoluteValue"))
    scores.set("AbsoluteValue", scores.get("AbsoluteValue") + 5);
  if (tokens.has("List") && scores.has("List")) scores.set("List", scores.get("List") + 2);
  // RV binders (Ω → _) / PSpace overweight Measure from {π : Measure Ω}.
  if (hasRandomAstCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 5);
  // pure set identities / inclusions between set constructions ({ω | …} ∪ {ω | …} = {ω | …}) are Set lemmas
  {
    const INTERVAL = /^(Set\.)?I(cc|co|oc|oo|ci|ic|oi|io)$/;
    const isSetCons = (n) => {
      const u = unwrapParen(n);
      const k = cls(u);
      return isSetBuilder(u) || k === "Lean_cup" || k === "Lean_cap" ||
        (k === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken" && INTERVAL.test(u.args[0].text || ""));
    };
    if (concl && (cls(concl) === "LeanEq" || cls(concl) === "Lean_subseteq") && (concl.args || []).length === 2 && concl.args.every(isSetCons)) add("Set", 8);
    // `x ∈ Ico a b` with no data type in sight → Set rather than the Nat fallback
    if (concl && (cls(concl) === "Lean_in" || cls(concl) === "LeanIn") && isSetCons(concl.args?.[1])) add("Set", 1);
  }
  // matrix exponential (`exp (t • Q)` with Q : Matrix …) lives in NormedSpace/
  if (scores.has("NormedSpace") && hasNode(sigNode, (n) => cls(n) === "LeanToken" && (n.text === "exp" || n.text === "NormedSpace.exp")) &&
      hasNode(sigNode, (n) => cls(n) === "LeanToken" && n.text === "Matrix")) add("NormedSpace", 8);
  // limits of real sequences/functions (`lim [n → ∞] γ ^ n * x n = 0` next to `Set.range`) are Real lemmas
  if (concl && tokens.has("ℝ") && hasNode(concl, (n) => cls(n) === "Lean_lim")) add("Real", 3);
  // sSup / sInf of an image of a real-valued function (`sSup (f '' S)`, S : Set α) are Real lemmas
  if (concl && tokens.has("ℝ") && hasNode(concl, (n) => cls(n) === "LeanArgsSpaceSeparated" && cls(n.args?.[0]) === "LeanToken" && /^(sSup|sInf)$/.test(n.args[0].text || "") &&
      hasNode(n.args[1], (m) => cls(m) === "LeanToken" && m.text === "''"))) add("Real", 3);
  const existing = new Set(sections);
  const rank = (s) => [scores.get(s) ?? 0, depths.get(s) ?? -1];
  const better = (a, b) => {
    const [as, ad] = rank(a);
    const [bs, bd] = rank(b);
    if (as !== bs) return as > bs;
    if (ad !== bd) return ad > bd; // innermost data type wins ties
    if (existing.has(a) !== existing.has(b)) return existing.has(a);
    return a < b;
  };
  let best = sections[0] || "Nat";
  for (const s of candidates) if (better(s, best)) best = s;
  // No section evidence (generic algebra over α): the repository keeps these under Nat.
  if (!(scores.get(best) > 0) && existing.has("Nat")) best = genericSection(sigNode, tokens, existing);
  return { section: best, score: scores.get(best) ?? 0, tokens: [...tokens].sort() };
}

function hasNode(node, pred) {
  if (!node || typeof node !== "object") return false;
  if (pred(node)) return true;
  return (node.args || []).some((a) => hasNode(a, pred));
}

function conclusionNode(colonNode) {
  let type = colonNode?.args?.[colonNode.args.length - 1];
  while (type && (cls(type) === "LeanStatements" || cls(type) === "LeanArgsNewLineSeparated")) type = firstConclusion(type);
  return unwrapParen(type);
}

function isPropHyp(typeNode) {
  if (!typeNode) return false;
  const name = cls(typeNode);
  if (["Lean_forall","Lean_exists","Lean_lt","Lean_gt","Lean_le","Lean_ge","LeanEq","Lean_ne","LeanNe","Lean_leftrightarrow","Lean_land","Lean_lor","Lean_lnot","Lean_in","LeanIn","Lean_subseteq"].includes(name)) return true;
  if (name === "LeanArgsSpaceSeparated") {
    let head = typeNode.args?.[0];
    // `Φ.Attracts K B`, `Φ.Invariant K`: a capitalized method predicate applied to arguments
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^[A-Z][A-Za-z0-9]+$/.test(head.args[1].text || "") && !TYPE_TO_SECTION[head.args[1].text]) return true;
    if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken") head = head.args[0]; // StronglyMeasurable[m] g
    if (cls(head) === "LeanToken") {
      const t = head.text;
      if (t === "Pairwise" || t === "And" || t === "Or" || t === "Not" || /^Is[A-Z]/.test(t) || /^Has[A-Z]/.test(t)) return true;
      // Explicit typeclass hyps: (h : DoeblinMinorization P), FiniteGCDOne A, …
      const dataHeads = new Set([
        "Matrix", "Set", "Finset", "List", "Array", "Vector", "Tensor", "Option", "Subtype",
        "Type", "Sort", "Nat", "Int", "Rat", "Real", "Complex", "Fin", "Bool", "String", "Unit",
      ]);
      if (t && /^[A-Z][A-Za-z0-9]+$/.test(t) && t.length >= 3 && !dataHeads.has(t)) return true;
    }
  }
  if (name === "LeanProperty") return true;
  if (name === "LeanParenthesis") return isPropHyp(typeNode.args?.[0]);
  if (name === "LeanStatements") {
    const expr = (typeNode.args || []).find((a) => cls(a) !== "LeanLineComment");
    return isPropHyp(expr);
  }
  return false;
}

const TOKEN_ALIAS = {
  "ℙ": "Prob",
  GetElem: "Get",
  StdPart: "St",
  stdPart: "St",
  val: "Val",
  Val: "Val",
  coe: "Val",
  HMul: "Mul",
  HAdd: "Add",
  HSub: "Sub",
  HDiv: "Div",
  HPow: "Pow",
  HMod: "Mod",
  mk: "", // prefer receiver type via LeanConstruct elsewhere
};

/** Non-ASCII notation → ASCII atom ("" drops it); path atoms are ASCII only. */
const SYMBOL_NAME = { "𝔼": "Expect", "∅": "Empty", "⊤": "Top", "⊥": "Bot", "π": "Pi", "√": "Sqrt", "𝓝": "", atTop: "", atBot: "" };

/** Second naming pass: Greek / subscript letters are kept (`spec.η`, `maxₐ`, `μmin`), as the repo does. */
let KEEP_GREEK = false;
const GREEK_KEEP_RE = /[\u0370-\u03FF\u1F00-\u1FFF\u2090-\u209C\u1D62-\u1D6A\u2080-\u2089]/u;
function nameToken(text) {
  if (!text) return "";
  const t = String(text);
  const last = t.includes(".") ? t.slice(t.lastIndexOf(".") + 1) : t;
  if (SYMBOL_NAME[last] !== undefined) return SYMBOL_NAME[last];
  if (KEEP_GREEK && GREEK_KEEP_RE.test(last)) {
    let s = nameTokenRaw(t);
    // no case change for a non-ASCII initial (μmin, not Μmin)
    if (/^[^\x00-\x7F]/.test(last) && !last.includes("_")) s = last;
    return [...s].filter((ch) => /[\x00-\x7F]/.test(ch) || GREEK_KEEP_RE.test(ch)).join("").replace(/\*+$/, "");
  }
  return nameTokenRaw(t).replace(/[^\x00-\x7F]/g, "").replace(/\*+$/, "");
}

function nameTokenRaw(text) {
  if (!text) return "";
  let s = String(text);
  if (s.includes(".")) s = s.slice(s.lastIndexOf(".") + 1);
  if (!s || s === "[anonymous]" || s === "anonymous" || s === "_") return "";
  if (TOKEN_ALIAS[s] !== undefined) return TOKEN_ALIAS[s];
  if (s.includes("_")) {
    s = s.split("_").map((p) => (p ? p.charAt(0).toUpperCase() + p.slice(1) : "")).join("");
  } else {
    s = s.charAt(0).toUpperCase() + s.slice(1);
  }
  return TOKEN_ALIAS[s] !== undefined ? TOKEN_ALIAS[s] : s;
}



function collectLeafBinders(node, out = new Set(), noBinders = false) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  if (!noBinders && (name === "LeanBrace" || name === "LeanParenthesis")) {
    const colon = node.args?.[0];
    if (cls(colon) === "LeanColon") {
      const binders = colon.args?.[0];
      if (cls(binders) === "LeanToken") {
        if (binders.text) out.add(binders.text);
      } else if (cls(binders) === "LeanArgsSpaceSeparated") {
        const bs = binders.args || [];
        if (bs.every((x) => cls(x) === "LeanToken")) {
          for (const a of bs) if (a.text) out.add(a.text);
        }
      }
    }
  }
  // ∀ a ∈ A, ... / ∃ a ∈ A, ...
  if (name === "Lean_forall" || name === "Lean_exists") {
    const head = node.args?.[0];
    if ((cls(head) === "Lean_in" || cls(head) === "LeanIn") && cls(head.args?.[0]) === "LeanToken") {
      const t = head.args[0].text;
      if (t) out.add(t);
    }
    // bare ∀ j, ... / ∃ j, ... (binder token then body); also `∀ i j`, `∃ C ≥ 0`, `∀ᵐ ω ∂μ`
    if (cls(head) === "LeanToken" && head.text) out.add(head.text);
    quantBinderNames(head, out);
    if (cls(head) === "LeanColon" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text) {
      out.add(head.args[0].text);
    }
  }
  if (name === "Lean_int") for (const b of (node.args || []).slice(0, -1)) quantBinderNames(b, out);
  // `{ω | P ω}` / `{μ : S → ℝ | P μ}`: the set-builder binder
  if (name === "LeanBrace" && cls(node.args?.[0]) === "LeanBitOr") quantBinderNames(node.args[0].args?.[0], out);
  if (name === "Lean_fun" && cls(node.args?.[0]) === "Lean_mapsto") quantBinderNames(node.args[0].args?.[0], out);
  if (name === "Lean_fun" && cls(node.args?.[0]) === "LeanRightarrow" && cls(node.args[0].args?.[0]) === "LeanArgsSpaceSeparated") {
    quantBinderNames(node.args[0].args[0], out);
  }
  if (name === "Lean_fun") {
    const arrow = node.args?.[0];
    let b = cls(arrow) === "LeanRightarrow" ? arrow.args?.[0] : null;
    if (cls(b) === "LeanColon") b = b.args?.[0];
    for (const t of cls(b) === "LeanToken" ? [b] : cls(b) === "LeanArgsSpaceSeparated" ? b.args || [] : []) {
      if (cls(t) === "LeanToken" && t.text && t.text !== "_") out.add(t.text);
    }
  }
  if (name === "Lean_sum" || name === "Lean_prod") {
    for (const b of (node.args || []).slice(0, -1)) {
      if (cls(b) === "LeanToken" && b.text && b.text !== "_") out.add(b.text);
      if ((cls(b) === "Lean_in" || cls(b) === "LeanIn") && cls(b.args?.[0]) === "LeanToken" && b.args[0].text) {
        out.add(b.args[0].text);
      }
      if (cls(b) === "LeanColon" && cls(b.args?.[0]) === "LeanToken" && b.args[0].text && b.args[0].text !== "_") {
        out.add(b.args[0].text);
      }
    }
  }
  for (const a of node.args || []) collectLeafBinders(a, out, noBinders);
  return out;
}

/**
 * README Snake_Case: F_Y means F _ Y.
 * Intermediate `One` (from literal 1) becomes digit `1` after the underscore → Eq_1.
 */
function snakeFocus(tag, focus) {
  const f = focus === "One" ? "1" : focus;
  return tag + "_" + f;
}

/**
 * Bare path segment `1` → `One` (Windows `lake` rejects `/1/` folders).
 * Keep `0` and compound atoms like `Eq_1` / `Ge_1` unchanged.
 * Nat literal 1 is spelled One in path segments (Windows-safe).
 */
const NUM_WORD = ["Zero", "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine", "Ten"];
function numberWord(d) {
  const n = Number(d);
  if (String(n) === d && n <= 10) return NUM_WORD[n];
  return [...d].map((c) => NUM_WORD[+c]).join("");
}
function sanitizePathSeg(seg) {
  // a module component may not start with a digit (lake): `eq/0` → `eq/Zero`, `0OrP` → `ZeroOrP`, `-1` → `NegOne`;
  // digits after the first letter stay (`Gt_0`, `Div1'2`)
  const m = /^(-?)(\d+)(.*)$/s.exec(seg);
  if (!m) return seg;
  return (m[1] ? "Neg" : "") + numberWord(m[2]) + m[3];
}

/** Valid Lean module-name component (identifier, no leading digit; Greek/subscript letters allowed). */
function validModuleComponent(c) {
  return /^[\p{L}_][\p{L}\p{N}_'!?\u2080-\u209C\u1D62-\u1D6A\u2070-\u207F]*$/u.test(c || "");
}
function validModulePath(p) {
  return String(p).replace(/\.lean$/, "").split("/").every(validModuleComponent);
}

function sanitizeRelPath(rel) {
  return String(rel)
    .split("/")
    .map((part) => {
      // preserve ".lean" on the last segment
      if (part.endsWith(".lean")) {
        const stem = part.slice(0, -5);
        return sanitizePathSeg(stem) + ".lean";
      }
      return sanitizePathSeg(part);
    })
    .join("/");
}


/** Digit-digit joins keep an apostrophe (README Apostrophe): Div1'2, DivSqrt3'2. */
function joinDigits(a, b) {
  return /\d$/.test(a) && /^\d/.test(b) ? a + "'" + b : a + b;
}

/** Numeric literal or arithmetic of literals (`0`, `1 / 2`, `√3 / 2`). */
function isConstNode(node) {
  const n = unwrapParen(node);
  const c = cls(n);
  if (c === "LeanToken") return /^-?\d+(\.\d+)?$/.test(n.text || "") || n.text === "π";
  if (c === "LeanAdd" || c === "LeanSub" || c === "LeanMul" || c === "LeanDiv" || c === "LeanPow" || c === "LeanNeg" || c === "Lean_sqrt") {
    return (n.args || []).length > 0 && n.args.every(isConstNode);
  }
  return false;
}

function isTypeSortNode(t) {
  const c = cls(t);
  if (c === "LeanToken") return /^(Type|Sort)/.test(t.text || "");
  if (c === "LeanArgsSpaceSeparated") return isTypeSortNode(t.args?.[0]);
  if (c === "Lean_rightarrow") return isTypeSortNode(t.args?.[t.args.length - 1]);
  return false;
}

/** Binders declared as types, e.g. `{S : Type*}`. */
function collectTypeBinders(indented, out = new Set()) {
  const walk = (n) => {
    if (!n || typeof n !== "object") return;
    const c = cls(n);
    if (c === "LeanStatements") return;
    if (c === "LeanBrace" || c === "LeanParenthesis") {
      const colon = n.args?.[0];
      if (cls(colon) === "LeanColon" && isTypeSortNode(colon.args?.[1])) {
        const b = colon.args?.[0];
        for (const t of cls(b) === "LeanToken" ? [b] : b?.args || []) if (cls(t) === "LeanToken") out.add(t.text);
      }
      return;
    }
    for (const a of n.args || []) walk(a);
  };
  walk(indented);
  return out;
}

/**
 * Camel-joinable argument: a token, or an application whose arguments are type binders
 * (`IsCompactSimplex`, `RowStochasticBroadcast`) or an ascribed binder application.
 * Term applications such as `uncurry f` stay Snake (`Measurable_Uncurry`).
 */
function isSimpleArg(node, opts) {
  let n = node;
  let ascribed = false;
  while (cls(n) === "LeanParenthesis" || cls(n) === "LeanColon") {
    if (cls(n) === "LeanColon") ascribed = true;
    n = n.args?.[0];
  }
  const c = cls(n);
  if (c === "LeanToken" || c === "LeanProperty") return true;
  if (c === "LeanArgsSpaceSeparated" && cls(n.args?.[0]) === "LeanToken") {
    // `Function.uncurry spec.update`: an application to named projections reads Camel (MeasurableUncurryUpdate)
    if (!ascribed && n.args.length === 2 && cls(n.args[1]) === "LeanProperty" && cls(n.args[1].args?.[0]) === "LeanToken" && cls(n.args[1].args?.[1]) === "LeanToken") return true;
    return n.args.slice(1).every((x) => cls(x) === "LeanToken" &&
      (ascribed ? opts.leaves?.has(x.text) : opts.typeLeaves ? opts.typeLeaves.has(x.text) : opts.leaves?.has(x.text)));
  }
  if (c === "LeanArgsSpaceSeparated" && qualHeadText(n.args?.[0]) && cls(n.args[0]) === "LeanProperty" && !ascribed && n.args.length === 2) {
    // `Function.uncurry spec.update` (namespaced head, one named argument)
    const x = n.args[1];
    if (cls(x) === "LeanProperty" && cls(x.args?.[0]) === "LeanToken" && cls(x.args?.[1]) === "LeanToken") return true;
  }
  return false;
}

/** `fun x => ∑ …` / `fun x => g x ^ 2` / `fun x => F …` read Camel after the head (TendstoSum). */
function funBodyUnary(funNode) {
  const f = unwrapParen(funNode);
  const arrow = f?.args?.[f.args.length - 1];
  const body = unwrapParen(arrow?.args?.[arrow.args.length - 1]);
  const c = cls(body);
  if (c === "Lean_sum" || c === "Lean_prod") return true;
  if (c === "LeanPow" && cls(body.args?.[1]) === "LeanToken" && body.args[1].text === "2") return true;
  return c === "LeanArgsSpaceSeparated" && cls(body.args?.[0]) === "LeanToken" && /^[A-Z]/.test(body.args[0].text || "");
}

/** `μ[X | m]` → X (also `μ[fun ω => X ω | m]`, where `fun` swallows `| m`); null otherwise. */
function condExpArg(node) {
  if (cls(node) !== "LeanGetElem") return null;
  const h = node.args?.[0];
  if (cls(h) === "LeanToken" && (h.text === "ℙ" || h.text === "𝔼")) return null;
  const idx = node.args?.[1];
  if (cls(idx) === "LeanBitOr") return idx.args?.[0];
  // `μ[f (n + 1) | ℱ n]` parses as f ((n + 1) | ℱ n): rebuild the application f (n + 1)
  if (cls(idx) === "LeanArgsSpaceSeparated" && cls(idx.args?.[idx.args.length - 1]) === "LeanBitOr") {
    const app = Object.create(Object.getPrototypeOf(idx));
    Object.assign(app, idx);
    app.args = [...idx.args.slice(0, -1), idx.args[idx.args.length - 1].args?.[0]];
    return app;
  }
  if (cls(idx) === "Lean_fun") {
    const arrow = idx.args?.[idx.args.length - 1];
    const body = arrow?.args?.[arrow.args.length - 1];
    if (cls(body) === "LeanBitOr") return body.args?.[0];
  }
  return null;
}

/** Applied heads named without `Get`: `(f ⁻¹' A)`, `μ[X | m] ω`. */
function fnLikeHead(head) {
  const h = unwrapParen(head);
  const c = cls(h);
  return c === "LeanPreimage" || !!condExpArg(h);
}

/** `AEStronglyMeasurable[m] f μ`: the bracket index is not a path atom. */
function normHead(head, opts) {
  const h = head;
  if (cls(h) === "LeanGetElem" && !condExpArg(h)) {
    const t = h.args?.[0];
    if (cls(t) === "LeanToken" && /^[A-Z]/.test(t.text || "") && !opts.leaves?.has(t.text)) return t;
  }
  return h;
}

/** Join one application argument onto head alternatives (Camel / Snake / optional). */
function argJoinAlts(acc, a, alts, opts) {
  const u = unwrapParen(a);
  const ac = cls(a);
  const compound = ac !== "LeanToken" && ac !== "LeanProperty" && !(ac === "LeanParenthesis" && cls(u) === "LeanToken");
  const fun = cls(u) === "Lean_fun";
  const simple = isSimpleArg(a, opts) || isConstNode(a);
  const snake = (h, c) => h + "_" + c;
  let next = compound && (simple || fun)
    ? uniq([...cartJoin(acc, alts, joinHeadChild), ...cartJoin(acc, alts, snake)])
    : cartJoin(acc, alts, compound ? snake : joinHeadChild);
  if (fun && alts.includes("Fun")) next = uniq([...cartJoin(acc, ["Fun"], (h, c) => h + c), ...next]);
  // bare `fun x => f x ω` and numeric literal args (`eLpNorm f 1 μ`) may be omitted
  // lambda arguments (`Summable fun n => T n ^ 2` → Summable) and numeric literals may be omitted
  const optional = fun || (cls(u) === "LeanToken" && /^\d+$/.test(u.text || ""));
  if (compound && !simple && !fun && opts.__embedHead) next = uniq([...next, ...cartJoin(acc, alts, joinHeadChild)]);
  return optional ? uniq([...next, ...acc]) : next;
}

const CONST_TOKENS = new Set(["univ", "⊤", "⊥", "∅"]);
/** Constant arguments of a leaf-headed application, e.g. `μ Set.univ` → Univ. */
function leafHeadConstArgs(args, opts) {
  const out = [];
  for (const a of args) {
    const u = unwrapParen(a);
    const c = cls(u);
    const isConst = (c === "LeanProperty" && cls(u.args?.[0]) === "LeanToken" && /^[A-Z]/.test(u.args[0].text || "") && cls(u.args?.[1]) === "LeanToken") ||
      (c === "LeanToken" && CONST_TOKENS.has(u.text) && !opts.leaves?.has(u.text));
    if (!isConst) continue;
    const n = c === "LeanProperty" ? nameToken(u.args[1].text) : nameToken(u.text);
    if (n) out.push(n);
  }
  return out;
}

/** Relation alternatives: `ae` soft relations for ᵐ, literal-left mirroring, identity. */
function relationAlts(node, tag0, opts) {
  const args = node.args || [];
  const ae = node.superscript === "ᵐ";
  const T = (t) => (ae ? "Ae" + t : t);
  const T0 = T;
  const S = (t) => (t === "Iff" ? "is" : t === "Subset" ? "sub" : ae ? (t === "Eq" ? "ae" : "ae" + t) : t.toLowerCase());
  const leftAlts = nameExprAlts(args[0], opts);
  const rightAlts = nameExprAlts(args[1], opts);
  const gen = (tag, L, R) => {
    const soft = S(tag);
    const out = [];
    if (tag === "Eq" || tag === "Iff") { const rs = new Set(R); for (const l of L) if (l && rs.has(l)) out.push(l); }
    // preferred alternatives of both sides first (diagonal order), so caps keep the best pairs
    const pairs = [];
    for (let i = 0; i < L.length; i++) for (let j = 0; j < R.length; j++) pairs.push([i + j, i, j]);
    pairs.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const [, i, j] of pairs) {
      {
        const l = L[i];
        const r = R[j];
        if (!l || !r) continue;
        if (l === r && (tag === "Eq" || tag === "Iff")) out.push(l); // Identity: Sum = Sum.eq.Sum
        if (l === r && tag !== "Eq" && tag !== "Iff") out.push(T(tag) + l); // same kind on both sides: 𝔼 f ≥ 𝔼 g → GeExpect, GeLim
        if (l === r && !l.includes("/")) out.push(T(tag) + (pluralSnakeS(l) || pluralLetterS(l) || pluralMidS(l))); // Real/LeCoeS/is/Le, AddLimS
        {
          // hypotheses prefer the inline spelling (…/of/Any_Ge_0AndAll_LeNormSub_MulNormSub, canonical); `/rel/` kept as alternative (List/…/of/Add/eq/SubLength_1)
          if (r === "0" && (soft === "gt" || soft === "lt")) out.push(l + "/" + (soft === "gt" ? "Gt_0" : "Lt_0"));
          if (l === "0" && (soft === "gt" || soft === "lt")) out.push(r + "/" + (soft === "lt" ? "Gt_0" : "Lt_0"));
          out.push(l + "/" + soft + "/" + r);
        }
        out.push(T(tag) + l + r);
        out.push(l + T(tag) + r);
        if (l !== r && l.startsWith(r)) out.push(T(tag) + l);
        out.push(T(tag) + l + "_" + r);
      }
    }
    if (!L.length && R.length) for (const r of R) { out.push(T(tag) + "_" + r); out.push(T(tag) + r); }
    if (L.length && !R.length) {
      for (const l of L) {
        const m = mirroredFocus(tag, l);
        if (m) out.push(T(m));
        out.push(T(tag) + l);
        out.push(T(tag) + "_" + l);
      }
    }
    if (!L.length && !R.length) out.push(T(tag));
    if (tag === "Subset") {
      // `S ⊆ K` with a hole K reads as S (ContinuousSemiflow/OmegaLimitToFun/of/…); `F a ⊆ F b` → Subset
      if (!R.length) for (const l of L) out.push(l);
      if (!L.length) for (const r of R) out.push(r);
      for (const l of L) if (R.includes(l)) out.push(T(tag));
    }
    // the section itself is the subject: AbsorbingSet/Subset_PhaseSpace (absorbing_set … ⊆ phase_space …)
    if (opts.section && L.includes(opts.section) && !gen.__inner) {
      gen.__inner = true;
      try { out.push(...gen(tag, [], R)); } finally { gen.__inner = false; }
    }
    return out;
  };
  const mirror = MIRROR_REL[tag0] && isConstNode(args[0]) && !isConstNode(args[1]);
  // a cast identity `(n : ℝ*) = (n : ℝ)` / `(a : ℝ*) = (b : ℝ*)` reads Coe
  if (tag0 === "Eq" && args.every((a) => cls(unwrapParen(a)) === "LeanColon") && args.some((a) => isCoeAscription(unwrapParen(a))))
    return uniq([...gen(tag0, leftAlts, rightAlts), "Coe"]);
  // `lim [x → x₀] f x = a`: the limit statement reads Rel_rhs/Lim/Body (Real/Eq_0/Lim/Abs, Real/Eq/Lim/Abs);
  // as a hypothesis the limit side may be implicit (…/of/Eq_0)
  if (cls(unwrapParen(args[0])) === "Lean_lim") {
    const limOut = [];
    const bodyAlts = nameExprAlts(unwrapParen(args[0]).args?.slice(-1)[0], opts);
    const lims = bodyAlts.length ? bodyAlts.map((b) => "Lim/" + b) : ["Lim"];
    const rc = isConstNode(args[1]) ? rightAlts : [];
    for (const l of lims) { for (const r of rc) limOut.push(T0(tag0) + "_" + r + "/" + l); limOut.push(T0(tag0) + "/" + l); }
    for (const r of rightAlts) limOut.push(T0(tag0) + "_" + r);
    return uniq([...gen(tag0, leftAlts, rightAlts), ...limOut]);
  }
  // a lambda side may be abbreviated away: `μ[f | m] ≤ᵐ fun ω => …` → AeLeCondExp
  const isFun = (n) => cls(unwrapParen(n)) === "Lean_fun";
  const dropped = isFun(args[1]) && !isFun(args[0]) ? gen(tag0, leftAlts, []) : isFun(args[0]) && !isFun(args[1]) ? gen(tag0, [], rightAlts) : [];
  return uniq([...(mirror ? gen(MIRROR_REL[tag0], rightAlts, leftAlts) : []), ...dropped, ...gen(tag0, leftAlts, rightAlts)]);
}

function relationCanon(node, tag0, opts) {
  const args = node.args || [];
  const ae = node.superscript === "ᵐ";
  let tag = tag0;
  let left = nameExpr(args[0], opts);
  let right = nameExpr(args[1], opts);
  if (MIRROR_REL[tag] && isConstNode(args[0]) && !isConstNode(args[1])) {
    [left, right] = [right, left];
    tag = MIRROR_REL[tag];
  }
  const T = ae ? "Ae" + tag : tag;
  const soft = tag === "Iff" ? "is" : tag === "Subset" ? "sub" : ae ? (tag === "Eq" ? "ae" : "ae" + tag) : tag.toLowerCase();
  if (left && right) {
    if (left === right && (tag === "Eq" || tag === "Iff")) return left;
    if (opts.asGiven) return T + left + "_" + right;
    if (right === "0" && (soft === "gt" || soft === "lt")) return left + "/" + (soft === "gt" ? "Gt_0" : "Lt_0");
    if (left === "0" && (soft === "gt" || soft === "lt")) return right + "/" + (soft === "lt" ? "Gt_0" : "Lt_0");
    return left + "/" + soft + "/" + right;
  }
  if (!left && right) return snakeFocus(T, right);
  if (left && !right) {
    // `‖x‖ ≤ _` → LeNorm, `μ[f|m] =ᵐ _` → AeEqCondExp (F_Y is reserved for a leading hole)
    const m = mirroredFocus(tag, left);
    return m ? (ae ? "Ae" : "") + m : T + (left === "One" ? "1" : left);
  }
  return T;
}

/** Node kinds named before the generic rules (both canonical and alternatives). */
/** Condition of a set-builder `{x | p x}`; also `{x : α → β | p x}`, which lean.js parses as
 *  `{x : α → (β | p x)}` (the `|` is taken into the binder type). null when not a set-builder. */
function setBuilderCond(n) {
  const u = unwrapParen(n);
  if (cls(u) !== "LeanBrace") return null;
  const a = u.args?.[0];
  if (cls(a) === "LeanBitOr") return a.args?.[1] || null;
  if (cls(a) === "LeanColon") {
    let t = a.args?.[1];
    while (t && cls(t) !== "LeanBitOr" && (cls(t) === "Lean_rightarrow" || cls(t) === "LeanArgsSpaceSeparated")) t = t.args?.[t.args.length - 1];
    if (cls(t) === "LeanBitOr") return t.args?.[1] || null;
  }
  return null;
}
function isSetBuilder(n) { return !!setBuilderCond(n); }
/** Names of a set-builder condition, hypothesis style: `{ω | X ω ≤ t}` → Le, `{ω | t < X ω}` → Gt
 *  (the side mentioning the bound variable is the subject), `{ω | D ω = m + 1}` → Eq_Add_1. */
function setCondNames(node, opts, canon) {
  const cond = setBuilderCond(node);
  const u = unwrapParen(node);
  const a = u.args?.[0];
  const binders = quantBinderNames(a?.args?.[0]);
  const c = unwrapParen(cond);
  const tag = CLASS_TOKEN[cls(c)];
  const go = { ...opts, asGiven: true };
  const N = (n) => (canon ? [nameExpr(n, go)].filter(Boolean) : nameExprAlts(n, go));
  if (MIRROR_REL[tag] && (c.args || []).length === 2 && !mentionsAny(c.args[0], binders) && mentionsAny(c.args[1], binders)) {
    const T = MIRROR_REL[tag];
    const L = N(c.args[1]);
    const R = N(c.args[0]);
    const out = [];
    for (const l of L) for (const r of R) out.push(T + l + "_" + r);
    if (!L.length) for (const r of R) out.push(T + "_" + r);
    if (!R.length) for (const l of L) out.push(T + l);
    if (!canon || !out.length) out.push(T);
    return uniq(out);
  }
  const p = N(cond);
  if (!canon && tag) p.push(tag);
  return uniq(p);
}
/** `f` / `NS.f` (a namespaced constant parsed as a property of a capitalized token) → its text. */
function qualHeadText(n) {
  if (cls(n) === "LeanToken") return n.text || "";
  if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && /^[A-Z]/.test(n.args[0].text || "") && cls(n.args?.[1]) === "LeanToken") return n.args[0].text + "." + n.args[1].text;
  return "";
}
const EMBED_HEADS = new Set(["ofLp", "toLp", "ofL1", "toL1", "ofL2", "toL2", "WithLp.ofLp", "WithLp.toLp", "WithLp.equiv"]);
function appSlice(proto, xs) {
  if (xs.length === 1) return xs[0];
  const n = Object.create(Object.getPrototypeOf(proto));
  Object.assign(n, proto);
  n.args = xs;
  return n;
}
function preAlts(node, opts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  // `{ω | P ω}` → SetOfP (Set/Union_SetOfEq_Add_1/eq/SetOfLe_Add_1)
  if (isSetBuilder(node)) {
    const p = setCondNames(node, opts, canon);
    return p.length ? uniq(p.map((x) => "SetOf" + x)) : ["SetOf"];
  }
  if (c === "Lean_cup" || c === "Lean_cap") {
    const tag = c === "Lean_cup" ? "Union" : "Inter";
    const L = A(args[0]);
    const R = A(args[1]);
    const out = [];
    for (const l of L) for (const r of R) out.push(tag + l + "_" + r, tag + l + r);
    for (const r of R) out.push(tag + "_" + r);
    for (const l of L) out.push(tag + l);
    if (!out.length) out.push(tag);
    return uniq(out);
  }
  if (c === "Lean_lim") {
    const b = A(args[args.length - 1]);
    const lim = b.length ? uniq(b.flatMap((y) => ["Lim" + y, "Lim_" + y, "Lim/" + y])) : ["Lim"];
    if (canon) return lim;
    const base = nameExprAltsBase(node, opts); // the limit may stay implicit (Real/Cos/eq/Sum); keep it within node caps
    return uniq([...lim.slice(0, 30), ...base.slice(0, 200), ...lim, ...base]);
  }
  if ((c === "LeanNorm" || c === "LeanAbs") && cls(unwrapParen(args[0])) === "LeanSub") {
    // ‖f x - f y‖ with the same named function on both sides → NormSubF (NormSubUpdate, AbsSubMaxₐ)
    const sub = unwrapParen(args[0]);
    const l = nameExpr(sub.args?.[0], opts);
    const r = nameExpr(sub.args?.[1], opts);
    const pre = c === "LeanNorm" ? "Norm" : "Abs";
    if (l && l === r && !l.includes("/")) return uniq([pre + "Sub" + l, pre + "Sub" + l.replace(/_/g, ""), pre + "Sub"]);
  }
  if (c === "LeanArgsSpaceSeparated" && args.length >= 2) {
    const head = args[0];
    // `f '' S` → ImageS (Random/QuantileLower_Add/eq/ImageQuantileLower)
    const k = args.findIndex((a, i) => i > 0 && cls(a) === "LeanToken" && a.text === "''");
    if (k > 0 && k < args.length - 1) {
      const S = A(appSlice(node, args.slice(k + 1)));
      const F = A(appSlice(node, args.slice(0, k))).filter((f) => f !== "Fun");
      const out = S.map((s) => "Image" + s);
      if (!canon) for (const f of F) for (const s of S) out.push("Image" + f + s, "Image" + f + "_" + s);
      if (!canon) for (const s of S) out.push("Image_" + s);
      return out.length ? uniq(out) : ["Image"];
    }
    // 𝔼[a : π](f a) → ExpectF (Random/GeExpect/of/Ge)
    if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼" && args.length === 2) {
      const b = A(args[1]);
      return b.length ? uniq(b.flatMap((y) => ["Expect" + y, "Expect_" + y])) : ["Expect"];
    }
    // μ.real {ω | X ω ≤ t} → RealLe (Random/RealLe/le/RealLe, Random/AddRealLeRealGt/eq/One)
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^(real|toReal)$/.test(head.args[1].text || "") && args.length === 2 && isSetBuilder(args[1])) {
      const p = setCondNames(args[1], opts, canon);
      const out = p.map((x) => "Real" + x);
      if (!canon) out.push(...p.map((x) => "RealSetOf" + x), "Real");
      return uniq(out.length ? out : ["Real"]);
    }
    // embeddings of a hole are a hole: WithLp.ofLp w → (hole)
    if (KEEP_GREEK && EMBED_HEADS.has(qualHeadText(head)) && args.slice(1).every((a) => { const u = unwrapParen(a); return cls(u) === "LeanToken" && (opts.leaves?.has(u.text) || /^\d+$/.test(u.text || "")); }) && args.slice(1).some((a) => opts.leaves?.has(unwrapParen(a).text))) {
      return [];
    }
  }
  if (c === "Lean_partial" || c === "LeanPartial") return [];
  // named arguments `(π := X)` are elaboration hints, not path atoms
  if (c === "LeanParenthesis" && cls(args[0]) === "LeanAssign") return [];
  // `fun x => x n`: evaluation at a point → Apply (Measurable_Apply_PiLE)
  if (c === "Lean_fun") {
    const arrow = args[args.length - 1];
    const ac = cls(arrow);
    if (ac === "LeanRightarrow" || ac === "Lean_mapsto") {
      const body = unwrapParen(arrow.args?.[arrow.args.length - 1]);
      const own = quantBinderNames(arrow.args?.[0]);
      if (cls(body) === "LeanArgsSpaceSeparated" && cls(body.args?.[0]) === "LeanToken" && own.has(body.args[0].text) &&
          body.args.slice(1).every((a) => !mentionsAny(a, own))) {
        return canon ? ["Apply"] : uniq(["Apply", ...nameExprAltsBase(node, opts)]);
      }
    }
  }
  if (c === "Lean_mapsto") return A(args[args.length - 1]);
  if (c === "Lean_sqrt") {
    const x = A(args[0]);
    return x.length ? uniq(x.flatMap((y) => ["Sqrt" + y, "Sqrt_" + y])) : ["Sqrt"];
  }
  if (c === "LeanPreimage") {
    const f = A(args[0]);
    return f.length ? uniq(f.flatMap((y) => ["Preimage" + y, "Preimage_" + y])) : ["Preimage"];
  }
  if (c === "LeanInner") {
    let xs = args;
    if (xs.length === 1 && cls(xs[0]) === "LeanArgsCommaSeparated") xs = xs[0].args || [];
    const a = A(xs[0]);
    const b = A(xs[1]);
    if (!a.length && !b.length) return ["Inner"];
    if (!a.length) return uniq(b.map((y) => "Inner_" + y));
    if (!b.length) return uniq(a.map((x) => "Inner" + x));
    return uniq(a.flatMap((x) => b.flatMap((y) => ["Inner" + x + "_" + y, "Inner" + x + y])));
  }
  if (c === "LeanGetElem") {
    const h = args[0];
    const idx = args[1];
    const cx = condExpArg(node);
    if (cx) {
      // μ[X | m]: conditional expectation
      const x = A(cx);
      return x.length ? uniq(x.flatMap((y) => ["CondExp" + y, "CondExp_" + y])) : ["CondExp"];
    }
    const t = normHead(node, opts);
    if (t !== node) return [nameToken(t.text)].filter(Boolean);
  }
  if (c === "Lean_int") {
    const body = args[args.length - 1];
    let core = body;
    if (cls(body) === "LeanArgsSpaceSeparated") {
      const bs = (body.args || []).filter((x) => cls(x) !== "Lean_partial" && cls(x) !== "LeanPartial");
      if (bs.length !== (body.args || []).length) {
        if (bs.length === 1) core = bs[0];
        else {
          core = Object.create(Object.getPrototypeOf(body));
          Object.assign(core, body);
          core.args = bs;
        }
      }
    }
    const b = A(core);
    // in Random/, `∫ ω, f ω ∂μ` is an expectation: Random/Mul_Expect/eq/Expect_Mul, Random/Expect/le/ExpectAbs
    const asExpect = (xs) => (!canon && opts.section === "Random" ? uniq([...xs, ...xs.map((x) => x.replace(/^Integral/, "Expect"))]) : xs);
    if (b.length) return asExpect(uniq(b.flatMap((y) => ["Integral_" + y, "Integral" + y])));
    // hole integrand: the measure may carry the atom, ∫ x, f x ∂(κ ^ n) s → IntegralPow
    const part = cls(body) === "LeanArgsSpaceSeparated" ? (body.args || []).find((x) => cls(x) === "Lean_partial" || cls(x) === "LeanPartial") : null;
    const m = !canon && part ? A(part.args?.[0]) : [];
    return asExpect(uniq(["Integral", ...m.map((y) => "Integral" + y)]));
  }
  if (c === "Lean_prod") {
    const b = A(args[args.length - 1]);
    return b.length ? uniq(b.flatMap((y) => ["Prod_" + y, "Prod" + y])) : ["Prod"];
  }
  return null;
}

/** Preferred renderings added on top of the generic ones. */
function postAlts(node, opts, alts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  if (c === "LeanPow" && cls(args[1]) === "LeanToken" && args[1].text === "2") {
    const b = A(args[0]);
    const sq = b.length ? b.flatMap((y) => ["Square" + y, "Square_" + y]) : ["Square"];
    return uniq([...sq, ...alts]);
  }
  if (c === "Lean_sum" || c === "Lean_prod") {
    const bind = args.slice(0, -1).find((b) => cls(b) === "Lean_in" || cls(b) === "LeanIn");
    const set = unwrapParen(bind?.args?.[1]);
    const setHead = cls(set) === "LeanArgsSpaceSeparated" ? set.args?.[0] : null;
    const sname = cls(setHead) === "LeanToken" && !opts.leaves?.has(setHead.text) ? nameToken(setHead.text) : "";
    if (sname) {
      const tag = (c === "Lean_prod" ? "Prod" : node.superscript === "'" ? "TSum" : "Sum") + sname;
      const b = A(args[args.length - 1]);
      const extra = b.length ? b.flatMap((y) => [tag + "_" + y, tag + y]) : [tag];
      // interval ranges (Ico/Icc/Ioc/Ioo) are kept; `range n` is usually implicit
      alts = /^I[co][co]$/.test(sname) ? uniq(extra.flatMap((e, i) => (i < alts.length ? [e, alts[i]] : [e])).concat(alts.slice(extra.length))) : uniq([...alts, ...(canon ? [] : extra)]);
    }
    // body may be omitted: ∑ k ∈ Ico k n, b k * ∏ i ∈ …, (1 + c i) → SumMulProd
    if (!canon && alts.length) alts = uniq([alts[0], c === "Lean_prod" ? "Prod" : node.superscript === "'" ? "TSum" : "Sum", ...alts.slice(1)]);
  }
  if (c === "LeanPow" && !canon && cls(args[1]) !== "LeanBracket") {
    const b = A(args[0]);
    if (b.length) alts = uniq([...alts, ...b.map((y) => "Pow" + y)]);
  }
  if (c === "Lean_bullet" && !canon) {
    const L = A(args[0]);
    const R = A(args[1]);
    const extra = [];
    for (const l of L.length ? L : [""]) for (const r of R.length ? R : [""]) {
      if (l || r) extra.push("SMul" + l + r);
      if (l && r) extra.push("SMul" + l + "_" + r);
    }
    return uniq([...alts, ...extra]);
  }
  return alts;
}

const NODE_ALT_CAP = 1000;
function nameExprAlts(node, opts = {}) {
  if (!node) return [];
  const pre = preAlts(node, opts, false);
  const alts = postAlts(node, opts, pre ?? nameExprAltsBase(node, opts), false);
  return alts.length > NODE_ALT_CAP ? alts.slice(0, NODE_ALT_CAP) : alts;
}

function nameExpr(node, opts = {}) {
  if (!node) return "";
  const pre = preAlts(node, opts, true);
  const base = pre ? pre[0] || "" : nameExprBase(node, opts);
  return postAlts(node, opts, base ? [base] : [], true)[0] || "";
}

function unwrapParen(node) {
  let n = node;
  while (cls(n) === "LeanParenthesis") n = n.args?.[0];
  return n;
}

/** `«x.bvar»` quotations are holes (like binder leaves), not Bvar atoms. */
function isBvarQuotation(node) {
  if (!node || typeof node !== "object") return false;
  if (cls(node) === "LeanDoubleAngleQuotation") {
    const inner = node.args?.[0];
    if (cls(inner) === "LeanProperty" && cls(inner.args?.[1]) === "LeanToken" && inner.args[1].text === "bvar") {
      return true;
    }
    return isBvarQuotation(inner);
  }
  return false;
}

function eventHasAnd(node) {
  if (!node || typeof node !== "object") return false;
  const n = cls(node);
  if (n === "Lean_land") return true;
  if (n === "LeanParenthesis") return eventHasAnd(node.args?.[0]);
  if (n === "LeanBitOr") return false; // sides checked by caller
  if (Array.isArray(node.args)) return node.args.some(eventHasAnd);
  return false;
}

/**
 * Match `ℙ[μ](E)` written as LeanArgsSpaceSeparated(GetElem(ℙ, μ), (E)).
 * Returns the event node, or null.
 */
function matchProbApp(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "LeanArgsSpaceSeparated") return null;
  const head = n.args?.[0];
  if (cls(head) !== "LeanGetElem") return null;
  if (cls(head.args?.[0]) !== "LeanToken" || head.args[0].text !== "ℙ") return null;
  // Prefer the parenthesized event; ignore trailing density args like `ω`.
  for (let i = 1; i < (n.args || []).length; i++) {
    const a = n.args[i];
    if (cls(a) === "LeanParenthesis") return unwrapParen(a);
  }
  return null;
}

/**
 * Random.Prob* atoms from the event under ℙ[π](·):
 *   E | C with ∧ in C  → ProbCond_Joint
 *   E | C with ∧ in E  → ProbCondJoint
 *   E | C              → ProbCond
 *   ∧-joint event      → ProbS
 *   otherwise          → Prob
 */
function nameProbEvent(event) {
  const e = unwrapParen(event);
  if (cls(e) === "LeanBitOr") {
    const left = unwrapParen(e.args?.[0]);
    const right = unwrapParen(e.args?.[1]);
    const leftAnd = eventHasAnd(left);
    const rightAnd = eventHasAnd(right);
    if (leftAnd && !rightAnd) return "ProbCondJoint";
    if (rightAnd && !leftAnd) return "ProbCond_Joint";
    if (leftAnd && rightAnd) return "ProbCondJoint_Joint";
    return "ProbCond";
  }
  if (eventHasAnd(e)) return "ProbS";
  return "Prob";
}

function nameProbApp(node) {
  const event = matchProbApp(node);
  if (!event) return "";
  return nameProbEvent(event);
}

/**
 * Statement lists: skip `-- imply` comments and `have` scaffolding so path
 * atoms come from the real conclusion (not binder ids like `_hPxy_z` / `hPxyy`).
 */

/**
 * Ae / reference-measure binders: `∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, …`
 * Path convention drops these wrappers (no All_All_All_ prefix). Plain math
 * `∀ x, P x` still gets All_.
 */
function isAeQuantifier(node) {
  if (!node || typeof node !== "object") return false;
  const name = cls(node);
  if (name !== "Lean_forall" && name !== "Lean_exists") return false;
  const head = node.args?.[0];
  let foundPartial = false;
  let foundBvar = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || (foundPartial && foundBvar)) return;
    const c = cls(n);
    if (c === "Lean_partial" || c === "LeanPartial") foundPartial = true;
    if (c === "LeanDoubleAngleQuotation" || c === "LeanDoubleAngleQuotation") {
      const inner = n.args?.[0];
      if (cls(inner) === "LeanProperty" && cls(inner.args?.[1]) === "LeanToken" && inner.args[1].text === "bvar") {
        foundBvar = true;
      }
    }
    if (c === "LeanToken" && (n.text === "ReferenceMeasure" || n.text === "measure")) foundPartial = true;
    if (Array.isArray(n.args)) for (const a of n.args) walk(a);
  };
  walk(head);
  return foundPartial || foundBvar;
}

const MIRROR_REL = { Lt: "Gt", Gt: "Lt", Le: "Ge", Ge: "Le" };
/** `0 < _` → Gt_0, `1 ≤ _` → Ge_1 (literal on the left, hole on the right). */
function mirroredFocus(tag, left) {
  return MIRROR_REL[tag] && /^-?\d+$/.test(left) ? snakeFocus(MIRROR_REL[tag], left) : "";
}

const GUARD_REL = new Set(["Lean_lt", "Lean_gt", "Lean_le", "Lean_ge", "Lean_in", "LeanIn"]);

function guardRestConjunct(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n || cls(n) !== "Lean_land") return null;
  const [left, right] = n.args || [];
  if (!right) return null;
  let l = left;
  while (cls(l) === "LeanParenthesis") l = l.args?.[0];
  return GUARD_REL.has(cls(l)) ? right : null;
}

/** Names bound by a quantifier head: `x`, `x y`, `x : T`, `(i : Fin m) (j : Fin n)`, `x ∈ A`, `x | p x`. */
function quantBinderNames(head, out = new Set()) {
  const c = cls(head);
  if (c === "LeanToken") { if (head.text && head.text !== "_") out.add(head.text); }
  else if (c === "LeanColon" || c === "LeanBitOr" || GUARD_REL.has(c)) quantBinderNames(head.args?.[0], out);
  else if (c === "LeanParenthesis" || c === "LeanArgsSpaceSeparated") for (const a of head.args || []) quantBinderNames(a, out);
  return out;
}

/** Number of variables bound by a ∀/∃ head (`∀ x y` → 2, `∀ n ≥ n₀` → 1). */
function quantArity(node) {
  return quantBinderNames(node.args?.[0]).size;
}

function mentionsAny(node, names) {
  if (!node || typeof node !== "object") return false;
  if (cls(node) === "LeanToken") return names.has(node.text);
  return (node.args || []).some((a) => mentionsAny(a, names));
}

/**
 * Rest conjunct after a binder restriction. Besides `<`/`∈` guards (any quantifier),
 * for `∃ x, R x ∧ Q` the first conjunct R x (any predicate on a bound variable) is the
 * domain restriction and may be dropped: `Any_And_Q` (cf. Matrix/Any_And_Stationary,
 * Vector/Any_And_EqGetFlatten, Set/Any_And_In).
 */
function existsRestConjunct(quant) {
  const body = quant.args?.[quant.args.length - 1];
  const guarded = guardRestConjunct(body);
  if (guarded || cls(quant) !== "Lean_exists") return guarded;
  let n = body;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (cls(n) !== "Lean_land" || !n.args?.[1]) return null;
  return mentionsAny(n.args[0], quantBinderNames(quant.args?.[0])) ? n.args[1] : null;
}

function splitTopConjunction(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n || cls(n) !== "Lean_land") return null;
  const [left, right] = n.args || [];
  if (!left || !right) return null;
  const leftParts = splitTopConjunction(left);
  return [...(leftParts || [left]), right];
}

function firstConclusion(node) {
  const args = node?.args || [];
  const meaningful = args.filter((a) => {
    const c = cls(a);
    return c && c !== "LeanLineComment" && c !== "Lean_have";
  });
  if (meaningful.length) return meaningful[meaningful.length - 1];
  return args.filter((a) => cls(a) !== "LeanLineComment").pop() || null;
}

/**
 * Rough lean.js path atom(s). Offline fallback for phase-1 scaffolding;
 * naming alts for structured expressions also live in nameExprAlts.
 */
/** `(x : ℝ*)`: a cast into the hyperreals reads `Coe` (Real/LeCoeS/is/Le, Hyperreal/GtCoe_0/is/Gt_0). */
function isCoeAscription(node) {
  return cls(node) === "LeanColon" && hasNode(node.args?.[1], (n) => cls(n) === "LeanToken" && n.text === "ℝ*");
}

function nameExprBase(node, opts = {}) {
  if (!node) return "";
  const name = cls(node);
  if (isCoeAscription(node)) return "Coe" + nameExpr(node.args[0], opts);

  // Local `have` in imply is proof scaffolding — never a path atom.
  if (name === "Lean_have") return "";
  if (isBvarQuotation(node)) return "";

  // ℙ[π](E) / ℙ[π](E | C) → Prob / ProbS / ProbCond*
  {
    const probName = nameProbApp(node);
    if (probName) return probName;
  }

  if (name === "LeanStatements" || name === "LeanArgsNewLineSeparated") {
    return nameExpr(firstConclusion(node), opts);
  }

  if (CLASS_TOKEN[name]) {
    // Arith ops stay Camel (DivLeftRight) / Prob idioms — not Left/div/Right paths.
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg"]);
    if (!ARITH.has(name)) {
    const tag = CLASS_TOKEN[name];
    const args = node.args || [];
    if (name === "Lean_exists" && node.unique) {
      const core = nameExpr(existsRestConjunct(node) || args[args.length - 1], opts);
      return core ? core + "/Unique" : "Unique";
    }
    if (name === "Lean_exists" || name === "Lean_forall") {
      const body = nameExpr(args[args.length - 1], opts);
      if (!body) return tag;
      // `∀ᵐ x ∂μ, P` → AeP (AeTendsto, AeAll_Le…); ReferenceMeasure binders stay implicit
      if (isAeQuantifier(node)) return node.superscript === "ᵐ" ? "Ae" + body : body;
      const rest = existsRestConjunct(node);
      const multi = ""; // `∀ x y` is usually spelled All (Iterates/Any_Ge_0AndAll_LeNormSub_MulNormSub); All_All kept as alternative
      // ∃ C, 0 ≤ C ∧ Q → Any_Ge_0AndQ, relations inline (Any_Ge_0AndAll_LeNormSub_MulNormSub)
      if (guardRestConjunct(args[args.length - 1]) && name === "Lean_exists") { const g = nameExpr(args[args.length - 1], { ...opts, asGiven: true }); if (g && !g.includes("/")) return tag + "_" + g; }
      if (rest) {
        const restName = nameExpr(rest, opts);
        if (restName) return tag + "_And_" + restName;
      }
      if (!body.includes("/") && /^Eq/.test(body)) return multi + tag + "_" + body; // ∀ i, f i = g i → All_Eq
      // `∀ t, τ ≤ t → P t` with a named bound τ keeps the implication (ForwardSolvesCriticEquation/All_Imp_LeNorm);
      // a constant guard (`∀ t, 0 ≤ t → P t`) stays implicit (…/All_LeNorm)
      if (name === "Lean_forall" && !body.includes("/")) {
        const imp = unwrapParen(args[args.length - 1]);
        const prem = cls(imp) === "Lean_rightarrow" ? unwrapParen(imp.args?.[0]) : null;
        const bound = new Set();
        quantBinderNames(args[0], bound);
        if (prem && ["Lean_le", "Lean_lt", "Lean_ge", "Lean_gt"].includes(cls(prem)) && (prem.args || []).length === 2) {
          const [a, b] = prem.args.map(unwrapParen);
          const isB = (x) => cls(x) === "LeanToken" && bound.has(x.text);
          const other = isB(a) && !isB(b) ? b : isB(b) && !isB(a) ? a : null;
          if (other && !isConstNode(other) && cls(other) !== "LeanToken" && nameExpr(other, opts)) return tag + "_Imp_" + body;
        }
      }
      if (body.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(body)) return body;
      return multi + tag + "_" + body;
    }
    if (name === "Lean_lnot") {
      const body = nameExpr(args[args.length - 1], opts);
      return body ? "Not" + body : "Not";
    }
    if (name === "Lean_land" || name === "Lean_lor") {
      const left = nameExpr(args[0], opts);
      const right = nameExpr(args[1], opts);
      const join = name === "Lean_lor" ? "Or" : "And";
      if (left && right) return left + join + right;
      return left || right || join;
    }
    return relationCanon(node, tag, opts);
    } // end non-arith CLASS_TOKEN
  }

  if (name === "Lean_sum") {
    const tag = node.superscript === "'" ? "TSum" : "Sum";
    const args = node.args || [];
    const body = nameExpr(args[args.length - 1], opts);
    return body ? tag + "_" + body : tag;
  }

  const WRAP_OP_PREFIX = {
    LeanNorm: "Norm",
    LeanAbs: "Abs",
    LeanCeil: "Ceil",
    LeanFloor: "Floor",
  };
  const wrapPrefix = WRAP_OP_PREFIX[name];
  if (wrapPrefix !== undefined) {
    const arg = node.args?.[0];
    if (cls(unwrapParen(arg)) === "LeanSub") return wrapPrefix + "Sub";
    const leafHead = cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken" && opts.leaves?.has(arg.args[0].text) && cls(unwrapParen(arg.args?.[1])) !== "LeanSub";
    if (leafHead) return wrapPrefix; // ‖e₁ (n + 1) ω‖ with binder e₁ → Norm (arguments are indices)
    if (cls(arg) === "LeanArgsSpaceSeparated" && (cls(arg.args?.[0]) === "LeanToken" || cls(arg.args?.[0]) === "LeanProperty")) {
      const headNode = arg.args[0];
      const camelFn = cls(headNode) === "LeanToken" ? nameToken(headNode.text) : nameExpr(headNode, opts);
      const inner = unwrapParen(arg.args?.[1]);
      if (cls(inner) === "LeanSub") return wrapPrefix + camelFn + nameExpr(inner, opts);
      return wrapPrefix + camelFn;
    }
    const inner = nameExpr(arg, opts);
    // ‖x + y‖ → NormAdd (bare operator tag), ‖f x‖ → Norm_F
    return inner ? wrapPrefix + (/^[A-Z][a-z]+$/.test(inner) && CLASS_TOKEN[cls(unwrapParen(arg))] ? "" : "_") + inner : wrapPrefix;
  }

  if (name === "LeanToken") {
    const raw = node.text || "";
    if (opts.leaves?.has(raw)) return ""; // binder leaf → hole
    if (/^-?\d+$/.test(raw)) return raw; // keep 0, 1, etc.
    return nameToken(raw);
  }

  if (name === "LeanConstruct") {
    // Inductive.mk → type name when available on the construct head.
    const head = node.args?.[0];
    if (cls(head) === "LeanToken") {
      const t = head.text || "";
      if (t.endsWith(".mk")) {
        const typ = t.slice(0, -3);
        const seg = typ.includes(".") ? typ.slice(typ.lastIndexOf(".") + 1) : typ;
        return nameToken(seg);
      }
      return nameToken(t);
    }
    return nameExpr(head, opts);
  }

  if (name === "LeanProperty") {
    // AST heuristic for const vs method naming.
    // Bare-token receiver (ns.f or x.f) -> prop only; structured receiver -> PropReceiver.
    const obj = node.args?.[0];
    const prop = node.args?.[1];
    const propName = cls(prop) === "LeanToken" ? nameToken(prop.text || "") || nameExpr(prop, opts) : nameExpr(prop, opts);
    if (cls(obj) === "LeanToken") return propName || "";
    const objName = nameExpr(obj, opts);
    if (objName && propName) return propName + objName;
    return propName || objName || "";
  }
  if (name === "LeanParenthesis") return nameExpr(node.args?.[0], opts);
  if (name === "Lean_fun" || name === "LeanRightarrow" || name === "Lean_rightarrow") {
    const body = node.args?.[node.args.length - 1];
    const bodyName = nameExpr(body, opts);
    // `→` / `=>`: path follows the conclusion (drop `P ≠ 0 →` guards).
    if (name === "LeanRightarrow" || name === "Lean_rightarrow") return bodyName;
    // `fun x => body` is transparent: Summable_Integral, TendstoSum; a hole body stays `Fun` (MapFun)
    return bodyName || "Fun";
  }
  if (name === "LeanArgsSpaceSeparated") {
    const args = node.args || [];
    const head = normHead(args[0], opts);
    if (cls(head) === "LeanToken" && head.text === "Pairwise") {
      let restNode = args[1];
      while (cls(restNode) === "LeanParenthesis") restNode = restNode.args?.[0];
      if (cls(restNode) === "Lean_fun" || cls(restNode) === "LeanRightarrow") {
        restNode = restNode.args?.[restNode.args.length - 1];
      }
      const rest = nameExpr(restNode, opts);
      return rest ? "Pairwise_" + rest : "Pairwise";
    }
    const last = args[args.length - 1];
    if (cls(last) === "LeanParenthesis" && cls(last.args?.[0]) === "LeanSub") {
      // F data (μ - ν) with a named F → F_Sub (ForwardSolvesStateEquation_Sub); unknown f → UFnSub
      const hn = cls(head) === "LeanToken" && !opts.leaves?.has(head.text) ? nameToken(head.text) : "";
      return hn ? hn + "_Sub" : "UFnSub";
    }
    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headName = nameExpr(head, opts);
      if (headName) {
        let acc = fnLikeHead(head) ? headName : joinHeadChild("Get", headName);
        for (const a of args.slice(1)) {
          const an = nameExpr(a, opts);
          if (an) acc = joinHeadChild(acc, an);
        }
        return acc;
      }
    }
    if (cls(head) === "LeanProperty") {
      const method = nameExpr(head, opts);
      const argNames = args.slice(1).map((a) => nameExpr(a, opts)).filter(Boolean);
      // FlatMap (Fun...) -> FlatMap_Fun... ; Product (Cons) -> ProductCons
      if (method && argNames.length === 1) {
        const arg = argNames[0];
        const argNode = args.slice(1).find((a) => nameExpr(a, opts) === arg);
        const u = unwrapParen(argNode);
        if (arg === "Fun") return method + arg;
        if (arg.startsWith("Fun")) return method + "_" + arg;
        // method-call argument: (dirac C).prod (μ.map Y) → ProdDirac_Map
        if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanProperty") return method + "_" + arg;
        if (cls(u) === "Lean_fun") return funBodyUnary(u) ? method + arg : method + "_" + arg;
        return method + arg;
      }
      if (method && argNames.length === 0) return method;
      if (method && argNames.length > 1) return method + "_" + argNames.reduce(joinDigits);
    }
    if (cls(head) === "LeanToken") {
      const headName = opts.leaves?.has(head.text) ? "" : nameToken(head.text || "");
      let argPairs = args.slice(1).map((a) => [a, nameExpr(a, opts)]).filter(([_, n]) => n);
      if (argPairs.length > 1 || (argPairs.length === 1 && args.length > 2 && head === args[0])) argPairs = argPairs.filter(([a, n]) => !(n === "Fun" && cls(unwrapParen(a)) === "Lean_fun")); // Tendsto (fun n => x n ω) atTop (𝓝 x*) → Tendsto
      const argNames = argPairs.map(([_, n]) => n);
      const idxName = head !== args[0] ? nameExpr(args[0].args?.[1], opts) : "";
      if (idxName) {
        // σ-algebra index last: Measurable[Filtration.piLE n] (frestrictLe n) → Measurable_FrestrictLe_PiLE
        let inner = argNames.length ? headName + "_" + argNames.reduce(joinDigits) : headName;
        if (argNames.length === 1) {
          const [an, arg] = argPairs[0];
          const camel = arg === "Fun" || cls(an) === "LeanToken" || (cls(unwrapParen(an)) === "Lean_fun" && funBodyUnary(an));
          inner = headName + (camel ? "" : "_") + arg;
        }
        return inner + "_" + idxName;
      }
      if (headName && argNames.length === 1) {
        const [argNode, arg] = argPairs[0];
        if (arg === "Fun") return headName + arg;
        if (cls(unwrapParen(argNode)) === "Lean_fun") return funBodyUnary(argNode) ? headName + arg : headName + "_" + arg;
        if (arg.startsWith("Fun")) return headName + "_" + arg;
        if (!isSimpleArg(argNode, opts)) return headName + "_" + arg;
        return headName + arg;
      }
      if (headName && argNames.length === 0) return headName;
      if (headName && argNames.length > 1) return headName + "_" + argNames.reduce(joinDigits);
    }
    const named = args.map((a) => nameExpr(a, opts)).filter(Boolean);
    if (named.length === 0) return "";
    if (named.length === 1) return named[0];
    return named.join("");
  }
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ")) {
    let tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanPow" && cls(args[1]) === "LeanBracket") tag = "Iterate";
    if (name === "LeanNeg") {
      const body = nameExpr(args[0], opts);
      return body ? "Neg" + body : "Neg";
    }
    if (name === "LeanMul") {
      const sub = subscriptedMulAtom(node);
      if (sub) {
        const right = nameExpr(args[1], opts);
        const left = nameExpr(args[0], opts);
        if (right && left) return sub + left + "_" + right;
        if (right) return sub + "_" + right;
        if (left) return sub + left;
        return sub;
      }
    }
    if (name === "LeanDiv" || name === "LeanMul") {
      const lEv = matchProbApp(args[0]);
      const rEv = matchProbApp(args[1]);
      if (lEv && rEv) {
        const ln = nameProbEvent(lEv);
        const rn = nameProbEvent(rEv);
        if (name === "LeanDiv") {
          if (ln === "ProbCondJoint" && rn === "ProbCond") return "DivProbSCond";
          if (ln === "ProbCond_Joint" && rn === "ProbCond") return "DivProbSCond";
          if (ln === "ProbCondJoint" && rn === "ProbCond_Joint") return "DivProbSCond";
          if (ln === "ProbS" && rn === "ProbS") return "DivProbSCond";
          if (ln === "ProbS" && rn === "Prob") return "DivProbS";
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return "Div" + ln + rn;
        }
        if (name === "LeanMul") {
          if (ln.startsWith("ProbCond") && rn.startsWith("ProbCond")) return "MulProbCond";
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return "Mul" + ln + rn;
        }
      }
    }
    const left = nameExpr(args[0], opts);
    const right = nameExpr(args[1], opts);
    if (left && right) {
      if (left === right) return tag + (pluralSnakeS(left) || pluralLetterS(left) || pluralMidS(left));
      return tag + joinDigits(left, right);
    }
    // C * ‖x - y‖ → MulNormSub: a wrapped (norm/abs) right operand reads camel like a unary head
    if (right) return ["LeanNorm", "LeanAbs"].includes(cls(unwrapParen(args[1]))) && /^(Norm|Abs)[A-Z]/.test(right) ? tag + right : snakeFocus(tag, right);
    if (left) return tag + left; // x * c with hole x: MulUniv (Snake F_Y only for a leading hole)
    return tag;
  }
  if (name === "LeanDoubleAngleQuotation") {
    return "";
  }
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return "Prob";
  }
  if (name === "LeanBitOr") {
    return "";
  }
  if (Array.isArray(node.args)) {
    for (const a of node.args) { const n = nameExpr(a, opts); if (n) return n; }
  }
  return "";
}

/** Join head + child with Camel or Snake style */
function joinHeadChild(head, child) {
  if (!child) return head;
  if (!head) return child;
  if (/\d$/.test(head) && /^\d/.test(child)) return head + "'" + child;
  if (child.startsWith("Fun") || child.includes("_")) {
    if (!child.startsWith("Fun") && child.includes("_")) return head + child;
    return head + "_" + child;
  }
  return head + child;
}

/** `∀ x y, f x y ≤ g x y` with plain binders and both sides leaf functions applied to exactly those binders. */
function piPointwise(node) {
  const args = node.args || [];
  const names = [];
  for (const b of args.slice(0, -1)) {
    if (cls(b) === "LeanToken") names.push(b.text);
    else if (cls(b) === "LeanArgsSpaceSeparated" && b.args.every((x) => cls(x) === "LeanToken")) names.push(...b.args.map((x) => x.text));
    else return false;
  }
  const body = unwrapParen(args[args.length - 1]);
  if (!names.length || !["Lean_le", "Lean_lt", "Lean_ge", "Lean_gt"].includes(cls(body))) return false;
  const app = (s) => { const u = unwrapParen(s); return cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken" && u.args.length === names.length + 1 && u.args.slice(1).every((x, i) => cls(x) === "LeanToken" && x.text === names[i]); };
  return (body.args || []).length === 2 && body.args.every(app);
}

function nameExprAltsBase(node, opts = {}) {
  if (!node) return [];
  const name = cls(node);
  if (isCoeAscription(node)) {
    const inner = nameExprAlts(node.args[0], opts);
    return inner.length ? uniq(inner.map((x) => "Coe" + x)) : ["Coe"];
  }

  if (name === "Lean_have" || isBvarQuotation(node)) return [];

  // ℙ[π](E) probability idioms
  const probName = nameProbApp(node);
  if (probName) return [probName];

  if (name === "LeanStatements" || name === "LeanArgsNewLineSeparated") {
    return nameExprAlts(firstConclusion(node), opts);
  }

  if (CLASS_TOKEN[name]) {
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg"]);
    if (!ARITH.has(name)) {
      const tag = CLASS_TOKEN[name];
      const args = node.args || [];
      if (name === "Lean_exists" && node.unique) {
        const core = nameExprAlts(existsRestConjunct(node) || args[args.length - 1], opts);
        return core.length ? uniq(core.map((c) => c + "/Unique")) : ["Unique"];
      }
      if (name === "Lean_exists" || name === "Lean_forall") {
        const bodyNode = args[args.length - 1];
        const bodyAlts = nameExprAlts(bodyNode, opts);
        const rest = existsRestConjunct(node);
        const guardAlts = rest ? nameExprAlts(rest, opts).map((r) => tag + "_And_" + r) : [];
        if (!bodyAlts.length) return uniq([...guardAlts, tag]);
        if (isAeQuantifier(node)) {
          // `∀ᵐ x ∂μ, P` → AeP preferred (AeTendsto, AeAll_…); All_P / bare P kept (Random/All_Summable)
          return uniq(node.superscript === "ᵐ" ? [...bodyAlts.map((b) => "Ae" + b), ...bodyAlts.map((b) => tag + "_" + b), ...bodyAlts, ...guardAlts] : [...bodyAlts, ...guardAlts]);
        }
        if (quantArity(node) >= 2 && !node.__singleQuant) {
          node.__singleQuant = true;
          let single;
          try { single = nameExprAlts(node, opts); } finally { delete node.__singleQuant; }
          // `∀ x y, P` → All_All_P (distinct from `∀ x, P`)
          const inner = nameExprAlts(bodyNode, opts);
          const tagged = inner.filter((b) => !b.includes("/")).flatMap((b) => [tag + "_" + tag + "_" + b, tag + "_" + tag + b]);
          const rel = inner.filter((b) => b.includes("/") || /^(Prob|DivProb|MulProb)/.test(b));
          return uniq([...single.slice(0, 300), ...tagged.slice(0, 300), ...single.slice(300), ...rel, ...guardAlts, ...tagged.slice(300)]);
        }
        if (bodyAlts.some(b => b.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(b))) {
          // `∀ i ∈ s, f i = g i` → All_Eq (Finset/Sum/of/All_Eq, Kernel/All_Eq)
          const eqT = bodyAlts.filter((b) => !b.includes("/") && /^Eq/.test(b)).map((b) => tag + "_" + b);
          // relational bodies usually read `A/eq/B`; a one-atom rendering may still take the tag (All_AeLeCondExp)
          const tagged = bodyAlts.filter((b) => !b.includes("/")).flatMap((b) => [tag + "_" + b, tag + b]);
          return uniq([...eqT, ...tagged.slice(0, 200), ...bodyAlts, ...guardAlts, ...tagged.slice(200)]);
        }
        const out = [];
        for (const b of bodyAlts) {
          out.push(tag + "_" + b);
          out.push(tag + b);
        }
        // `∀ x, P x → Q x` may keep the implication: All_Imp_Q (Random/All_Imp_*, Bool/All_Imp)
        if (cls(unwrapParen(bodyNode)) === "Lean_rightarrow") for (const b of bodyAlts) out.push(tag + "_Imp_" + b);
        // `∀ ω, f ω ≤ g ω` is the pointwise order `f ≤ g`: the bare relation is an alternative
        if (name === "Lean_forall" && !rest && piPointwise(node)) out.push(...bodyAlts);
        return uniq([...guardAlts, ...out]);
      }
      if (name === "Lean_lnot") {
        const bodyAlts = nameExprAlts(args[args.length - 1], opts);
        if (!bodyAlts.length) return ["Not"];
        return bodyAlts.map(b => "Not" + b);
      }
      if (name === "Lean_land" || name === "Lean_lor") {
        const leftAlts = nameExprAlts(args[0], opts);
        const rightAlts = nameExprAlts(args[1], opts);
        const join = name === "Lean_lor" ? "Or" : "And";
        const out = [];
        for (const l of leftAlts) {
          for (const r of rightAlts) {
            out.push(l + join + r);
            out.push(l + "_" + join + "_" + r);
          }
        }
        return uniq(out);
      }
      return relationAlts(node, tag, opts);
    }
  }

  if (name === "Lean_sum") {
    const tag = node.superscript === "'" ? "TSum" : "Sum";
    const args = node.args || [];
    const bodyAlts = nameExprAlts(args[args.length - 1], opts);
    if (!bodyAlts.length) return [tag];
    return uniq(bodyAlts.flatMap((b) => [tag + "_" + b, tag + b]));
  }

  // Wrapper ops: Norm, Abs, Ceil, Floor
  const WRAP_OP_PREFIX = { LeanNorm: "Norm", LeanAbs: "Abs", LeanCeil: "Ceil", LeanFloor: "Floor" };
  const wrapPrefix = WRAP_OP_PREFIX[name];
  if (wrapPrefix !== undefined) {
    const arg = node.args?.[0];
    if (cls(unwrapParen(arg)) === "LeanSub") return [wrapPrefix + "Sub"];
    const leafHead = cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken" && opts.leaves?.has(arg.args[0].text) && cls(unwrapParen(arg.args?.[1])) !== "LeanSub";
    const oldLeaf = leafHead ? [wrapPrefix + nameToken(arg.args[0].text)] : [];
    if (!leafHead && cls(arg) === "LeanArgsSpaceSeparated" && (cls(arg.args?.[0]) === "LeanToken" || cls(arg.args?.[0]) === "LeanProperty")) {
      const headNode = arg.args[0];
      const headAlts = cls(headNode) === "LeanToken" ? [nameToken(headNode.text)] : nameExprAlts(headNode, opts);
      const inner = unwrapParen(arg.args?.[1]);
      if (cls(inner) !== "LeanSub") return uniq(headAlts.map((h) => wrapPrefix + h));
      const subAlts = nameExprAlts(inner, opts);
      const heads = headAlts.map((h) => wrapPrefix + h);
      return uniq([...cartJoin(heads, subAlts, (a, b) => a + b), ...heads.map((h) => h + "Sub")]);
    }
    const innerAlts = nameExprAlts(arg, opts);
    if (!innerAlts.length || leafHead) return uniq([wrapPrefix, ...innerAlts.slice(0, 50).map((i) => wrapPrefix + "_" + i), ...oldLeaf]);
    const out = [];
    for (const i of innerAlts) {
      out.push(wrapPrefix + "_" + i);
      out.push(wrapPrefix + i);
    }
    return uniq([...out, ...oldLeaf]);
  }

  if (name === "LeanToken") {
    const raw = node.text || "";
    if (opts.leaves?.has(raw)) return [];
    if (raw === "1") return ["1"];
    if (/^-?\d+$/.test(raw)) return [raw];
    const nt = nameToken(raw);
    return nt ? [nt] : [];
  }

  if (name === "LeanConstruct") {
    const head = node.args?.[0];
    if (cls(head) === "LeanToken") {
      const t = head.text || "";
      if (t.endsWith(".mk")) {
        const typ = t.slice(0, -3);
        const seg = typ.includes(".") ? typ.slice(typ.lastIndexOf(".") + 1) : typ;
        return [nameToken(seg)];
      }
      return [nameToken(t)];
    }
    return nameExprAlts(head, opts);
  }

  if (name === "LeanProperty") {
    const obj = node.args?.[0];
    const prop = node.args?.[1];
    const propAlts = cls(prop) === "LeanToken"
      ? (nameToken(prop.text || "") ? [nameToken(prop.text || "")] : nameExprAlts(prop, opts))
      : nameExprAlts(prop, opts);
    if (cls(obj) === "LeanToken") return propAlts;
    const objAlts = nameExprAlts(obj, opts);
    const out = [];
    for (const o of objAlts) {
      for (const p of propAlts) {
        if (o && p) {
          out.push(p + o);
          out.push(o + p);
        }
      }
    }
    for (const p of propAlts) if (p) out.push(p);
    for (const o of objAlts) if (o) out.push(o);
    return uniq(out);
  }

  if (name === "LeanParenthesis") return nameExprAlts(node.args?.[0], opts);

  if (name === "Lean_fun" || name === "LeanRightarrow" || name === "Lean_rightarrow") {
    const body = node.args?.[node.args.length - 1];
    const bodyAlts = nameExprAlts(body, opts);
    if (name === "LeanRightarrow" || name === "Lean_rightarrow") return bodyAlts;
    if (!bodyAlts.length) return ["Fun"];
    // transparent `fun` first (Summable_Integral, TendstoSum), `Fun…` spellings kept
    return uniq([...bodyAlts, ...bodyAlts.map(b => b.startsWith("Fun") ? b : "Fun" + b)]);
  }

  if (name === "LeanArgsSpaceSeparated") {
    const args = node.args || [];
    const head = normHead(args[0], opts);
    // Pairwise special case
    if (cls(head) === "LeanToken" && head.text === "Pairwise") {
      let restNode = args[1];
      while (cls(restNode) === "LeanParenthesis") restNode = restNode.args?.[0];
      if (cls(restNode) === "Lean_fun" || cls(restNode) === "LeanRightarrow") {
        restNode = restNode.args?.[restNode.args.length - 1];
      }
      const restAlts = nameExprAlts(restNode, opts);
      if (!restAlts.length) return ["Pairwise"];
      return restAlts.map(r => "Pairwise_" + r);
    }
    // UFnSub special case
    const last = args[args.length - 1];
    if (cls(last) === "LeanParenthesis" && cls(last.args?.[0]) === "LeanSub") {
      const hn = cls(head) === "LeanToken" && !opts.leaves?.has(head.text) ? [nameToken(head.text)] : [];
      return uniq([...hn.filter(Boolean).map((h) => h + "_Sub"), "UFnSub"]);
    }

    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headAlts = nameExprAlts(head, opts);
      if (headAlts.length) {
        const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
        let acc = cartJoin([fnLikeHead(head) ? "" : "Get"], headAlts, joinHeadChild);
        // applied power `(κ ^ n) s` may read without Get: PowKernelMat
        if (cls(unwrapParen(head)) === "LeanPow") acc = uniq([...acc, ...headAlts]);
        const all = [...acc];
        for (const aa of argAltLists) {
          acc = cartJoin(acc, aa, joinHeadChild);
          all.push(...acc);
        }
        return uniq(all);
      }
    }

    // Property head: method(args)
    if (cls(head) === "LeanProperty") {
      const methodAlts = nameExprAlts(head, opts);
      const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
      if (!methodAlts.length) return [];
      if (!argAltLists.length) return methodAlts;
      // Cartesian product of all arg alternatives
      let acc = methodAlts;
      const all = [...methodAlts];
      for (const a of args.slice(1)) {
        const argAlts = nameExprAlts(a, opts);
        if (!argAlts.length) continue;
        acc = uniq([...cartJoin(acc, argAlts, joinHeadChild), ...argJoinAlts(acc, a, argAlts, opts)]);
        all.push(...acc);
      }
      return uniq(all);
    }

    // Token head: Func(args)
    if (cls(head) === "LeanToken") {
      const headLeaf = opts.leaves?.has(head.text);
      const headName = headLeaf ? "" : nameToken(head.text || "");
      if (!headName) {
        // `μ Set.univ` → Univ; dropped notation heads (`𝓝 0`) → their arguments
        if (headLeaf) {
          const consts = leafHeadConstArgs(args.slice(1), opts);
          return consts.length ? [consts.join("")] : [];
        }
        const rest = args.slice(1).map((a) => nameExprAlts(a, opts)).filter((x) => x.length);
        return rest.length ? rest.reduce((acc, x) => cartJoin(acc, x, (a, b) => a + b)) : [];
      }
      let acc = [headName];
      const all = [headName];
      const embedOpts = EMBED_HEADS.has(head.text) ? { ...opts, __embedHead: true } : opts;
      for (const a of args.slice(1)) {
        const alts = nameExprAlts(a, opts);
        if (!alts.length) continue;
        acc = argJoinAlts(acc, a, alts, embedOpts);
        if (acc.length > NODE_ALT_CAP) acc = acc.slice(0, NODE_ALT_CAP);
        all.push(...acc);
      }
      const idx = head !== args[0] ? nameExprAlts(args[0].args?.[1], opts) : [];
      if (idx.length) return uniq([...cartJoin(acc, idx, (h, i) => h + "_" + i), ...all]);
      return uniq(all);
    }

    // Generic: cartesian product of all arg alts
    const argAltLists = args.map(a => nameExprAlts(a, opts)).filter(a => a.length);
    if (!argAltLists.length) return [];
    if (argAltLists.length === 1) return argAltLists[0];
    let acc = argAltLists[0];
    for (let i = 1; i < argAltLists.length; i++) {
      acc = cartJoin(acc, argAltLists[i], (a, b) => a + b);
    }
    return uniq(acc);
  }

  // Arithmetic ops: Sub, Add, Mul, Div, Pow, Neg
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ")) {
    let tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanPow" && cls(args[1]) === "LeanBracket") tag = "Iterate";
    if (name === "LeanNeg") {
      const bodyAlts = nameExprAlts(args[0], opts);
      if (!bodyAlts.length) return ["Neg"];
      return bodyAlts.map(b => "Neg" + b);
    }
    if (name === "LeanMul") {
      const sub = subscriptedMulAtom(node);
      if (sub) {
        const rightAlts = nameExprAlts(args[1], opts);
        const leftAlts = nameExprAlts(args[0], opts);
        if (rightAlts.length && leftAlts.length) {
          const leftResult = cartJoin([sub], leftAlts, joinHeadChild);
          return uniq(leftResult.flatMap(l => rightAlts.flatMap(r => [l + "_" + r, l + r])));
        }
        if (rightAlts.length) {
          return uniq(rightAlts.flatMap((r) => [sub + "_" + r, sub + r]));
        }
        return leftAlts.length ? cartJoin([sub], leftAlts, joinHeadChild) : [sub];
      }
    }
    if (name === "LeanDiv" || name === "LeanMul") {
      const lEv = matchProbApp(args[0]);
      const rEv = matchProbApp(args[1]);
      if (lEv && rEv) {
        const ln = nameProbEvent(lEv);
        const rn = nameProbEvent(rEv);
        if (name === "LeanDiv") {
          if (ln === "ProbCondJoint" && rn === "ProbCond") return ["DivProbSCond"];
          if (ln === "ProbCond_Joint" && rn === "ProbCond") return ["DivProbSCond"];
          if (ln === "ProbCondJoint" && rn === "ProbCond_Joint") return ["DivProbSCond"];
          if (ln === "ProbS" && rn === "ProbS") return ["DivProbSCond"];
          if (ln === "ProbS" && rn === "Prob") return ["DivProbS"];
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return ["Div" + ln + rn];
        }
        if (name === "LeanMul") {
          if (ln.startsWith("ProbCond") && rn.startsWith("ProbCond")) return ["MulProbCond"];
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return ["Mul" + ln + rn];
        }
      }
    }
    const leftAlts = nameExprAlts(args[0], opts);
    const rightAlts = nameExprAlts(args[1], opts);
    const out = [];
    // same child on both sides first (Plural S: MulProdS), so node caps keep them
    const rightSet = new Set(rightAlts);
    for (const l of leftAlts) {
      if (!l || !rightSet.has(l)) continue;
      const snakePlural = pluralSnakeS(l);
      if (snakePlural) out.push(tag + snakePlural);
      out.push(tag + pluralMidS(l));
      if (pluralLetterS(l)) out.push(tag + pluralLetterS(l));
      out.push(tag + sameChildS(l));
    }
    // TagLeftRight, LeftTagRight, LeftRightTag, etc. — diagonal order so node caps keep the best pairs
    const diag = [];
    for (let i = 0; i < leftAlts.length; i++) for (let j = 0; j < rightAlts.length; j++) diag.push([i + j, i, j]);
    diag.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const [, di, dj] of diag) {
      const l = leftAlts[di], r = rightAlts[dj];
      {
        if (l && r) {
          if (l === r) {
            const snakePlural = pluralSnakeS(l);
            if (snakePlural) out.push(tag + snakePlural);
            out.push(tag + pluralMidS(l));
            if (pluralLetterS(l)) out.push(tag + pluralLetterS(l));
            out.push(tag + sameChildS(l));
          }
          if (joinDigits(l, r) !== l + r) out.push(tag + joinDigits(l, r));
          out.push(tag + l + r);
          out.push(tag + l + "_" + r); // AddMulProd_SumMulProd
        }
      }
    }
    // infix/suffix spellings after all prefix ones, so node caps keep deeper prefix pairs
    for (const [, di, dj] of diag) {
      const l = leftAlts[di], r = rightAlts[dj];
      if (!l || !r) continue;
      out.push(l + tag + r);
      out.push(l + r + tag);
      out.push(l + "_" + tag + "_" + r);
    }
    if (!leftAlts.length && rightAlts.length) {
      for (const r of rightAlts) {
        out.push(tag + "_" + r);
        out.push(tag + r);
      }
    }
    if (leftAlts.length && !rightAlts.length) {
      for (const l of leftAlts) {
        out.push(tag + l);
        out.push(l + tag);
      }
    }
    if (!leftAlts.length && !rightAlts.length) out.push(tag);
    // bare `fun ω ↦ f ω i` operands carry no atom: (fun …) * fun … → Mul
    const bareFun = (n, alts) => cls(unwrapParen(n)) === "Lean_fun" && alts.length === 1 && alts[0] === "Fun";
    if (bareFun(args[0], leftAlts) || bareFun(args[1], rightAlts)) {
      const L = bareFun(args[0], leftAlts) ? [] : leftAlts;
      const R = bareFun(args[1], rightAlts) ? [] : rightAlts;
      if (!L.length && !R.length) out.push(tag);
      for (const r of L.length ? [] : R) out.push(tag + "_" + r, tag + r);
      for (const l of R.length ? [] : L) out.push(tag + l);
    }
    // exponent/base details may be omitted: SummableSquarePow, TendstoSumPow
    if (name === "LeanPow" && (leftAlts.length || rightAlts.length)) out.push(tag);
    return uniq(out);
  }

  if (name === "Lean_bullet") {
    return ["SMul"];
  }

  if (name === "LeanDoubleAngleQuotation") return [];
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return ["Prob"];
  }
  if (name === "LeanBitOr") return [];

  if (Array.isArray(node.args)) {
    const childAlts = node.args.map(a => nameExprAlts(a, opts)).filter(a => a.length);
    if (!childAlts.length) return [];
    // Return first non-empty child alts
    return childAlts[0];
  }
  return [];
}

function classChain(node, out = []) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  if (CLASS_TOKEN[name] || name === "LeanEq" || name === "LeanConstruct" || name === "LeanProperty") out.push(name);
  else if (name === "LeanToken" && node.text && /^[A-Z]/.test(node.text)) out.push("Token:" + node.text);
  if (name === "Lean_exists" || name === "Lean_forall") { classChain(node.args?.[node.args.length - 1], out); return out; }
  if (name === "LeanEq" || name === "Lean_lt" || name === "LeanSub") {
    for (const a of node.args || []) classChain(a, out); return out;
  }
  if (name === "LeanArgsSpaceSeparated") {
    const head = node.args?.[0];
    if (cls(head) === "LeanToken") out.push("Token:" + head.text);
    else if (cls(head) === "LeanProperty") classChain(head, out);
    const last = node.args?.[node.args.length - 1];
    if (cls(last) === "LeanParenthesis") classChain(last.args?.[0], out);
    else if (node.args?.[1]) classChain(node.args[1], out);
    return out;
  }
  if (name === "LeanProperty") {
    const prop = node.args?.[1];
    if (cls(prop) === "LeanToken") out.push("Token:" + prop.text);
    classChain(node.args?.[0], out); return out;
  }
  if (name === "LeanStatements" || name === "LeanArgsNewLineSeparated") { classChain(firstConclusion(node), out); return out; }
  if (name === "LeanParenthesis") { classChain(node.args?.[0], out); return out; }
  if (name === "Lean_lnot" || name === "Lean_fun" || name === "LeanRightarrow") {
    classChain(node.args?.[node.args.length - 1], out); return out;
  }
  if (Array.isArray(node.args)) for (const a of node.args) classChain(a, out);
  return out;
}

function hasMainAttr(lemma) {
  return (lemma.args || []).some((a) => {
    if (cls(a) !== "LeanAttribute") return false;
    const walk = (n) => {
      if (!n || typeof n !== "object") return false;
      if (cls(n) === "LeanToken" && n.text === "main") return true;
      return Array.isArray(n.args) && n.args.some(walk);
    };
    return walk(a);
  });
}

function extractLemmas(ast) { return (ast.args || []).filter((a) => cls(a) === "Lean_lemma"); }
function getLemmaName(lemma) {
  const assign = (lemma.args || []).find((a) => cls(a) === "LeanAssign");
  const colon = assign?.args?.find((a) => cls(a) === "LeanColon");
  const argsNode = colon?.args?.find((a) => cls(a) === "LeanArgsIndented" || cls(a) === "LeanArgsSpaceSeparated");
  const nameToken = argsNode?.args?.find((a) => cls(a) === "LeanToken");
  return nameToken?.text || "";
}
function extractLemma(ast, lemmaName) {
  const lemmas = extractLemmas(ast);
  if (lemmaName) {
    const named = lemmas.find((l) => getLemmaName(l) === lemmaName);
    if (named) return named;
  }
  return lemmas.find(hasMainAttr) || lemmas[0];
}

function findColonDeep(node) {
  if (!node || typeof node !== "object") return null;
  if (cls(node) === "LeanColon") return node;
  if (Array.isArray(node.args)) {
    for (const c of node.args) {
      const r = findColonDeep(c);
      if (r) return r;
    }
  }
  return null;
}

function extractSignature(lemma) {
  const outerAssign = (lemma.args || []).find((a) => cls(a) === "LeanAssign");
  if (!outerAssign) return null;
  let colon = (outerAssign.args || []).find((a) => cls(a) === "LeanColon");
  if (!colon) {
    const wrapped = (outerAssign.args || []).find((a) => cls(a) === "LeanAssign");
    colon = wrapped ? findColonDeep(wrapped) : null;
  }
  if (!colon) return null;
  const indented = (colon.args || []).find((a) => cls(a) === "LeanArgsIndented");
  const implyStmts = (colon.args || []).find((a) => cls(a) === "LeanStatements");
  const nls = (indented?.args || []).find((a) => cls(a) === "LeanArgsNewLineSeparated");
  return { colon, indented, nls, implyStmts };
}

function extractGivens(nls) {
  const args = nls?.args || [];
  let pastGiven = false;
  const hyps = [];
  for (const a of args) {
    if (cls(a) === "LeanLineComment" && /given/i.test(a.text || "")) { pastGiven = true; continue; }
    if (!pastGiven) continue;
    // several binders on one line: `(h : LyapunovCandidate V V') (n : ℕ)`
    const items = cls(a) === "LeanArgsSpaceSeparated" && (a.args || []).every((x) => cls(x) === "LeanParenthesis") ? a.args : [a];
    for (const p of items) {
      if (cls(p) !== "LeanParenthesis") continue;
      const colon = p.args?.[0];
      if (cls(colon) !== "LeanColon") continue;
      const binder = colon.args?.[0];
      const typeNode = colon.args?.[1];
      const names = cls(binder) === "LeanArgsSpaceSeparated" ? (binder.args || []).map((x) => x.text).filter(Boolean) : [binder?.text || ""];
      hyps.push({ name: binder?.text || names[0] || "", names, typeNode, prop: isPropHyp(typeNode) });
    }
  }
  return hyps;
}

/** Prop-like instance binders on term variables, e.g. `[RowStochastic P]` (not `[Fintype S]`). */
function extractInstanceHyps(indented) {
  const termBinders = new Set(); // declared {x : T} with T not a Type/Sort (auto-bound α never qualifies)
  const isTypeSort = (t) => {
    const c = cls(t);
    if (c === "LeanToken") return /^(Type|Sort)/.test(t.text || "");
    if (c === "LeanArgsSpaceSeparated") return isTypeSort(t.args?.[0]);
    if (c === "Lean_rightarrow") return isTypeSort(t.args?.[t.args.length - 1]);
    return false;
  };
  const out = [];
  const walk = (n) => {
    if (!n || typeof n !== "object") return;
    const c = cls(n);
    if (c === "LeanStatements" || c === "LeanParenthesis") return;
    if (c === "LeanBrace") {
      const colon = n.args?.[0];
      if (cls(colon) === "LeanColon" && !isTypeSort(colon.args?.[1])) {
        const b = colon.args?.[0];
        for (const t of cls(b) === "LeanToken" ? [b] : b?.args || []) if (cls(t) === "LeanToken") termBinders.add(t.text);
      }
      return;
    }
    if (c === "LeanBracket") {
      const app = n.args?.[0];
      const head = app?.args?.[0];
      if (cls(app) === "LeanArgsSpaceSeparated" && cls(head) === "LeanToken" && /^[A-Z]/.test(head.text || "")) {
        const xs = app.args.slice(1);
        if (xs.length && xs.every((x) => cls(x) === "LeanToken" && termBinders.has(x.text))) {
          out.push({ name: "[" + head.text + "]", typeNode: app, prop: true });
        }
      }
      return;
    }
    for (const a of n.args || []) walk(a);
  };
  walk(indented);
  return out;
}

/**
 * Proofs do not matter for naming: when lean.js fails on a proof (e.g. `convert … <;> first | rfl | (…)`),
 * retry with the main lemma's proof replaced by `sorry`.
 */
function truncateMainProof(source) {
  const at = source.indexOf("@[main]");
  const imply = source.indexOf("-- imply", at < 0 ? 0 : at);
  if (imply < 0) return source;
  const m = /:=(\s|$)/.exec(source.slice(imply));
  if (!m) return source;
  return source.slice(0, imply + m.index) + ":= by\n  sorry\n";
}
function compileLemmaSource(source) {
  try {
    return compile(source);
  } catch (e) {
    const cut = truncateMainProof(source);
    if (cut === source) throw e;
    return compile(cut);
  }
}

export function suggest(filePath, lemmaName, options = {}) {
  const abs = path.resolve(filePath);
  const source = fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const ast = compileLemmaSource(source);
  const lemma = extractLemma(ast, lemmaName);
  if (!lemma) throw new Error("No Lean_lemma found");
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  for (const r of new Set([sig.indented, sig.nls, sig.implyStmts])) reassociateDotProduct(r);
  const sections = existingSections();
  const picked = pickSection(sig.colon, sections, {
    custom: customSection(sections, sig.implyStmts, extractGivens(sig.nls).filter((h) => h.prop).map((h) => h.typeNode), importSections(source, sections), sig.indented),
    // `import sympy.….vector` → +1.5 for Vector; custom folders (Iterates, …) are decided by customSection only
    imports: [...importSections(source, sections).keys()].filter((s) => DATA_TYPE_SECTIONS.has(s) || TYPE_TO_SECTION[s]),
  });
  const section = picked.section;
  let relCurrent = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
  if (relCurrent.startsWith("..")) relCurrent = path.relative(REPO, abs).replace(/\\/g, "/");
  const leaves = collectLeafBinders(sig.indented);
  collectLeafBinders(sig.implyStmts, leaves, true);
  // receivers used through projections in the conclusion (`w.μ …`), before projections become holes
  const conclNames = new Set();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken") conclNames.add(n.args[0].text);
    for (const a of n.args || []) walk(a);
  })(sig.implyStmts);
  {
    const bundles = bundleVars(sig.indented);
    for (const r of new Set([sig.nls, sig.implyStmts])) holeBundleProjections(r, bundles, leaves);
  }
  const nameOpts = { leaves, typeLeaves: collectTypeBinders(sig.indented), section };
  const implyAltsOf = (sg, no) => {
    const joined = nameExprAlts(sg.implyStmts, no).filter(Boolean);
    const parts = splitTopConjunction(sg.implyStmts);
    if (!parts || parts.length < 2) return joined;
    const perConjunct = parts.map((p) => nameExprAlts(p, no).filter(Boolean));
    if (!perConjunct.every((a) => a.length)) return joined;
    const splitAlts = perConjunct.reduce(
      (acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))),
      [""],
    );
    return uniq([...splitAlts, ...joined]);
  };
  const implyAltsA = implyAltsOf(sig, nameOpts);
  // Canonical rendering (nameExpr) first when it is among the alternatives.
  // (an alternative differing only by the ' between adjacent numbers — Neg1'0 vs Neg10 — is the canonical one)
  const undig = (x) => sanitizeRelPath(x || "").replace(/(\d)'(?=\d)/g, "$1");
  const pickCanon = (alts, preferred) =>
    alts.find((a) => sanitizeRelPath(a) === sanitizeRelPath(preferred || "")) ||
    (preferred ? alts.find((a) => /\d'\d/.test(a) && undig(a) === undig(preferred)) : null) || alts[0] || preferred;
  const implyNameA = pickCanon(implyAltsA, nameExpr(sig.implyStmts, nameOpts)) || "Imply";
  // Second pass keeping Greek / subscript letters and Greek projections (`spec.η`, `maxₐ`, `μmin`).
  const passB = (() => {
    KEEP_GREEK = true;
    try {
      const sigB = extractSignature(extractLemma(compileLemmaSource(source), lemmaName));
      for (const r of new Set([sigB.indented, sigB.nls, sigB.implyStmts])) reassociateDotProduct(r);
      const leavesB = collectLeafBinders(sigB.indented);
      collectLeafBinders(sigB.implyStmts, leavesB, true);
      const bundlesB = bundleVars(sigB.indented);
      for (const r of new Set([sigB.nls, sigB.implyStmts])) holeBundleProjections(r, bundlesB, leavesB);
      const optsB = { leaves: leavesB, typeLeaves: collectTypeBinders(sigB.indented), section };
      const implyAlts = implyAltsOf(sigB, optsB);
      const implyName = pickCanon(implyAlts, nameExpr(sigB.implyStmts, optsB)) || "Imply";
      const givens = extractGivens(sigB.nls).map((h) => ({
        alts: nameExprAlts(h.typeNode, { ...optsB, asGiven: true }).filter(Boolean),
        name: nameExpr(h.typeNode, { ...optsB, asGiven: true }) || "Given",
      }));
      return { implyAlts, implyName, givens };
    } catch {
      return null;
    } finally {
      KEEP_GREEK = false;
    }
  })();
  const implyAlts = uniq([...implyAltsA, ...(passB?.implyAlts || [])]);
  // lowercase ASCII components (`min/…` from a stripped `μmin`) are not names; soft relations are
  const SOFT = /^(of|is|in|sub|eq|ne|lt|gt|le|ge|dvd|ae[A-Za-z]*)$/;
  const lowerComp = (p) => sanitizeRelPath(p || "").split("/").some((c) => /^[a-z]/.test(c) && !SOFT.test(c));
  let preferB = !!passB && passB.implyName !== implyNameA && lowerComp(implyNameA) && !lowerComp(passB.implyName);
  let implyName = preferB ? passB.implyName : implyNameA;
  const implyChain = classChain(sig.implyStmts);
  // Explicit structure values (`(M : HomMarkovChainSpec S)`, used through projections `M.kernel`
  // in the conclusion) are data arguments, not givens; `(μ : Simplex S)` used as a term stays a given.
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken") conclNames.add(n.args[0].text);
    for (const a of n.args || []) walk(a);
  })(sig.implyStmts);
  // Point/data arguments: `(z : EuclideanVec d)` when EuclideanVec also types implicit data binders.
  const dataHeads = new Set();
  (function walk(n, inType) {
    if (!n || typeof n !== "object") return;
    const c = cls(n);
    if (c === "LeanStatements" || c === "LeanBracket") return;
    if (c === "LeanBrace" && cls(n.args?.[0]) === "LeanColon") { walk(n.args[0].args?.[1], true); return; }
    if (inType && c === "LeanToken" && /^[A-Z]/.test(n.text || "")) dataHeads.add(n.text);
    if (inType && c === "LeanArgsSpaceSeparated") { walk(n.args?.[0], true); return; }
    if (c === "LeanParenthesis" && cls(n.args?.[0]) === "LeanColon" && !inType) {
      const ty = n.args[0].args?.[1];
      if (cls(ty) === "Lean_rightarrow") walk(ty, true);
      return;
    }
    for (const a of n.args || []) walk(a, inType);
  })(sig.indented, false);
  const conclTokenSet = new Set();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanToken") conclTokenSet.add(n.text);
    for (const a of n.args || []) walk(a);
  })(sig.implyStmts);
  const typeHead = (t) => {
    let h = unwrapParen(t);
    if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
    return cls(h) === "LeanToken" ? h.text : "";
  };
  const hyps = extractGivens(sig.nls).map((h, idx) => {
    h = { ...h, idx };
    const t = unwrapParen(h.typeNode);
    const structLike = cls(t) === "LeanToken" || (cls(t) === "LeanArgsSpaceSeparated" && cls(t.args?.[0]) === "LeanToken");
    const usedInConcl = (h.names || [h.name]).some((n) => conclTokenSet.has(n));
    if (h.prop && structLike && conclNames.has(h.name)) return { ...h, prop: false };
    if (h.prop && structLike && dataHeads.has(typeHead(t))) return { ...h, prop: false };
    // `(w : EuclideanVec d)` used in the conclusion: EuclideanVec is a type abbreviation, so w is a value
    // (kept as an optional given: ActorBox/Dist/le/Dist/of/EuclideanVec spells it)
    if (h.prop && structLike && sympyDecls().typeAbbrevs.has(typeHead(t)) && usedInConcl) return { ...h, optional: true, canonSkip: true };
    // `(μ : Measure Ω)` passed to the conclusion: a data argument (Random/Quantile/sub/QuantileLower);
    // a repo structure passed whole (`hMix : UniformExponentialMixing …`) may still be listed
    if (h.prop && structLike && usedInConcl && (TYPE_TO_SECTION[typeHead(t)] === typeHead(t) || typeHead(t) === "Measure")) return { ...h, optional: true, canonSkip: true };
    if (h.prop && structLike && usedInConcl && sympyDecls().structs.has(typeHead(t))) return { ...h, optional: true };
    // integrability side conditions may be left out of Random/ expectation names (Random/LeExpect/of/Le)
    if (h.prop && section === "Random") {
      let b = t;
      while (cls(b) === "Lean_forall") b = unwrapParen(b.args?.[b.args.length - 1]);
      if (typeHead(b) === "Integrable") return { ...h, optional: true };
    }
    return h;
  });
  // Generate ALL given name alternatives (reverse order for path); pass-B (Greek) renderings appended
  const givenAltLists = [...hyps.filter((h) => h.prop)].reverse().map((h) => {
    const b = passB?.givens?.[h.idx];
    const altsA = nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean);
    const nameA = nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given";
    return {
      binder: h.name,
      optional: !!h.optional,
      canonSkip: !!h.canonSkip,
      alts: uniq([...altsA, ...(b?.alts || [])]),
      name: nameA,
      nameB: b ? pickCanon(b.alts, b.name) : null,
      chain: classChain(h.typeNode),
    };
  });
  const instAltLists = extractInstanceHyps(sig.indented).reverse().map((h) => ({
    binder: h.name,
    alts: nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean),
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given",
    chain: classChain(h.typeNode),
  }));
  // Instance hyps precede the `-- given` block, so in (reverse-order) paths they come last.
  // Canonical: explicit givens only; instance hyps only when there are no explicit givens.
  const canonGivenLists = givenAltLists.filter((g) => !g.canonSkip); // instance hyps are optional, never canonical
  let givenNames = canonGivenLists.map((g) => ({ binder: g.binder, name: pickCanon(g.alts, g.name), chain: g.chain }));
  if (preferB) givenNames = canonGivenLists.map((g) => ({ binder: g.binder, name: g.nameB || pickCanon(g.alts, g.name), chain: g.chain }));
  // Cartesian product of given alternatives
  // Cartesian product of given alternatives, capped (full products reach millions of paths).
  const GIVEN_PATH_CAP = 2000;
  function cartGiven(lists) {
    let acc = [""];
    for (const g of lists) {
      const next = [];
      outer: for (const p of acc) {
        for (const a of [...(g.alts.length ? g.alts : ["Given"]), ...(g.optional ? [""] : [])]) {
          next.push(p && a ? p + "/" + a : p || a);
          if (next.length >= GIVEN_PATH_CAP) break outer;
        }
      }
      acc = next;
    }
    return acc;
  }
  const givenPaths = [...new Set([
    ...cartGiven(givenAltLists),
    ...(instAltLists.length && instAltLists.length <= 3 ? cartGiven([...givenAltLists, ...instAltLists]) : []),
  ])];
  // Displayed suggestions: capped product; membership is decided by altMatch below.
  const PATH_CAP = 20000;
  const shownImply = implyAlts.slice(0, 200);
  const shownGiven = givenPaths.slice(0, Math.max(1, Math.floor(PATH_CAP / Math.max(1, shownImply.length))));
  // non-ASCII (Greek / subscript) components are allowed, as in the repo (QLearningSpec/AbsSubMaxₐ);
  // invalid module components are filtered below
  const allPaths = uniq(
    shownImply.flatMap((implyAlt) =>
      shownGiven.map((givenPath) => {
        const implyPath = sanitizeRelPath(implyAlt);
        const gp = givenPath ? sanitizeRelPath(givenPath) : "";
        const body = gp
          ? section + "/" + implyPath + "/of/" + gp + ".lean"
          : section + "/" + implyPath + ".lean";
        return body.replace(/\\/g, "/");
      }),
    ),
  ).filter((p) => !/\[anonymous\]|anonymous/i.test(p));
  // Membership without enumerating: section / imply alt / given alts in order (+ ≤3 instance hyps).
  const altSet = (alts) => new Set(alts.map((a) => sanitizeRelPath(a)));
  const implySet = altSet(implyAlts);
  const gSets = givenAltLists.map((g) => { const s = g.alts.length ? altSet(g.alts) : new Set(["Given"]); if (g.optional) s.__optional = true; return s; });
  const iSets = instAltLists.length && instAltLists.length <= 3
    ? instAltLists.map((g) => (g.alts.length ? altSet(g.alts) : new Set(["Given"])))
    : null;
  // No section evidence at all (generic typeclass lemma, no ℕ/ℤ/ℝ/Set token): Nat is only the repo-majority
  // default (113 such files live there), so any data-type section is accepted for consistency.
  const sectionFree = picked.score === 0;
  // Hyperreal evidence that is only casts of real variables (`(a : ℝ*) ≤ (b : ℝ*) ↔ a ≤ b`, a b : ℝ):
  // the repo files such lemmas under Real as well (Real/LeCoeS/is/Le next to Hyperreal/GtCoe_0/is/Gt_0)
  const altSections = new Set();
  if (section === "Hyperreal" && sections.includes("Real")) {
    let casts = 0;
    const outside = (n) => {
      if (!n || typeof n !== "object") return 0;
      if (cls(n) === "LeanToken") return n.text === "ℝ*" ? 1 : 0;
      if (isCoeAscription(n)) { casts++; return outside(n.args[0]); }
      return (n.args || []).reduce((a, c) => a + outside(c), 0);
    };
    let bad = outside(sig.implyStmts);
    (function walk(n) {
      if (!n || typeof n !== "object") return;
      if ((cls(n) === "LeanBrace" || cls(n) === "LeanParenthesis") && cls(n.args?.[0]) === "LeanColon") { bad += outside(n.args[0].args?.[1]); return; }
      for (const a of n.args || []) walk(a);
    })(sig.indented);
    if (casts && !bad) altSections.add("Real");
  }
  function altMatch(p) {
    const cur = String(p).replace(/\\/g, "/").replace(/^Lemma\//, "").replace(/\.lean$/, "");
    if (/anonymous/i.test(cur)) return false;
    const curSec = cur.split("/")[0];
    if (curSec !== section && !altSections.has(curSec) && !(sectionFree && DATA_TYPE_SECTIONS.has(curSec) && sections.includes(curSec))) return false;
    const rest = cur.slice(curSec.length + 1);
    const matchGivens = (str, sets) => {
      const go = (i, s) => {
        if (i === sets.length) return s === "";
        if (sets[i].__optional && go(i + 1, s)) return true;
        for (const a of sets[i]) {
          if (s === a && go(i + 1, "")) return true;
          if (s.startsWith(a + "/") && go(i + 1, s.slice(a.length + 1))) return true;
        }
        return false;
      };
      return go(0, str);
    };
    if (gSets.every((s) => s.__optional) && implySet.has(rest)) return true;
    for (let i = rest.indexOf("/of/"); i >= 0; i = rest.indexOf("/of/", i + 1)) {
      if (!implySet.has(rest.slice(0, i))) continue;
      const g = rest.slice(i + 4);
      if (gSets.length && matchGivens(g, gSets)) return true;
      if (iSets && matchGivens(g, [...gSets, ...iSets])) return true;
    }
    return false;
  }
  const buildRel = (iname, gnames) => {
    const ip = sanitizeRelPath(iname);
    const gp = gnames.map((g) => sanitizeRelPath(g.name)).join("/");
    return sanitizeRelPath(gp ? section + "/" + ip + "/of/" + gp + ".lean" : section + "/" + ip + ".lean");
  };
  let relPath = buildRel(implyName, givenNames);
  // the plain rendering is already another lemma's path (sibling collision): take the Greek-keeping one
  if (passB && !preferB) {
    const givenNamesB = canonGivenLists.map((g) => ({ binder: g.binder, name: g.nameB || pickCanon(g.alts, g.name), chain: g.chain }));
    const relB = buildRel(passB.implyName, givenNamesB);
    const cur = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
    if (relB !== relPath && cur !== relPath && fs.existsSync(path.join(LEMMA_ROOT, relPath))) {
      preferB = true;
      implyName = passB.implyName;
      givenNames = givenNamesB;
      relPath = relB;
    }
  }
  const implyPath = sanitizeRelPath(implyName);
  if (!allPaths.includes(relPath) && altMatch(relPath)) allPaths.push(relPath);
  // Canonical first, then shortest — unless the canonical rendering is overlong (Windows MAX_PATH).
  const tooLong = (p) => ("Lemma/" + p).length > PATH_WARN_LEN;
  const preferCanon = true;
  const sorted = allPaths.sort((a, b) => (preferCanon ? (b === relPath) - (a === relPath) : 0) || byBestToWorst(a, b));
  // every component must be a valid Lean module-name component (no leading digit, identifier characters)
  const validSorted = sorted.filter(validModulePath);
  const suggestions = validSorted.length ? validSorted : sorted;
  const moduleName = relPath.replace(/\.lean$/, "").split(/[/\\]/).join(".");
  const suggestedPath = suggestions[0] || relPath.replace(/\\/g, "/");
  const result = {
    file: abs,
    currentPath: relCurrent.startsWith("Lemma/") ? relCurrent.slice(6) : relCurrent,
    suggestedPath,
    suggestions,
    moduleName,
    section,
    sectionScore: picked.score,
    sectionTokens: picked.tokens,
    imply: { name: implyPath, chain: implyChain },
    givensLeanOrder: hyps.map((h) => ({ binder: h.name, prop: h.prop, name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) })),
    givensPathOrder: givenNames,
    warnings: [],
  };
  if (sectionFree) result.warnings.push(`no section evidence (no data-type token): ${section} is the repo default for generic lemmas; Int/Real/Set/… are accepted too`);
  if (validSorted.length && validSorted.length < sorted.length) result.warnings.push(`${sorted.length - validSorted.length} alternative(s) dropped: not valid Lean module names`);
  if (!validModulePath(suggestedPath)) result.warnings.push("suggested path has a component that is not a valid Lean module name: " + suggestedPath.replace(/\.lean$/, "").split("/").filter((c) => !validModuleComponent(c)).join(", "));
  if (tooLong(suggestedPath)) {
    result.warnings.push(`suggested path is ${("Lemma/" + suggestedPath).length} chars (> ${PATH_WARN_LEN}); ` +
      "with build prefixes it may exceed Windows MAX_PATH (260) — consider shortening" +
      (suggestions.length > 1 ? `; shortest alternative (${("Lemma/" + [...suggestions].sort(byBestToWorst)[0]).length} chars): Lemma/${[...suggestions].sort(byBestToWorst)[0]}` : ""));
  }
  const matchedSuggestion = altMatch(result.currentPath)
    ? result.currentPath
    : suggestions.find((s) => pathsConsistent(result.currentPath, s).ok);
  result.consistent = matchedSuggestion
    ? { ok: true, reason: "exact match", existing: result.currentPath, suggested: matchedSuggestion }
    : pathsConsistent(result.currentPath, result.suggestedPath);
  // Py-name mode: ported lemmas keep their py module name (the /py summary pairs Lean and py module names).
  // `options.py` = "Section/Name/…" (explicit) or true (auto: pyLink/Lemma/<current>.py exists).
  const curMod = result.currentPath.replace(/\.lean$/, "");
  const pyCounterpart = pyModuleExists(curMod);
  if (pyCounterpart) result.pyCounterpart = curMod;
  if (options.py) {
    const explicit = typeof options.py === "string" && options.py !== "auto";
    const pyName = explicit ? String(options.py).replace(/\\/g, "/").replace(/^Lemma\//, "").replace(/\.(lean|py)$/, "").replace(/\./g, "/") : pyCounterpart ? curMod : null;
    result.py = { name: pyName, source: explicit ? "flag" : "pyLink", derived: { suggestedPath: result.suggestedPath, consistent: result.consistent } };
    if (pyName && pyName === curMod) result.consistent = { ok: true, reason: "py name", existing: result.currentPath, suggested: pyName + ".lean" };
    else if (pyName) result.consistent = { ok: false, reason: "py name mismatch: expected " + pyName, existing: result.currentPath, suggested: pyName + ".lean" };
  }
  return result;
}

/** `pyLink` is the py repository (served at localhost:8080/py); `pyLink/Lemma/<A>/<B>.py` mirrors `Lemma/<A>/<B>.lean`. */
function pyModuleExists(mod) {
  const base = path.join(REPO, "pyLink", "Lemma", ...String(mod).split("/"));
  try { return fs.existsSync(base + ".py") || fs.existsSync(path.join(base, "__init__.py")); } catch { return false; }
}

/**
 * Is `existing` lemma path consistent with `suggested`?
 * Strict exact-match: the current path must be literally generated by the algorithm.
 * Returns { ok, reason, existing, suggested }.
 */
export function pathsConsistent(existing, suggested) {
  const norm = (p) =>
    String(p)
      .replace(/\\/g, "/")
      .replace(/^Lemma\//, "")
      .replace(/\.lean$/, "");
  const a = norm(existing);
  const b = norm(suggested);
  if (a === b) {
    return { ok: true, reason: "exact match", existing: a, suggested: b };
  }
  const aSegs = a.split("/").filter(Boolean);
  const bSegs = b.split("/").filter(Boolean);
  if (aSegs.length === 0 || bSegs.length === 0) {
    return { ok: false, reason: "empty path", existing: aSegs, suggested: bSegs };
  }
  if (aSegs[0] !== bSegs[0]) {
    return { ok: false, reason: "section mismatch: " + aSegs[0] + " vs " + bSegs[0], existing: aSegs, suggested: bSegs };
  }
  return { ok: false, reason: "path mismatch", existing: aSegs, suggested: bSegs };
}

/** Paths longer than this ("Lemma/…​.lean") are flagged; build prefixes push them past MAX_PATH. */
const PATH_WARN_LEN = 150;

/** Best = shortest ASCII bytes; worst = longest (redundant). Tie-break lexicographic. */
function byBestToWorst(a, b) {
  const ba = Buffer.byteLength(a, "utf8");
  const bb = Buffer.byteLength(b, "utf8");
  if (ba !== bb) return ba - bb;
  return a < b ? -1 : a > b ? 1 : 0;
}

function printHuman(r) {
  console.log("current:    Lemma/" + r.currentPath);
  for (const w of r.warnings || []) console.log("warning:    " + w);
  {
    const chk = r.consistent || pathsConsistent(r.currentPath, r.suggestedPath);
    console.log("consistent: " + (chk.ok ? "yes" : "no") + (chk.ok ? "" : " (" + chk.reason + ")"));
  }
  if (r.py) console.log("py name:    " + (r.py.name ? "Lemma/" + r.py.name + " (" + r.py.source + ")" : "— (no py counterpart)") + "; derived: Lemma/" + r.py.derived.suggestedPath + (r.py.derived.consistent.ok ? " (consistent)" : ""));
  else if (r.pyCounterpart) console.log("py:         pyLink/Lemma/" + r.pyCounterpart + ".py exists (use --py to keep the py name)");
  console.log("section:    " + r.section + " (score " + r.sectionScore + "; tokens: " + (r.sectionTokens.join(", ") || "—") + ")");
  console.log("suggestions (" + r.suggestions.length + ", best→worst by ASCII bytes):");
  for (const s of r.suggestions) {
    console.log("  - Lemma/" + s + "  [" + Buffer.byteLength(s, "utf8") + " B]" + (("Lemma/" + s).length > PATH_WARN_LEN ? "  ⚠ long" : ""));
  }
  console.log("imply:      " + r.imply.name);
  console.log("  chain:    " + r.imply.chain.join(" → "));
  console.log("givens (Lean order → path uses reverse):");
  for (const g of r.givensLeanOrder) console.log("  " + (g.prop ? "✓" : "·") + " " + g.binder + ": " + (g.name || "(skip)"));
  console.log("givens (path order):");
  for (const g of r.givensPathOrder) console.log("  " + g.name + "   [" + g.chain.join(" → ") + "]");
}

function cli() {
  const argv = process.argv.slice(2);
  const json = argv.includes("--json");
  const lemmaIdx = argv.indexOf("--lemma");
  const lemmaName = lemmaIdx >= 0 ? argv[lemmaIdx + 1] : null;
  // --py <Section/Name/…> keeps that py module name; bare --py (or --py=auto) uses pyLink/Lemma/<current>.py
  let py = null;
  const pyEq = argv.find((a) => a.startsWith("--py="));
  const pyIdx = argv.indexOf("--py");
  if (pyEq) py = pyEq.slice(5) || true;
  else if (pyIdx >= 0) {
    const v = argv[pyIdx + 1];
    py = v && !v.startsWith("-") && !/\.lean$/.test(v) ? v : true;
  }
  const pyVal = typeof py === "string" ? py : null;
  const file = argv.find((a) => !a.startsWith("-") && a !== lemmaName && a !== pyVal);
  if (!file) {
    console.error("Usage: node mjs/lemmaPath.mjs [--json] [--lemma <name>] [--py [<Section/Name/…>]] <path-to.lean>");
    process.exit(1);
  }
  try {
    const result = suggest(file, lemmaName, { py });
    if (json) console.log(JSON.stringify(result, null, 2));
    else printHuman(result);
  } catch (e) {
    console.error(e.message || e);
    process.exit(1);
  }
}

const isMain =
  process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;
if (isMain) cli();
