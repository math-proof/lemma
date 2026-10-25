
import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import { compile } from "../js/parser/lean.js";
import { strStmt } from "../js/parser/lean/utility.js";
import { loadSectionKindMap } from "./lemmaSectionKind.mjs";

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
  // Type classes are not sections (AGENTS.md): additive/ring algebra → Int (data type).
  AddCommGroup: "Int",
  AddGroup: "Int",
  Ring: "Int",
  CommRing: "Int",
  LinearOrderedAddCommGroup: "Int",
  Rat: "Rat",
  "ℚ": "Rat",
  Fin: "Fin",
  Finset: "Finset",
  Multiset: "Multiset",
  Finsupp: "Finsupp",
  CurveDivisor: "Finsupp", // abbrev CurveDivisor := C →₀ ℤ (→ blocks abbrevHeads)
  List: "List",
  Set: "Set",
  Filter: "Filter",
  Matrix: "Matrix",
  Tensor: "Tensor",
  Vector: "Vector",
  Polynomial: "Polynomial",
  MvPolynomial: "MvPolynomial",
  LaurentPolynomial: "LaurentPolynomial",
  PowerSeries: "PowerSeries",
  MvPowerSeries: "MvPowerSeries",
  Ideal: "Ideal",
  // PiLp-based sequence spaces live with Matrix in this repository.
  l1Space: "Matrix",
  L1Space: "Matrix",
  l2Space: "Matrix",
  lpSpace: "Matrix",
  WithLp: "Matrix",
  PiLp: "Matrix",
  EuclideanSpace: "Matrix", // EuclideanSpace ℝ ι = PiLp 2 (ι → ℝ)
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

/** sympy/<dir>/… modules whose data structures belong to a data-type section. */
const SYMPY_DIR_SECTION = { stats: "Random", matrices: "Matrix", tensor: "Tensor", sets: "Set" };
/** Weight of a binder typed by a repo data structure (`{M : Model Θ S A}` from sympy.stats.policy_trajectory):
 *  beats incidental `γ ∈ Set.Ico 0 1` (Set 3) and typeclass / scalar evidence. */
const STRUCT_BINDER_WEIGHT = 4;

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
  Lean_notin: "NotIn", // y ∉ X → NotIn (of/…/NotIn/…; keep in De Bruijn reverse of-tail)
  LeanInf: "Inf",
  Lean_cdotp: "Dot", // x ⬝ᵥ y → Dot (FiniteMRP/DotVecMul_D)
  LeanMatMul: "Dot", // A @ x (Dot.dot) → Dot (Random/ExpectDot/eq/DotExpect, Random/ExpectCondDot/eq/DotExpectCond)
  Lean_subseteq: "Subset", // A ⊆ B → A/sub/B, Subset_B (Real/AbsorbingSet/sub/PhaseSpace, Random/Quantile/sub/QuantileLower)
};

function cls(n) { return n?.constructor?.name || ""; }

/** Head of the (co)domain of a type text: `Matrix S S ℝ` → Matrix, `S × A → ProbabilityMeasure S` → ProbabilityMeasure. */
function codomainHead(text) {
  let t = String(text || "").replace(/--.*$/, "").replace(/\s*(:=|\bwhere\b)[\s\S]*$/, "").trim();
  let depth = 0, cut = 0;
  for (let i = 0; i < t.length; i++) {
    const c = t[i];
    if ("([{⟨".includes(c)) depth++;
    else if (")]}⟩".includes(c)) depth--;
    else if (c === "→" && depth === 0) cut = i + 1;
  }
  t = t.slice(cut).trim();
  const m = /^\(*\s*([A-Za-zℝℕℤℚℂ][\w.']*)/u.exec(t);
  return m ? m[1] : null;
}
/** Type head of a declaration header `def P (x : T) : Matrix S S ℝ` (after its last top-level `:`). */
function declTypeHead(hd) {
  let depth = 0, cut = -1;
  for (let i = 0; i < hd.length; i++) {
    const c = hd[i];
    if ("([{⟨".includes(c)) depth++;
    else if (")]}⟩".includes(c)) depth--;
    else if (c === ":" && depth === 0 && hd[i + 1] !== "=") cut = i + 1;
  }
  return cut < 0 ? null : codomainHead(hd.slice(cut));
}

/** Declarations of the repo's sympy/**.lean modules: structure fields and type abbreviations. */
let SYMPY_DECLS = null;
function sympyDecls() {
  if (SYMPY_DECLS) return SYMPY_DECLS;
  const structs = new Map(); // structure → Map(field → type head)
  const structInfo = new Map(); // structure → { module: ["stats", "policy_trajectory"], ns: ["PolicyGradient"], prop }
  const typeAbbrevs = new Set(); // `abbrev EuclideanVec (d : ℕ) := EuclideanSpace ℝ (Fin d)` (not set-builder / Prop)
  const abbrevHeads = new Map(); // EuclideanVec → EuclideanSpace, LpSpace → PiLp (head of a non-product right-hand side)
  const propDecls = new Set(); // `class Iterates … : Prop where`, `structure SolvesStateEquation … : Prop where`, `def … : Prop :=`
  const dataDecls = new Set(); // `structure Skeleton … where`, `inductive Hist …`, type abbreviations: values of these are data
  const valueDefs = new Set(); // `def actor_box … : Set …` → ActorBox: a value / function, not a type
  const members = new Map(); // structure → Map(field / namespace def → head of its (co)domain type): FiniteMRP.D → Matrix
  const parents = new Map(); // structure → parent structure (`extends MDPSpec S A`)
  const nsDefsRaw = []; // [namespace, def, type head] resolved against the structures after the scan
  const scan = (text, module = []) => {
    const lines = text.replace(/\r\n/g, "\n").split("\n");
    const ns = [];
    for (let i = 0; i < lines.length; i++) {
      // declaration kinds: Prop predicates / value definitions / data types (header up to `where` / `:=`)
      const dm = /^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(class|structure|def|abbrev|inductive)\s+([^\s({\[:]+)/.exec(lines[i]);
      if (dm) {
        let hd = lines[i];
        for (let j = i + 1; j < Math.min(lines.length, i + 8) && !/(:=|\bwhere\b|\|)/.test(hd); j++) hd += " " + lines[j].trim();
        hd = hd.replace(/(:=|\bwhere\b)[\s\S]*$/, " $1");
        const nm = dm[2].includes(".") ? "" : dm[2];
        if (nm && dm[1] !== "inductive" && /:\s*Prop\s*(?:extends\b[^:]*)?(?::=|where)\s*$/.test(hd)) propDecls.add(nm);
        else if (nm && (dm[1] === "structure" || dm[1] === "inductive" || (dm[1] === "class" && /^[A-Z]/.test(nm)))) dataDecls.add(nm);
        else if (nm && dm[1] === "def" && /^[a-z]/.test(nm)) valueDefs.add(nm.split("_").map((x) => x.charAt(0).toUpperCase() + x.slice(1)).join(""));
        if (nm && dm[1] === "def" && ns.length) { const th = declTypeHead(hd.replace(/\s*(:=|\bwhere\b)\s*$/, "")); if (th) nsDefsRaw.push([ns[ns.length - 1], nm, th]); }
      }
      const nsm = /^namespace\s+(\S+)/.exec(lines[i]);
      if (nsm) { ns.push(nsm[1]); continue; }
      const endm = /^end\s+(\S+)/.exec(lines[i]);
      if (endm && ns.length && ns[ns.length - 1] === endm[1]) { ns.pop(); continue; }
      const ab = /^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?abbrev\s+([^\s({\[:]+)(.*)$/.exec(lines[i]);
      if (ab) {
        const k = ab[2].indexOf(":=");
        let rhs = k >= 0 ? ab[2].slice(k + 2).trim() : "";
        if (k >= 0 && !rhs) rhs = (lines[i + 1] || "").trim();
        const head = k >= 0 ? ab[2].slice(0, k) : ab[2];
        if (rhs && !/^[{]|^Set\b/.test(rhs) && !/:\s*Prop\s*$/.test(head.trim())) {
          typeAbbrevs.add(ab[1]);
          dataDecls.add(ab[1]);
          const hm = /^([A-Z][\w.]*)/.exec(rhs);
          if (hm && !/[×⊕→]/.test(rhs)) abbrevHeads.set(ab[1], hm[1]);
        }
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
        const ft = /^\s{2}([^\s:()]+(?:\s+[^\s:()]+)*)\s*:\s*(.+)$/.exec(l);
        if (ft) { const h = codomainHead(ft[2]); if (h) { if (!members.has(st[1])) members.set(st[1], new Map()); for (const nm of ft[1].split(/\s+/)) if (nm) members.get(st[1]).set(nm, h); } }
        if (f) for (const nm of f[1].split(/\s+/)) fields.set(nm, f[2].replace(/[()]/g, ""));
      }
      structs.set(st[1], fields);
      const ext = /\bextends\s+([A-Z][\w.]*)/.exec(header);
      if (ext) parents.set(st[1], ext[1]);
      structInfo.set(st[1], { module, ns: ns.flatMap((x) => x.split(".")), prop: /:\s*Prop\s*(?:extends|where)\b/.test(header) });
    }
  };
  const walk = (d) => {
    let es = [];
    try { es = fs.readdirSync(d, { withFileTypes: true }); } catch { return; }
    for (const e of es) {
      const q = path.join(d, e.name);
      if (e.isDirectory()) walk(q);
      else if (q.endsWith(".lean")) { try { scan(fs.readFileSync(q, "utf8"), path.relative(path.join(REPO, "sympy"), q).replace(/\.lean$/, "").split(path.sep)); } catch {} }
    }
  };
  walk(path.join(REPO, "sympy"));
  for (const [nsName, nm, th] of nsDefsRaw) {
    if (!structs.has(nsName)) continue;
    if (!members.has(nsName)) members.set(nsName, new Map());
    if (!members.get(nsName).has(nm)) members.get(nsName).set(nm, th);
  }
  SYMPY_DECLS = { structs, structInfo, typeAbbrevs, abbrevHeads, propDecls, dataDecls, valueDefs, members, parents };
  return SYMPY_DECLS;
}

/**
 * Section of a repo data structure (not a Prop structure, not a Lemma folder of its own — those are
 * custom sections): its namespace names a section (`namespace Kernel`), else the sympy module directory
 * does (`sympy/stats/policy_trajectory.lean` ∋ `structure Model` → Random). null otherwise.
 */
let LEMMA_FOLDERS = null;
function lemmaFolders() {
  if (!LEMMA_FOLDERS) { try { LEMMA_FOLDERS = fs.readdirSync(LEMMA_ROOT, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name); } catch { LEMMA_FOLDERS = []; } }
  return LEMMA_FOLDERS;
}
function structSection(name, sections = lemmaFolders()) {
  const info = sympyDecls().structInfo.get(name);
  if (!info || info.prop) return null;
  if (sections.includes(name) || sections.some((s) => !DATA_TYPE_SECTIONS.has(s) && name.startsWith(s) && /[A-Z]/.test(name.charAt(s.length)))) return null;
  // a bundle of section data (`kernel : Kernel S S`, `init : ProbabilityMeasure S`: HomMarkovChainSpec) is read
  // through its projections (M.kernel → Kernel); only a notion built from repo structures / functions
  // (`env : Env S A`, `pol : Policy Θ S A`: Model) is placed by its namespace / module
  const SCALAR = new Set(["Real", "Nat", "Int", "Rat", "Complex"]);
  for (const ty of sympyDecls().structs.get(name)?.values() || []) { const sec = TYPE_TO_SECTION[ty]; if (sec && !SCALAR.has(sec)) return null; }
  for (const n of [...info.ns].reverse()) if (DATA_TYPE_SECTIONS.has(n) && sections.includes(n)) return n;
  for (const d of info.module.slice(0, -1)) if (SYMPY_DIR_SECTION[d]) return SYMPY_DIR_SECTION[d];
  return null;
}

/**
 * Sections are data types. A Lemma folder named after a repo Prop predicate (`structure SolvesStateEquation … : Prop`,
 * `class GeneratorMatrix … : Prop`, `class Iterates … : Prop`) or after a value definition (`def actor_box … : Set …`,
 * `def absorbing_set`) is no data type: it never becomes a custom section, its name is only a hypothesis /
 * conclusion token. Files still filed under such a folder stay accepted there (see `legacySection` in suggest).
 */
function nonDataFolder(name) {
  const { propDecls, dataDecls, valueDefs } = sympyDecls();
  if (DATA_TYPE_SECTIONS.has(name) || TYPE_TO_SECTION[name] || dataDecls.has(name)) return false;
  return propDecls.has(name) || valueDefs.has(name);
}

/** Declared (co)domain head of a structure member (field or namespace def), through `extends`. */
function memberType(T, f, k = 0) {
  const { members, parents } = sympyDecls();
  const t = members.get(T)?.get(f);
  if (t) return t;
  const p = parents.get(T);
  return p && k < 4 ? memberType(p, f, k + 1) : null;
}

/** Section of a repo type abbreviation through its head: EuclideanVec → EuclideanSpace → Matrix. */
function abbrevSection(name) {
  const { abbrevHeads } = sympyDecls();
  for (let t = name, k = 0; t && k < 5; k++) {
    if (TYPE_TO_SECTION[t]) return TYPE_TO_SECTION[t];
    t = abbrevHeads.get(t);
  }
  return null;
}

/** Binder types that are repo data structures with a section: `{M : Model Θ S A}` → Map(Model → Random). */
const STRUCT_BINDER_CACHE = new WeakMap();
function structBinderTypes(node) {
  if (node && typeof node === "object" && STRUCT_BINDER_CACHE.has(node)) return STRUCT_BINDER_CACHE.get(node);
  const out = new Map();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    const c = cls(n);
    if ((c === "LeanBrace" || c === "LeanParenthesis") && cls(n.args?.[0]) === "LeanColon") {
      let h = n.args[0].args?.[1];
      if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
      if (cls(h) === "LeanToken") { const sec = structSection(h.text); if (sec) out.set(h.text, sec); }
    }
    for (const a of n.args || []) walk(a);
  })(node);
  if (node && typeof node === "object") STRUCT_BINDER_CACHE.set(node, out);
  return out;
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
/**
 * Policy-gradient trajectory sample space `ℕ → ℝ × S × A` (expanded form of `Ω` for
 * `PolicyGradient.Model`), possibly parenthesized. `ℝ` here is a coordinate of the path, not a Real-section cue.
 */
function isTrajectorySampleSpace(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_rightarrow" || (u.args || []).length !== 2) return false;
  const left = unwrapParen(u.args[0]);
  if (!(cls(left) === "LeanToken" && (left.text === "ℕ" || left.text === "Nat"))) return false;
  const right = unwrapParen(u.args[1]);
  if (cls(right) !== "Lean_times") return false;
  // product must involve ℝ (reward coordinate): ℝ × S × A
  let hasReal = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || hasReal) return;
    if (cls(n) === "LeanToken" && (n.text === "ℝ" || n.text === "Real")) hasReal = true;
    for (const a of n.args || []) walk(a);
  })(right);
  return hasReal;
}

/** Domain of an RV arrow: bare `Ω` / `Omega`, or the expanded trajectory `ℕ → ℝ × S × A`. */
function isSampleSpaceDomain(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanToken" && (u.text === "Ω" || u.text === "Omega")) return true;
  return isTrajectorySampleSpace(u);
}

function hasRandomAstCues(node) {
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "Lean_rightarrow") {
      // Convention: sample-space RVs are binders {x : Ω → α} or {a : ℕ → (ℕ → ℝ × S × A) → A}.
      if (isSampleSpaceDomain(n.args?.[0])) {
        found = true;
        return;
      }
    }
    if (cls(n) === "LeanToken") {
      const t = n.text;
      // a binder typed by a data structure of the Random section (PolicyGradient.Model, the trajectory law)
      if (structBinderTypes(node).get(t) === "Random") { found = true; return; }
      if (
        t === "PSpace" ||
        t === "ProbabilityMeasure" ||
        t === "IsProbabilityMeasure" ||
        t === "𝔼"
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

/**
 * Strong Random signal: a random-variable binder (x : … → Ω → X, a function out of the sample space)
 * together with probability structure: ℙ / 𝔼 notation, an observed-value «x.bvar» binder or a PSpace instance.
 */
function hasRandomVariableCues(node) {
  let rv = false;
  let prob = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || (rv && prob)) return;
    if (cls(n) === "Lean_rightarrow") {
      if (isSampleSpaceDomain(n.args?.[0])) rv = true;
    }
    if (cls(n) === "LeanToken" && typeof n.text === "string") {
      const t = n.text;
      // a Random data structure binder (PolicyGradient.Model, the trajectory law) stands in for Ω → · binders
      if (structBinderTypes(node).get(t) === "Random") rv = true;
      if (t === "ℙ" || t === "𝔼" || /PSpace$/.test(t) || /\.bvar$/.test(t)) prob = true;
    }
    if (Array.isArray(n.args)) for (const c of n.args) walk(c);
  };
  walk(node);
  return rv && prob;
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
 * Section tokens with a position weight: 0 in a function domain (`ℕ → ℝ` / `ℕ ⇀ ℂ` indices),
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
      // a constant of a repo data structure's namespace (`QLearningSpec.maxₐ`, sympy/stats) → its section
      else if (structSection(ns)) put("st:" + ns, w);
    }
  }
  // `QLearningSpec.maxₐ` parses as a projection of the structure name: a namespace constant of a repo data structure
  if (c === "LeanProperty" && cls(node.args?.[0]) === "LeanToken" && /^[A-Z]/.test(node.args[0].text || "") && structSection(node.args[0].text)) put("st:" + node.args[0].text, w);
  if (c === "LeanProperty" && cls(node.args?.[1]) === "LeanToken") {
    const p = nameToken(node.args[1].text || "");
    if (TYPE_TO_SECTION[p] === p) put("." + p, w);
  }
  // `→` and indexed families `ℕ ⇀ ℂ`: domain is an index, codomain is the value field.
  if ((c === "Lean_rightarrow" || c === "Lean_rightharpoonup") && node.args?.length === 2) {
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
/** Lemma folders named after typeclasses: sections are data types, so these are never chosen from binders. */
const TYPECLASS_FOLDERS = new Set(["NormedSpace", "NormedAddCommGroup", "NormedField", "InnerProductSpace", "AddCommGroup",
  "Group", "IsAlgClosed", "Module", "NumberField"]);

/** Topic/util Lemma folders that are never legal sections (AGENTS.md: section = data type). */
const TOPIC_FOLDERS = new Set([
  "AlgebraicCurve", "AlgebraicGeometry", "AutomorphicForm", "CerednikDrinfeld", "Curve",
  "Definitions", "Fourier", "groupCohomology", "HeckeEis", "ModularCurve", "P2M",
  // Mathlib non-type-former defs / util names - never legal as Lemma sections (Ideal/Count dumps).
  "Count", "Sum", "Prod", "Map", "Factors", "RamificationIdx", "RamificationIdx'",
]);

/** Body 2026-10-24: these 17 are never legal sections (no transitional keep). */
const ILLEGAL_SECTIONS = new Set([
  "Group", "InnerProductSpace", "IsAlgClosed", "Module", "NormedSpace", "NumberField",
  "AlgebraicCurve", "AlgebraicGeometry", "AutomorphicForm", "CerednikDrinfeld", "Curve",
  "Definitions", "Fourier", "groupCohomology", "HeckeEis", "ModularCurve", "P2M",
]);

/** Mathlib kinds from `mjs/lemmaSectionKinds.json` (refreshed by `node mjs/lemmaSectionKind.mjs`). */
let SECTION_KIND_MAP = null;
function sectionKindMap() {
  if (!SECTION_KIND_MAP) SECTION_KIND_MAP = loadSectionKindMap();
  return SECTION_KIND_MAP;
}

/** Topic/typeclass folders must not be chosen as sections (AGENTS.md). TYPE_TO_SECTION aliases stay allowed. */
export function refusedSectionFolder(name) {
  if (DATA_TYPE_SECTIONS.has(name) || TYPE_TO_SECTION[name]) return false;
  if (ILLEGAL_SECTIONS.has(name) || TYPECLASS_FOLDERS.has(name) || TOPIC_FOLDERS.has(name)) return true;
  const kind = sectionKindMap().get(name);
  return kind === "topic/unknown" || kind === "type class";
}

function customSection(sections, conclNode, givenTypes, importDecls = new Map(), binders = null) {
  const custom = sections.filter((s) => !DATA_TYPE_SECTIONS.has(s) && !TYPE_TO_SECTION[s] && !refusedSectionFolder(s));
  // a normalized *policy* among the hypotheses (`∀ θ, ∑ a, p θ a = 1`) makes it a probability lemma.
  // Bare convex-combination weights (`∑ i ∈ Finset.range n, w[i] = 1` with ContinuousOn / Icc) stay Real —
  // Finset / Sum / weights alone must not pick the Random type-class folder (AGENTS.md).
  if (sections.includes("Random") && givenTypes.some((g) => {
    let h = unwrapParen(g);
    let hadForall = false;
    while (cls(h) === "Lean_forall") {
      hadForall = true;
      h = unwrapParen(h.args?.[h.args.length - 1]);
    }
    return hadForall && cls(h) === "LeanEq" && cls(unwrapParen(h.args?.[0])) === "Lean_sum" && cls(h.args?.[1]) === "LeanToken" && h.args[1].text === "1";
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
  // typeclasses (NormedSpace, …) name no data type, so they never pick a section
  for (const t of conclTokens(binders)) if (custom.includes(t) && !TYPECLASS_FOLDERS.has(t)) return t;
  return null;
}

/** `import sympy.stats.iterates` → Iterates, when such a Lemma folder exists. */
/** open MvPolynomial PowerSeries -> data-type section boosts (like sympy imports). */
function openDataSections(source) {
  const out = [];
  for (const m of String(source || "").matchAll(/^open\s+([^\n]+)/gm)) {
    for (const name of m[1].trim().split(/\s+/)) {
      const sec = TYPE_TO_SECTION[name] || (DATA_TYPE_SECTIONS.has(name) ? name : null);
      if (sec) out.push(sec);
    }
  }
  return out;
}

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
  const structTypes = structBinderTypes(sigNode);
  for (const [t, w] of weights) {
    let sec;
    let raw;
    if (t.startsWith(".")) { sec = TYPE_TO_SECTION[t.slice(1)]; raw = 2; }
    else if (t.startsWith("ns:")) { sec = TYPE_TO_SECTION[t.slice(3)]; raw = 1; }
    else if (t.startsWith("st:")) { sec = structSection(t.slice(3)); raw = STRUCT_BINDER_WEIGHT; }
    else if (!TYPE_TO_SECTION[t] && structTypes.has(t)) { sec = structTypes.get(t); raw = STRUCT_BINDER_WEIGHT; } // {M : Model Θ S A} → Random
    else if (!TYPE_TO_SECTION[t] && sympyDecls().abbrevHeads.has(t)) { sec = abbrevSection(t); raw = 1; } // {w : ℝ → EuclideanVec m} → Matrix
    else { sec = TYPE_TO_SECTION[t]; raw = t === sec ? 3 : SECTION_WEIGHT[t] ?? 1; }
    if (!sec) continue;
    // ℕ/ℤ/Fin often only index or count (e : Fin 2 picks an exponent); prefer the value field (ℂ → Complex).
    // Fin is an index only when a scalar field is also present, so Fin-primary lemmas stay Fin.
    const scalarField = tokens.has("ℂ") || tokens.has("ℝ") || tokens.has("ℚ")
      || tokens.has("Complex") || tokens.has("Real") || tokens.has("Rat");
    const index = sec === "Nat" || sec === "Int" || (sec === "Fin" && scalarField);
    if (index && tokens.size > 0) raw = Math.min(raw, 1) * 0.5;
    const x = w === 0 ? raw * 0.5 : w === 2 && !index ? raw + 0.5 : raw;
    add(sec, x);
  }
  if (hasNode(sigNode, (n) => cls(n) === "LeanNorm" || cls(n) === "Lean_sqrt" || (cls(n) === "LeanToken" && n.text === "π"))) add("Real", 1);
  // projections of a repo-structure binder are read through their declared types (non-scalar only):
  // `MRP.D : Matrix S S ℝ` → Matrix, `MDP.pi : S → ProbabilityMeasure A` → Random, `MDP.MRP.P` through FiniteMDP.MRP : FiniteMRP
  {
    const bundles = bundleVars(sigNode);
    const projSecs = new Set();
    const SCALAR = new Set(["Real", "Nat", "Int", "Rat", "Complex"]);
    if (bundles.size) (function walk(n) {
      if (!n || typeof n !== "object") return;
      if (cls(n) === "LeanProperty") {
        const parts = propertyParts(n);
        if (parts && parts.length >= 2 && bundles.has(parts[0])) {
          let ty = bundles.get(parts[0]), last = null;
          for (const p of parts.slice(1)) { const nt = memberType(ty, p); if (!nt) break; ty = last = nt; }
          const sec = last && (TYPE_TO_SECTION[last] || abbrevSection(last));
          if (sec && !SCALAR.has(sec)) projSecs.add(sec);
          return;
        }
      }
      for (const a of n.args || []) walk(a);
    })(sigNode);
    for (const sec of projSecs) add(sec, 2);
  }
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
  // RV binders (Ω → _ / ℕ → (ℕ → ℝ × S × A) → _) / PSpace overweight Measure / Real from {π : Measure Ω} / ℝ in the path.
  if (hasRandomAstCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 5);
  // random variables with their observed values / probability-expectation sugar
  // ({x : ℕ → Ω → X} {«x.bvar» : ℕ → X}, ℙ[π](x = «x.bvar»), 𝔼[π] x, SinglePSpace π x) are Random lemmas,
  // even though Measure / Measurable hypotheses also score for the Measure section.
  if (hasRandomVariableCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 4);
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
    // incidental interval-range hyps ((`{γ, ℓ} : Set ℝ) ⊆ Set.Ico 0 1) score Set 3 from the
    // bare `Set` token; when the conclusion is not a set identity / membership and ℝ is present,
    // keep only a weak Set signal so Real (ℝ binders / Fun ℕ ℝ / GtInftySup) can win.
    const conclIsSetFocus = !!(concl && (
      ((cls(concl) === "LeanEq" || cls(concl) === "Lean_subseteq") && (concl.args || []).length === 2 && concl.args.every(isSetCons)) ||
      ((cls(concl) === "Lean_in" || cls(concl) === "LeanIn") && isSetCons(concl.args?.[1]))
    ));
    if (!conclIsSetFocus && tokens.has("ℝ") && (scores.get("Set") ?? 0) > 1 &&
        hasNode(sigNode, (n) => cls(n) === "LeanToken" && INTERVAL.test(n.text || ""))) {
      scores.set("Set", 1);
    }
  }
  // real analysis on ℝ (ContinuousOn / DifferentiableOn / ContDiff / deriv): prefer Real over
  // incidental `Finset.range` sum domains (Finset token alone scores 3). Bare ℝ+Finset sums
  // (AbsSum/le/Sum_Abs) stay Finset; Jensen-style ContinuousOn / deriv lemmas go Real.
  {
    const realAnalysis = [...tokens].some((t) => /^(ContinuousOn|DifferentiableOn|ContDiff(On)?|deriv)$/.test(t));
    if (realAnalysis && tokens.has("ℝ") && scores.has("Real")) add("Real", 3);
    const bothFinsetBigOps = !!(concl && CLASS_TOKEN[cls(concl)] && (concl.args || []).length === 2 &&
      concl.args.every((a) => {
        const u = unwrapParen(a);
        return (cls(u) === "Lean_sum" || cls(u) === "Lean_prod") && (u.args || []).some((b) => cls(b) === "Lean_in");
      }));
    if (realAnalysis && !bothFinsetBigOps && tokens.has("ℝ") && (scores.get("Finset") ?? 0) > 1) {
      scores.set("Finset", 1);
    }
  }
  // Matrix.det / Matrix.of / Matrix Fin-stack sugar as concluded subject → Matrix over Fin /
  // Finset.range in the entry (DetStack_Mul_Sum_Mul_Pow_Sub/eq/PowSub__Mul). True Finset-primary keep Finset.
  {
    const isMatrixOf = (n) => {
      if (cls(n) !== "LeanProperty" || cls(n.args?.[0]) !== "LeanToken" || n.args[0].text !== "Matrix") return false;
      const p = n.args[1];
      if (cls(p) === "LeanToken" && p.text === "of") return true;
      // Matrix.of fun … → Property(Matrix, ArgsSpaceSeparated(of, fun))
      return cls(p) === "LeanArgsSpaceSeparated" && cls(p.args?.[0]) === "LeanToken" && p.args[0].text === "of";
    };
    const isMatrixFinStack = (n) => cls(n) === "LeanStack" && !!matrixFinBindersOf(n);
    const isDetProp = (n) => cls(n) === "LeanProperty" && cls(n.args?.[1]) === "LeanToken" && n.args[1].text === "det";
    const conclMatrixDet = !!(concl && (hasNode(concl, isDetProp) || hasNode(concl, isMatrixOf) || hasNode(concl, isMatrixFinStack)));
    if (conclMatrixDet && scores.has("Matrix")) {
      add("Matrix", 4);
      if ((scores.get("Finset") ?? 0) > 1) scores.set("Finset", 1);
      if ((scores.get("Fin") ?? 0) > 1) scores.set("Fin", 1);
    }
  }
  // R[X] / K[X] (LeanGetElem ... X) are polynomials -> Polynomial section
  if (scores.has("Polynomial") && hasNode(sigNode, (n) =>
    cls(n) === "LeanGetElem" && cls(n.args?.[1]) === "LeanToken" && n.args[1].text === "X")) {
    add("Polynomial", 4);
  }
  // MvPolynomial (Fin n) / Ideal (MvPolynomial) / eval / homogeneous grading:
  // the polynomial ring beats Fin index parameters and Ideal container binders.
  {
    const hasMvP = hasNode(sigNode, (n) => cls(n) === "LeanToken" && n.text === "MvPolynomial");
    if (hasMvP && scores.has("MvPolynomial")) {
      add("MvPolynomial", 4);
      if ((scores.get("Fin") ?? 0) > 1) scores.set("Fin", 1);
      if ((scores.get("Ideal") ?? 0) > 1) scores.set("Ideal", 1);
    }
  }
  // Module.finrank k (homogeneousSubmodule) is filed under PowerSeries (Hilbert finrank /
  // AddMonoidAlgebra convention in this repo), not Fin / MvPolynomial.
  {
    const hasHomog = hasNode(sigNode, (n) => cls(n) === "LeanToken" && n.text === "homogeneousSubmodule");
    const hasFinrank = hasNode(sigNode, (n) =>
      (cls(n) === "LeanToken" && n.text === "finrank") ||
      (cls(n) === "LeanProperty" && cls(n.args?.[1]) === "LeanToken" && n.args[1].text === "finrank"));
    if (hasHomog && hasFinrank && scores.has("PowerSeries")) {
      add("PowerSeries", 5);
      if ((scores.get("Fin") ?? 0) > 1) scores.set("Fin", 1);
      if ((scores.get("MvPolynomial") ?? 0) > 1) scores.set("MvPolynomial", 1);
    }
  }
  // matrix exponential (`exp (t • Q)` with Q : Matrix …) lives in NormedSpace/
  // (`Real.exp` / `Complex.exp` are scalar exponentials, not the matrix one)
  const matrixExp = (n) => {
    if (!n || typeof n !== "object") return false;
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && /^(Real|Complex)$/.test(n.args[0].text || "")) return false;
    if (cls(n) === "LeanToken" && (n.text === "exp" || n.text === "NormedSpace.exp")) return true;
    return (n.args || []).some(matrixExp);
  };
  if (scores.has("NormedSpace") && matrixExp(sigNode) &&
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
  // `x ⟂ᵢ[π] y` (Indep) and `x ⟂ᵢ[π] y | z` (CondIndep, a top-level `|` whose left side is `⟂ᵢ`) are propositions
  if (indepAtom(typeNode)) return true;
  const name = cls(typeNode);
  if (["Lean_forall","Lean_exists","Lean_lt","Lean_gt","Lean_le","Lean_ge","LeanEq","Lean_ne","LeanNe","Lean_leftrightarrow","Lean_land","Lean_lor","Lean_lnot","Lean_in","LeanIn","Lean_notin","Lean_subseteq"].includes(name)) return true;
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
const SYMBOL_NAME = {
  "𝔼": "Expect", "∇": "Grad", "∅": "Empty", "⊤": "Top", "⊥": "Bot", "∞": "Infty", "π": "Pi", "√": "Sqrt", "𝓝": "",
  "max⁻¹": "ArgMax", "min⁻¹": "ArgMin",
  atTop: "", atBot: "",
};

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

/**
 * P2M opaque stubs glued onto a CamelCase name: `KwF4gRRTateChainRule` → `TateChainRule`.
 * Requires a digit in the stub (hash-like); leaves ordinary identifiers alone.
 */
function stripOpaqueKwPrefix(s) {
  const m = /^(Kw(?=[A-Za-z0-9]*\d)[A-Za-z0-9]*?)(?=[A-Z][a-z])/.exec(s);
  return m ? s.slice(m[0].length) : s;
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
  s = stripOpaqueKwPrefix(s);
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
  // Instance binders `[Field K]` / `[Algebra K F]`: type/term args are binder leaves so
  // namespaced Props (`NS.TateChainRule K F E h`) do not grow `_KFE` path junk.
  if (!noBinders && name === "LeanBracket") {
    const app = node.args?.[0];
    if (cls(app) === "LeanArgsSpaceSeparated") {
      for (const a of (app.args || []).slice(1)) {
        if (cls(a) === "LeanToken" && a.text && a.text !== "_") out.add(a.text);
      }
    } else if (cls(app) === "Lean_forall" || cls(app) === "Lean_exists") {
      // fall through to quantifier walk below via args
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
  // LeanStack Fin binders (`i < n` / Matrix `i < n, j < n`) are holes like ∑ binders
  if (name === "LeanStack") {
    const binders = matrixFinBindersOf(node);
    const lts = binders || (cls(node.bound ?? node.args?.[0]) === "Lean_lt" ? [node.bound ?? node.args[0]] : []);
    for (const lt of lts) {
      if (cls(lt?.args?.[0]) === "LeanToken" && lt.args[0].text && lt.args[0].text !== "_") out.add(lt.args[0].text);
    }
  }
  // if h : P then ... else ... (dite): proof binder must not become a path token (All_Eq_Sum_ExpH).
  if (name === "LeanIte" && cls(node.args?.[0]) === "LeanColon") {
    quantBinderNames(node.args[0].args?.[0], out);
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
  // Cond token is ExpectCond (not Expect_Cond), including mid-segment (ExpectSMulExpect_Cond).
  seg = seg.replaceAll("Expect_Cond", "ExpectCond");
  // Remaining Expect_* unary → CamelCase: Expect_Add → ExpectAdd. GradExpect_* -> GradExpect* (fuse). AddExpect_* / *_Expect untouched.
  if (seg.startsWith("Expect_"))
    seg = "Expect" + seg.slice("Expect_".length);
  // GradExpect_DotPow_Id -> GradExpectDotPow_Id (Body: match ExpectDotPow_Id CamelCase)
  if (seg.startsWith("GradExpect_"))
    seg = "GradExpect" + seg.slice("GradExpect_".length);
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
  if (c === "LeanToken") return /^-?\d+(\.\d+)?$/.test(n.text || "") || n.text === "π" || n.text === "∞";
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

/** Applied heads named without `Get`: `(f ⁻¹' A)`, `μ[X | m] ω`, `max⁻¹[i] e` / `min⁻¹[i] e`. */
function fnLikeHead(head) {
  const h = unwrapParen(head);
  const c = cls(h);
  return c === "LeanPreimage" || !!condExpArg(h) || isArgMaxMinGetElem(h);
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

/** Infix / wrap arithmetic whose path atom is already a compound head (DotPow_Id, …). */
const ARITH_OP = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanMatMul"]);

/** Prefix for `f x`: arithmetic compounds (@ / ^ / …) ω-eval → Ext (ExtDotPow_Id); else Get. */
function applyEvalPrefix(head) {
  if (fnLikeHead(head)) return "";
  if (ARITH_OP.has(cls(unwrapParen(head)))) return "Ext";
  return "Get";
}

/**
 * `∀ᵐ ω, HasSum … ∧ ‖((γ ^ id) @ r[t:]) ω‖ ≤ bound` → All_And_LeNormExtDotPow_Id.
 * Drops the HasSum conjunct and the bound; keeps LeNorm of the ExtDotPow_Id eval.
 */
function aeAndLeNormExtName(body, opts) {
  let n = body;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (cls(n) !== "Lean_land" || !n.args?.[1]) return "";
  const le = unwrapParen(n.args[1]);
  if (cls(le) !== "Lean_le") return "";
  const norm = unwrapParen(le.args?.[0]);
  if (cls(norm) !== "LeanNorm") return "";
  const leName = nameExpr(le, opts);
  if (!leName || !/^LeNormExt/.test(leName)) return "";
  return "All_And_" + leName;
}

/**
 * `∀ᵐ ω, L = R` one-atom: Ae_EqL (then `∀ t, …` → All_Ae_EqL).
 * Prefer this over AeL/eq/R (e.g. All_Ae_EqGradLogProbCond, not AeGradLogProbCond/eq/GradLogProb).
 * Ordinary `=` under ∀ᵐ (not `=ᵐ` / MEq). Same underscore style as All_Eq / All_AeGe_0 siblings.
 */
function aeEqAtom(body) {
  if (!body || typeof body !== "string") return "";
  const m = /^([^/]+)\/eq\/(.+)$/.exec(body);
  if (m) return "Ae_Eq" + m[1];
  // hole / focus Eq… already one-atom
  if (/^Eq(?![a-z])/.test(body) && !body.includes("/")) return "Ae_" + body;
  return "";
}

/** Join one application argument onto head alternatives (Camel / Snake / optional). */
function argJoinAlts(acc, a, alts, opts) {
  const u = unwrapParen(a);
  const ac = cls(a);
  const compound = ac !== "LeanToken" && ac !== "LeanProperty" && !(ac === "LeanParenthesis" && cls(u) === "LeanToken");
  const fun = cls(u) === "Lean_fun";
  const simple = isSimpleArg(a, opts) || isConstNode(a);
  // Integrable ((γ ^ id) @ r[t:]) → IntegrableDotPow_Id (glue op compound; not Integrable_DotPow_Id)
  const opArg = ARITH_OP.has(cls(u));
  const snake = (h, c) => h + "_" + c;
  let next = compound && (simple || fun)
    ? uniq([...cartJoin(acc, alts, joinHeadChild), ...cartJoin(acc, alts, snake)])
    : cartJoin(acc, alts, compound && !opArg ? snake : joinHeadChild);
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

/**
 * Glue a numeric right onto a left atom: `Joint` is binary (`F_Y` style), so `_0` would be
 * Joint's second argument — use `__0` (`GtProbJoint__0`, never `GtProbJoint_0`). Same idea as
 * Tensor `SumMul__0`.
 */
function glueNumSuffix(left, dig) {
  return (/Joint$/.test(left || "") ? "__" : "_") + dig;
}

/** Binary AST ops whose second argument is named with Snake_Case (`F_Y` = `F _ Y`, README).
 *  A trailing `_0` after such a rendering is ambiguous with that second argument. */
function leftEndsInBinSnake(node) {
  const u = unwrapParen(node);
  const c = cls(u);
  if (c === "LeanPreimage" || c === "LeanInner") return true;
  if (c === "LeanParenthesis") return leftEndsInBinSnake(u.args?.[0]);
  if (c === "LeanArgsSpaceSeparated") {
    const head = u.args?.[0];
    // μ.real (f ⁻¹' s) / (f ⁻¹' s) applied: the preimage is the binary spine
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^(real|toReal)$/.test(head.args[1].text || ""))
      return (u.args || []).slice(1).some(leftEndsInBinSnake);
    if (fnLikeHead(head)) return true;
    return leftEndsInBinSnake(head);
  }
  return false;
}

/** Preferred left atom when a binary-snake spine would make `_0` ambiguous: `(M θ).real (s t ⁻¹' {x})` → Real_Preimage
 *  (hole for the measure / M θ; one Preimage; no trailing S from the process variable `s`). */
function binSnakeLeftName(node, left) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanArgsSpaceSeparated") {
    const head = u.args?.[0];
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^(real|toReal)$/.test(head.args[1].text || "")
        && (u.args || []).slice(1).some(leftEndsInBinSnake))
      return "Real_Preimage";
  }
  if (/^RealPreimageS?$/.test(left || "")) return "Real_Preimage";
  return left;
}

/**
 * Interval constructor head: Ico / Set.Ico / Finset.Ico (and Icc/Ioc/Ioo).
 * Used for asGiven S subset Set.Ico a b -> Subset_Ico (not Set/sub/Ico from the Set type ascription).
 */
function intervalCtorName(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanArgsSpaceSeparated") u = unwrapParen(u.args?.[0]);
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && /^I[co][co]$/.test(u.args[1].text || ""))
    return u.args[1].text;
  if (cls(u) === "LeanToken" && /^I[co][co]$/.test(u.text || "")) return u.text;
  return "";
}

/**
 * Domain atom of a scoped ∑ / ∏ binder: `i ∈ Finset.range n` → Range, `i ∈ Set.Icc a b` → Icc.
 * Bare `Icc` / namespaced `Set.Icc` / `Finset.range` all resolve to the constructor token.
 */
function sumDomainName(node) {
  const bind = (node.args || []).slice(0, -1).find((b) => cls(b) === "Lean_in" || cls(b) === "LeanIn");
  if (!bind) return "";
  let set = unwrapParen(bind.args?.[1]);
  if (cls(set) === "LeanArgsSpaceSeparated") set = unwrapParen(set.args?.[0]);
  if (cls(set) === "LeanProperty" && cls(set.args?.[1]) === "LeanToken") {
    const t = set.args[1].text || "";
    if (/^I[co][co]$/.test(t) || t === "range") return nameToken(t);
  }
  if (cls(set) === "LeanToken" && set.text && !/^_/.test(set.text)) {
    const t = set.text;
    if (/^I[co][co]$/.test(t) || t === "range") return nameToken(t);
  }
  return "";
}

/**
 * Nested AST for `∑ i ∈ Finset.range n, _ = k` (asGiven):
 *   Eq ( Sum ( Range (·), · ) , k )  →  `EqSumRange__k`
 * CamelCase nests heads; `_` only marks omitted args (Range's n, Sum's body) — never
 * empty segments between operators (`Eq__Sum__Range_k` is wrong).
 */
function eqSumRangeNumName(node, opts) {
  if (!opts?.asGiven) return "";
  const u = unwrapParen(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return "";
  const rhs = unwrapParen(u.args[1]);
  if (cls(rhs) !== "LeanToken" || !/^\d+$/.test(rhs.text || "")) return "";
  const sum = unwrapParen(u.args[0]);
  if (cls(sum) !== "Lean_sum" && cls(sum) !== "Lean_prod") return "";
  if (sumDomainName(sum) !== "Range") return "";
  const body = nameExpr(sum.args[sum.args.length - 1], { ...opts, asGiven: false });
  // hole body only — a named summand is a different atom
  if (body) return "";
  const sumAtom = sumRangeArityName(sum, opts);
  if (!sumAtom) return "";
  // Eq(left, k): nest left, then k as Eq's right (not an extra `_` before k — left already ends in `__`)
  return "Eq" + sumAtom + rhs.text;
}
/**
 * asGiven: hole-bodied ∑ i ∈ Finset.range n, _ → `SumRange__`
 * = Sum(Range(·), ·): Range nested under Sum; trailing `__` = Range's arg hole + Sum's body hole.
 */
function sumRangeArityName(node, opts) {
  if (!opts?.asGiven) return "";
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_sum" && cls(u) !== "Lean_prod") return "";
  if (sumDomainName(u) !== "Range") return "";
  const body = nameExpr(u.args[u.args.length - 1], { ...opts, asGiven: false });
  if (body) return "";
  const tag = cls(u) === "Lean_prod" ? "Prod" : (u.superscript === "'" ? "TSum" : "Sum");
  return tag + "Range__";
}

/**
 * `deriv^[n]` (LeanPow deriv with Bracket exponent) → DerivN (Deriv2), not IterateDerivN.
 * Used so `(deriv^[2] f) y < 0` names as Lt0Deriv2 / Gt0Deriv2, never ExtIterateDeriv2_0.
 */
function derivPowDegree(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanPow") return null;
  const base = unwrapParen(u.args?.[0]);
  const exp = unwrapParen(u.args?.[1]);
  if (cls(base) !== "LeanToken" || base.text !== "deriv") return null;
  if (cls(exp) !== "LeanBracket") return null;
  const dig = unwrapParen(exp.args?.[0]);
  if (cls(dig) !== "LeanToken" || !/^\d+$/.test(dig.text || "")) return null;
  return dig.text;
}
function derivPowName(node) {
  const d = derivPowDegree(node);
  return d == null ? "" : "Deriv" + d;
}
/** `(deriv^[n]) f y` / `deriv^[n] f y` application head → the DerivN atom (args are holes). */
function derivPowAppName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return "";
  return derivPowName(u.args?.[0]);
}

/**
 * Right-side leaf from Set.Ico / Icc / Ioc / Ioo (bare or with 0 / 1 / 0'1 bounds).
 * Membership / subset must snake: In_Ico, In_Ico0, Subset_Ico — never camel InIco / SubsetIco.
 */
function isIntervalLeafAlt(name) {
  return /^I[co][co](?:0'1|[01])?$/.test(name || "");
}

/** True when `In`/`Subset` (incl. Ae*) camel-glued onto an interval leaf (InIco, SubsetIco0, …). */
function isCamelIntervalRel(name) {
  return /^(Ae)?(In|Subset)I[co][co]/.test(name || "");
}

/** Capitalized token chain `A` / `A.B` / `A.B.C` — a module path, not a value receiver. */
function isModulePathReceiver(node) {
  let n = unwrapParen(node);
  while (cls(n) === "LeanProperty") {
    const obj = n.args?.[0];
    const prop = n.args?.[1];
    if (cls(prop) !== "LeanToken") return false;
    if (cls(obj) === "LeanToken") return /^[A-Z]/.test(obj.text || "");
    n = obj;
  }
  return cls(n) === "LeanToken" && /^[A-Z]/.test(n.text || "");
}

/** `Measure.count`, `Set.univ`, `ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule`: namespaced constants. */
function isNamespacedConst(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken") return false;
  const obj = u.args?.[0];
  if (cls(obj) === "LeanToken") return /^[A-Z]/.test(obj.text || "");
  return isModulePathReceiver(obj);
}

/** `(x : Measure S)` / a colon ascription in an argument list. */
function isTypeAscriptionExpr(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanColon") return true;
  if (cls(u) === "LeanArgsSpaceSeparated") return (u.args || []).some((a) => cls(unwrapParen(a)) === "LeanColon");
  return false;
}

/** Relation alternatives: `ae` soft relations for ᵐ (`=ᵐ` reads MEq, composed like Eq), literal-left mirroring, identity. */
function relationAlts(node, tag0, opts) {
  const args = node.args || [];
  const ae = node.superscript === "ᵐ";
  // `f =ᵐ[μ] g` is its own relation `MEq` (Lemma/Random/MEqCondExp_Integral, Random/Eq/of/Ne_0/MEq):
  // inline only (MEq_CondExp, MEqCondExp_Integral, bare MEq), never the `X.ae.Y` soft form
  if (ae && tag0 === "Eq") return meqAlts(node, opts);
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
        // asGiven: deriv^[n] ≶ 0 → Rel0DerivN first (Gt0Deriv2 for f'' < 0); never LtDeriv2_0
        if (opts.asGiven && /^Deriv\d+$/.test(l) && r === "0" && (tag === "Lt" || tag === "Gt")) {
          out.push((tag === "Lt" ? "Gt0" : "Lt0") + l);
        }
        // asGiven: AbsSub_Div_Sum ≤ AbsSub_Div_Sum → LeAbsSSub_Div_Sum
        if (opts.asGiven && l && l === r && /^AbsSub_Div_Sum/.test(l)) {
          out.push(T(tag) + "AbsSSub_Div_Sum");
        }
        // asGiven: binary-snake left + numeric right → Rel0Left (Ne0Real_Preimage), not RelLeft_0
        if (opts.asGiven && /^\d+$/.test(r) && leftEndsInBinSnake(args[0])) {
          out.push(T(tag) + r + binSnakeLeftName(args[0], l));
        } else if (opts.asGiven && isNamespacedConst(args[1])) {
          // Measure.count: no underscore (EqMeasureCount); EqMeasure_Count kept as alt
          // [CountableMeasure α] is an instance binder, not an of-atom — do not invent
          // EqMeasureCount for SinglePSpace.of.AEMeasurable / .Measurable after remigration.
          out.push(T(tag) + l + r);
          out.push(T(tag) + l + (/^\d+$/.test(r) ? glueNumSuffix(l, r) : "_" + r));
        } else if (opts.asGiven && (isTypeAscriptionExpr(args[0]) || isTypeAscriptionExpr(args[1]))) {
          out.push(T(tag) + l + r);
          out.push(T(tag) + l + (/^\d+$/.test(r) ? glueNumSuffix(l, r) : "_" + r));
        } else if ((tag === "In" || tag === "Subset") && isIntervalLeafAlt(r)) {
          // γ ∈ Set.Ico 0 1 / S ⊆ Set.Ico → In_Ico / Subset_Ico only (never InIco / SubsetIco)
          out.push(T(tag) + l + "_" + r);
        } else {
          out.push(T(tag) + l + r);
          out.push(l + T(tag) + r);
          if (l !== r && l.startsWith(r)) out.push(T(tag) + l);
          out.push(T(tag) + l + (/^\d+$/.test(r) ? glueNumSuffix(l, r) : "_" + r));
        }
      }
    }
    if (!L.length && R.length) {
      for (const r of R) {
        out.push(T(tag) + "_" + r);
        // interval leaves: In_Ico / Subset_Ico only — camel InIco ranks shorter and is never a real leaf
        if (!((tag === "In" || tag === "Subset") && isIntervalLeafAlt(r))) out.push(T(tag) + r);
      }
    }
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
    // the section itself is the subject: <Section>/Subset_X (the section's own notion ⊆ X) also reads Subset_X
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
  let outR = uniq([...(mirror ? gen(MIRROR_REL[tag0], rightAlts, leftAlts) : []), ...dropped, ...gen(tag0, leftAlts, rightAlts)]);
  // ∑ i ∈ Finset.range n, _ = k → EqSumRange__k (nested AST; drop Eq__Sum__Range_* / crushed EqSumRange_k)
  if (opts.asGiven && tag0 === "Eq") {
    const eqRange = eqSumRangeNumName(node, opts);
    if (eqRange) {
      outR = uniq([eqRange, ...outR.filter((a) => a !== eqRange && !/^Eq__Sum__Range_?\d+$/.test(a) && !/^EqSumRange_?\d+$/.test(a) && !/^EqSum_?\d+$/.test(a))]);
    }
  }
  // asGiven S subset Set.Ico a b -> Subset_Ico preferred (EqSlice/of/Subset_Ico; GAE of/.../Subset_Ico)
  if (opts.asGiven && tag0 === "Subset") {
    const iv = intervalCtorName(args[1]);
    if (iv) {
      const pref = "Subset_" + iv;
      outR = uniq([pref, ...outR.filter((a) => a !== pref && !isCamelIntervalRel(a))]);
    }
  }
  // x ∈ / ⊆ Set.Ico / Icc / Ioc / Ioo → In_Ico* / Subset_Ico* only (never InIco / SubsetIco)
  if ((tag0 === "In" || tag0 === "Subset") && intervalCtorName(args[1])) {
    outR = outR.filter((a) => !isCamelIntervalRel(a));
  }
  // `(M θ).real (s t ⁻¹' {x}) ≠ 0` → Ne0Real_Preimage only (drop NeRealPreimageS_0 / Ne0RealPreimageS)
  if (opts.asGiven && leftEndsInBinSnake(args[0]) && isConstNode(args[1])) {
    const dig = nameExpr(args[1], opts);
    const tUse = (MIRROR_REL[tag0] && isConstNode(args[0]) && !isConstNode(args[1])) ? MIRROR_REL[tag0] : tag0;
    const pref = (ae ? "Ae" : "") + tUse + dig + "Real_Preimage";
    outR = outR.filter((a) => !/PreimageS/.test(a) && !(/Preimage/.test(a) && /_\d+$/.test(a)));
    if (dig && !outR.includes(pref)) outR.unshift(pref);
  }
  // joint of RVs equal to a cdot section or one variable: Eq_Joint beside Eq (All_Eq_Joint under ∀)
  if (tag0 === "Eq" && eqJointSides(node)) {
    const i = outR.indexOf("Eq");
    if (i >= 0) outR.splice(i + 1, 0, "Eq_Joint");
    else outR.push("Eq_Joint");
    // prefer Eq_Joint ahead of bare Eq for ranking / pickCanon
    outR = uniq(["Eq_Joint", ...outR.filter((a) => a !== "Eq_Joint")]);
  }
  // ‖ExtDot…‖ ≤ bound: LeNormExt… preferred (no /le/MulSub1AbsR)
  if (!opts.asGiven && tag0 === "Le") {
    const leNorm = leftAlts.filter((l) => /^NormExt/.test(l)).map((l) => "Le" + l);
    if (leNorm.length) outR = uniq([...leNorm, ...outR]);
    // ‖r…‖ ≤ |R| → LeNorm_Abs preferred (not Norm/le/AbsR)
    if (leftAlts.some((l) => /^NormR?$/.test(l)) && rightAlts.some((r) => /^Abs/.test(r))) {
      outR = uniq(["LeNorm_Abs", ...outR]);
    }
  }
  return outR;
}

/** `=ᵐ` names: both sides named → MEqL_R (also MEqLR, MEqL when the sides agree; `L/ae/R` accepted), a hole or
 *  abbreviated lambda side → MEq_R / MEqL, both holes or both lambdas → MEq.
 *  Named Lean identifier sides snake after MEq only (`MEq_Clip`, never camel `MEqClip`; same family as
 *  `MEq_Expect` / `MEq_Expect_Cond`). Bare Expect (non-cond) stays `MEqExpect`; equal condSigma prefers
 *  `MEqExpectS`. This does not change Norm/Abs gluing: ‖clip …‖ → `NormClip` (not `Norm_Clip`); |R| → `AbsR`. */
const isFunNode = (n) => cls(unwrapParen(n)) === "Lean_fun";
/** Fuse `MEq` onto a side name. `condSigma`: abbreviated `Expect` from `𝔼[…|…]` → `MEq_Expect`, not `MEqExpect`. */
function meqFuse(side, condSigma = false) {
  if (!side) return "MEq";
  // intentional plural for equal Expect / equal condSigma sides
  if (side === "ExpectS" || side.startsWith("ExpectS_")) return "MEq" + side;
  // ExpectCond* (CamelCase) → MEq_Expect_Cond* (MEq atom keeps underscore); legacy Expect_Cond* too
  if (side === "ExpectCond") return "MEq_Expect_Cond";
  if (side.startsWith("ExpectCond")) return "MEq_Expect_Cond" + side.slice("ExpectCond".length);
  if (side === "Expect_Cond" || side.startsWith("Expect_Cond")) return "MEq_" + side;
  // underscored bodies: never camel-collapse past the infix
  if (side.includes("_")) return "MEq_" + side;
  if (side === "Expect") return condSigma ? "MEq_Expect" : "MEqExpect";
  if (/^Expect/.test(side)) return "MEq_" + side;
  // MEq + named id (Clip, …): snake — only here; Norm/Abs still camel-glue via joinHeadChild
  return "MEq_" + side;
}
/** Camel-collapsed / misplaced `MEqExpect*` imply folders.
 *  Legal sole: `MEqExpect`, `MEqExpectS`, `MEqExpectS_*`.
 *  Illegal: `MEqExpect_Cond`, `MEqExpectCond`, …; also bare `MEqExpect` inside a multi-segment imply chain. */
function isIllegalMeqImplySeg(seg, multi = false) {
  if (!seg) return false;
  if (seg === "MEqExpect") return !!multi; // legacy short for equal Expect; not a chain segment
  if (!/^MEqExpect/.test(seg)) return false;
  return !(seg === "MEqExpectS" || seg.startsWith("MEqExpectS_"));
}
function hasIllegalMeqImply(path) {
  const segs = String(path || "").split("/").filter(Boolean);
  const multi = segs.length > 1;
  return segs.some((s) => isIllegalMeqImplySeg(s, multi));
}
function meqAlts(node, opts) {
  const args = node.args || [];
  const L = nameExprAlts(args[0], opts);
  const R = nameExprAlts(args[1], opts);
  const leftCond = isExpectCondApp(args[0]);
  const rightCond = isExpectCondApp(args[1]);
  const bothCondSigma = leftCond && rightCond;
  const condSigma = leftCond || rightCond;
  const fuse = (side) => meqFuse(side, condSigma);
  const gen = (L, R) => {
    const out = [];
    const pairs = [];
    for (let i = 0; i < L.length; i++) for (let j = 0; j < R.length; j++) pairs.push([i + j, i, j]);
    pairs.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const [, i, j] of pairs) {
      const l = L[i], r = R[j];
      if (!l || !r) continue;
      // Expect vs Expect_Cond is the same condSigma sugar (C omitted): never MEqExpect_Expect_Cond
      if (bothCondSigma && isBareExpectFamily(l) && isBareExpectFamily(r) && l !== r) continue;
      // identity, as for Eq: CondExpPow_Id (both sides CondExpPow_Id); MEq_Expect_Cond / MEqExpectS
      if (l === r) {
        out.push(fuse(l), l);
        if (!l.includes("/")) {
          const pl = pluralSnakeS(l) || pluralLetterS(l) || pluralMidS(l);
          if (pl) out.push(fuse(pl));
        }
      } else {
        // unequal: snake join only — never camel `MEq`+l+r collapse
        out.push("MEq_" + l + "_" + r);
        if (l.startsWith(r)) out.push(fuse(l));
      }
      // the relation path form `X/ae/Y` stays legal (Random/CondExpInner/ae/Inner_CondExp); only fused AeEq is gone
      out.push(l + "/ae/" + r);
    }
    if (!L.length) for (const r of R) out.push(fuse(r));
    if (!R.length) for (const l of L) out.push(fuse(l));
    if (!L.length && !R.length) out.push("MEq");
    // both sides condSigma with omitted C: surface MEqExpectS; keep short MEqExpect for bare-Expect alts only
    // never unshift camel `MEqExpect_Cond` (that collapses `Expect_Cond`)
    if (bothCondSigma) out.unshift("MEqExpectS", "MEqExpect", "MEqExpectS_Cond", "MEq_Expect_Cond");
    return out;
  };
  const f0 = isFunNode(args[0]), f1 = isFunNode(args[1]);
  const dropped = f0 && f1 ? gen([], []) : f1 ? gen(L, []) : f0 ? gen([], R) : [];
  // bare `MEq` only when both sides are holes/funs — never append it into And-product shortenings
  const raw = uniq([...gen(L, R), ...dropped].filter(Boolean));
  return raw.filter((s) => !hasIllegalMeqImply(s));
}
function meqCanon(node, opts) {
  const args = node.args || [];
  const f0 = isFunNode(args[0]), f1 = isFunNode(args[1]);
  if (f0 && f1) return "MEq";
  // 𝔼[…|…] =ᵐ 𝔼[…|…] (condSigma both sides): Expect is binary; equal shapes → MEqExpectS, not Expect_Expect_…
  if (!f0 && !f1 && isExpectCondApp(args[0]) && isExpectCondApp(args[1])) return "MEqExpectS";
  const left = f0 ? "" : nameExpr(args[0], opts);
  const right = nameExpr(args[1], opts);
  const condSigma = isExpectCondApp(args[0]) || isExpectCondApp(args[1]);
  if (left && right) {
    if (left === right) {
      if (isBareExpectFamily(left)) {
        const plural = pluralSnakeS(left) || pluralLetterS(left) || pluralMidS(left);
        if (plural) return meqFuse(plural, condSigma);
      }
      return meqFuse(left, condSigma);
    }
    return "MEq_" + left + "_" + right;
  }
  if (right) return meqFuse(right, condSigma);
  if (left) return meqFuse(left, condSigma);
  return "MEq";
}

function relationCanon(node, tag0, opts) {
  const args = node.args || [];
  const ae = node.superscript === "ᵐ";
  if (ae && tag0 === "Eq") return meqCanon(node, opts);
  let tag = tag0;
  let left = nameExpr(args[0], opts);
  let right = nameExpr(args[1], opts);
  if (MIRROR_REL[tag] && isConstNode(args[0]) && !isConstNode(args[1])) {
    [left, right] = [right, left];
    tag = MIRROR_REL[tag];
  }
  const T = ae ? "Ae" + tag : tag;
  const soft = tag === "Iff" ? "is" : tag === "Subset" ? "sub" : ae ? (tag === "Eq" ? "ae" : "ae" + tag) : tag.toLowerCase();
  // (· t) = (r t, s t, a t) → Eq_Joint even when the `·` side names empty (All_Eq_Joint under ∀)
  if (tag === "Eq" && eqJointSides(node)) return "Eq_Joint";
  // ∑ i ∈ Finset.range n, _ = k → EqSumRange__k (nested Eq(Sum(Range(·),·), k))
  if (opts.asGiven && tag === "Eq") {
    const eqRange = eqSumRangeNumName(node, opts);
    if (eqRange) return eqRange;
  }
  if (left && right) {
    if (left === right && (tag === "Eq" || tag === "Iff")) return left;
    if (opts.asGiven) {
      // ({gamma, ell} : Set R) subset Set.Ico 0 1 -> Subset_Ico (drop incidental Set left; not Set/sub/Ico)
      const iv = tag === "Subset" ? intervalCtorName(args[1]) : "";
      if (iv) return "Subset_" + iv;
      // binary-snake left + numeric right: Ne0Real_Preimage (not NeRealPreimageS_0; `_0` would be Preimage's 2nd arg)
      if (/^\d+$/.test(right) && leftEndsInBinSnake(args[0])) return T + right + binSnakeLeftName(args[0], left);
      // namespaced const / type ascription: EqMeasureCount (no underscore)
      if (isNamespacedConst(args[1]) || isTypeAscriptionExpr(args[0]) || isTypeAscriptionExpr(args[1])) return T + left + right;
      // deriv^[n] ≶ 0 / 0 ≷ deriv^[n] → Rel0DerivN (0-first): f'' < 0 ≡ 0 > f'' → Gt0Deriv2
      // (never LtExtIterateDeriv2_0 / LtDeriv2_0)
      if (/^Deriv\d+$/.test(left || "") && right === "0" && (tag === "Lt" || tag === "Gt")) {
        return (tag === "Lt" ? "Gt0" : "Lt0") + left;
      }
      // |a - mean| ≤ |a - mean| with mean = (∑)/card → LeAbsSSub_Div_Sum (Plural S; keep Div_Sum)
      if (left && left === right && /^AbsSub_Div_Sum/.test(left)) return T + "AbsSSub_Div_Sum";
      // ProbJoint + 0 → GtProbJoint__0 (Joint is binary; never GtProbJoint_0)
      return T + left + (/^\d+$/.test(right) ? glueNumSuffix(left, right) : "_" + right);
    }
    if (right === "0" && (soft === "gt" || soft === "lt")) return left + "/" + (soft === "gt" ? "Gt_0" : "Lt_0");
    if (left === "0" && (soft === "gt" || soft === "lt")) return right + "/" + (soft === "lt" ? "Gt_0" : "Lt_0");
    // ‖(ExtDotPow_Id)‖ ≤ bound → LeNormExtDotPow_Id (bound stays in the statement, not the path)
    if (!opts.asGiven && tag === "Le" && /^NormExt/.test(left)) return "Le" + left;
    // ‖r k ω‖ ≤ |R| → LeNorm_Abs (not Norm/le/AbsR; Abs not AbsR in this compound)
    if (!opts.asGiven && tag === "Le" && /^NormR?$/.test(left) && /^Abs/.test(right)) return "LeNorm_Abs";
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
/** `∞` / `oo` on a comparison side. */
function isInftyToken(n) {
  const u = unwrapParen(n);
  return cls(u) === "LeanToken" && (u.text === "∞" || u.text === "oo");
}
/**
 * `sup[x, y] e < ∞` (sympy/concrete/sup.lean): GetElem `sup[…]` compared with infinity.
 * Literal given atom: `LtSup__Infty` (`Sup _ < ∞`; body of `sup` is a hole).
 * Short form (preferred in paths): `GtInftySup` (`∞ > Sup`, constant mirrored to the front).
 */
function isSupLtInfty(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_lt" || (u.args || []).length !== 2) return false;
  if (!isInftyToken(u.args[1])) return false;
  let lhs = unwrapParen(u.args[0]);
  const head = cls(lhs) === "LeanArgsSpaceSeparated" ? lhs.args?.[0] : lhs;
  return cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "sup";
}
/**
 * The elaborated forms of the `sup[…] e < ∞` sugar (sympy/concrete/sup.lean), written out:
 * `BddAbove (Set.range fun x ↦ e)` and `BddAbove ((fun (x, y) ↦ e) '' {p | c})`. Named like the sugar,
 * GtInftySup (the only accepted spelling). A plain `BddAbove (f '' S)` / `BddAbove (Set.range f)` is not the sugar.
 */
function isBddAboveSup(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return false;
  if (cls(u.args[0]) !== "LeanToken" || u.args[0].text !== "BddAbove") return false;
  let a = unwrapParen(u.args[1]);
  // `Set.range fun x ↦ e` parses as Set.(range fun x ↦ e)
  if (cls(a) === "LeanProperty" && cls(a.args?.[0]) === "LeanToken" && a.args[0].text === "Set") a = a.args[1];
  // a multi-line image `(fun p ↦ e) ''\n {p | c}` is indented: its first line carries the lambda and ''
  if (cls(a) === "LeanArgsIndented") a = a.args?.[0];
  if (cls(a) !== "LeanArgsSpaceSeparated") return false;
  const xs = a.args || [];
  if (xs.length === 2 && cls(xs[0]) === "LeanToken" && /^(Set\.)?range$/.test(xs[0].text || "") && cls(unwrapParen(xs[1])) === "Lean_fun") return true;
  return xs.length >= 2 && cls(unwrapParen(xs[0])) === "Lean_fun" && cls(xs[1]) === "LeanToken" && xs[1].text === "''";
}
/** Kind of the bounded quantity of a sup-bound (sugar or elaborated): `‖…‖` → Norm, `|…|` → Abs, else "". */
function supBoundKind(node) {
  const u = unwrapParen(node);
  let body = null;
  if (isSupLtInfty(u)) {
    const lhs = unwrapParen(u.args[0]);
    body = cls(lhs) === "LeanArgsSpaceSeparated" ? lhs.args?.[lhs.args.length - 1] : null;
  } else {
    let a = unwrapParen(u.args?.[1]);
    if (cls(a) === "LeanProperty") a = a.args?.[1];
    if (cls(a) === "LeanArgsIndented") a = a.args?.[0];
    const f = (a?.args || []).map(unwrapParen).find((x) => cls(x) === "Lean_fun");
    const r = f?.args?.[0];
    body = cls(r) === "LeanRightarrow" ? r.args?.[r.args.length - 1] : null;
  }
  const k = cls(unwrapParen(body));
  return k === "LeanNorm" ? "Norm" : k === "LeanAbs" ? "Abs" : "";
}
/** `sup[…] e < ∞` names: shortest first (GtInftySup), then the typed form (GtInftySup_Norm / GtInftySup_Abs). */
function supBoundAlts(node) {
  const k = supBoundKind(node);
  return k ? ["GtInftySup", "GtInftySup_" + k, "LtSup__Infty"] : ["GtInftySup", "LtSup__Infty"];
}
/**
 * Body of a gradient application: binder sugar or binder-free Mathlib gradient.
 * Returns the differentiated expression, or null when node is not a gradient app.
 * The binder / evaluation point is never a path atom.
 */
/** True when node is (gamma ^ id) @ ... (DotPow_Id return path). */
function isDotPowIdApp(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanMatMul" || (u.args || []).length !== 2) return false;
  let pow = unwrapParen(u.args[0]);
  if (cls(pow) !== "LeanPow" || (pow.args || []).length !== 2) return false;
  let exp = unwrapParen(pow.args[1]);
  if (cls(exp) === "LeanColon") exp = unwrapParen(exp.args?.[0]);
  return cls(exp) === "LeanToken" && exp.text === "id";
}

/** (ell ^ id) @ fun k => ... -- FunPowDot (GAE / GradExpect DotFunMulFunPowDot vocabulary). */
function isFunPowDotApp(node) {
  if (!isDotPowIdApp(node)) return false;
  const u = unwrapParen(node);
  return cls(unwrapParen(u.args[1])) === "Lean_fun";
}

/** 1 - ell (literal 1 minus a binder/hole). */
function isSub1(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanSub" || (u.args || []).length !== 2) return false;
  const left = unwrapParen(u.args[0]);
  return cls(left) === "LeanToken" && left.text === "1";
}

/**
 * GAE identity left-hand side (Schulman Eq. (16) sugar):
 * (1 - ell) * ((ell ^ id) @ fun k => (gamma ^ range (k + 1)) @ delta[t:])
 * -> MulSub1_FunPowDot (not MulSub1DotPowS from accidental Pow/Pow plural S).
 */
function isMulSub1FunPowDot(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanMul" || (u.args || []).length !== 2) return false;
  return isSub1(u.args[0]) && isFunPowDotApp(u.args[1]);
}

/**
 * (gamma ^ range (k + 1)) @ ... -- DotPow_Range (FinsetPow.dot / GAE k-step slice).
 * Exponent head is range (token or Set.range / Finset.range property).
 */
function isDotPowRangeApp(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanMatMul" || (u.args || []).length !== 2) return false;
  let pow = unwrapParen(u.args[0]);
  if (cls(pow) !== "LeanPow" || (pow.args || []).length !== 2) return false;
  let exp = unwrapParen(pow.args[1]);
  if (cls(exp) === "LeanColon") exp = unwrapParen(exp.args?.[0]);
  if (cls(exp) === "LeanArgsSpaceSeparated") {
    const h = unwrapParen(exp.args?.[0]);
    if (cls(h) === "LeanToken" && h.text === "range") return true;
    if (cls(h) === "LeanProperty" && cls(h.args?.[1]) === "LeanToken" && h.args[1].text === "range") return true;
  }
  if (cls(exp) === "LeanToken" && exp.text === "range") return true;
  if (cls(exp) === "LeanProperty" && cls(exp.args?.[1]) === "LeanToken" && exp.args[1].text === "range") return true;
  return false;
}

/** fun k => (gamma ^ range ...) @ ... */
function funBodyOf(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_fun") return null;
  const arrow = u.args?.[u.args.length - 1];
  if (cls(arrow) === "LeanRightarrow" || cls(arrow) === "Lean_mapsto") return unwrapParen(arrow.args?.[arrow.args.length - 1]);
  return unwrapParen(u.args?.[u.args.length - 1]);
}

/**
 * (ell ^ id) @ fun k => (gamma ^ range (k + 1)) @ delta[t:]
 * -> Dot_FunDotPow_Range (outer Dot of Fun whose body is DotPow_Range).
 */
function isDotFunDotPowRangeApp(node) {
  if (!isDotPowIdApp(node)) return false;
  const body = funBodyOf(unwrapParen(node).args[1]);
  return !!body && isDotPowRangeApp(body);
}

/**
 * GAE identity LHS (Schulman Eq. (16) sugar):
 * (1 - ell) * ((ell ^ id) @ fun k => (gamma ^ range (k + 1)) @ delta[t:])
 * -> MulSub1_Dot_FunDotPow_Range (not MulSub1_FunPowDot).
 */
function isMulSub1DotFunDotPowRange(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanMul" || (u.args || []).length !== 2) return false;
  return isSub1(u.args[0]) && isDotFunDotPowRangeApp(u.args[1]);
}

/** Expect of (gamma ^ id) @ ... */
function isExpectDotPowId(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return false;
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼")) return false;
  return isDotPowIdApp(u.args[1]);
}

/** Grad of (.log of ProbCond) */
function isGradLogProbCond(node) {
  const gb = gradientBody(node);
  if (!gb) return false;
  const u = unwrapParen(gb);
  if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken" || u.args[1].text !== "log") return false;
  let obj = unwrapParen(u.args[0]);
  if (cls(obj) === "LeanColon") obj = unwrapParen(obj.args?.[0]);
  return !!matchProbApp(obj);
}

/**
 * Expect of `(lhs • GradLogProbCond)` — In_Ico0 / Body policy-gradient SMul forms.
 * - `(γ^id) @ … • ∇log π(·|·)` → `ExpectSMul_GradLogProbCond` (G left implicit).
 * - `𝔼[(γ^id) @ … | …] • ∇log π` → `ExpectSMulExpectCondDotPow_Id` (GradLog right omitted).
 * ExpectCond stays CamelCase; never Expect_Cond / Expect_SMul.
 */
function expectSMulGradLogNames(node, canon) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return [];
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼")) return [];
  // Peel paren / indent / newline wrappers around multi-line • integrands (In_Ico0 RHS).
  let body = u.args[1];
  for (let i = 0; i < 10; i++) {
    body = unwrapParen(body);
    const c = cls(body);
    if (
      c === "LeanArgsNewLineSeparated" ||
      c === "LeanStatements" ||
      c === "LeanArgsIndented" ||
      c === "LeanArgsCommaSeparated" ||
      (c === "LeanArgsSpaceSeparated" && (body.args || []).length === 1)
    ) {
      const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
      if (kids.length === 1) {
        body = kids[0];
        continue;
      }
      if (c === "LeanArgsNewLineSeparated" || c === "LeanStatements" || c === "LeanArgsIndented") {
        body = firstConclusion(body);
        continue;
      }
    }
    break;
  }
  if (cls(body) !== "Lean_bullet" || (body.args || []).length !== 2) return [];
  const left = unwrapParen(body.args[0]);
  const right = unwrapParen(body.args[1]);
  if (!isGradLogProbCond(right)) return [];
  // RHS: 𝔼[G | C] • GradLog → ExpectSMulExpectCondDotPow_Id (GradLog omitted)
  const condBody = isExpectCondApp(left) ? expectCondBody(unwrapParen(left).args[1]) : null;
  if (condBody && isDotPowIdApp(condBody)) {
    return canon
      ? ["ExpectSMulExpectCondDotPow_Id"]
      : uniq(["ExpectSMulExpectCondDotPow_Id", "ExpectSMulExpectCond", "ExpectSMul"]);
  }
  {
    const ln = nameExpr(left, {});
    if (/^ExpectCondDotPow_Id$/.test(ln) || /^ExpectCondDot$/.test(ln)) {
      return canon
        ? ["ExpectSMulExpectCondDotPow_Id"]
        : uniq(["ExpectSMulExpectCondDotPow_Id", "ExpectSMulExpectCond", "ExpectSMul"]);
    }
  }
  // LHS: DotPow_Id • GradLog → ExpectSMul_GradLogProbCond (G left implicit)
  if (isDotPowIdApp(left)) {
    return canon
      ? ["ExpectSMul_GradLogProbCond"]
      : uniq(["ExpectSMul_GradLogProbCond", "ExpectSMul"]);
  }
  return [];
}


/**
 * Body Eq_SymmToDual In_Ico0 imply stem (LHS fused; not SymmToDual/eq/ExpectTSum_SMul).
 * Shared by the remigrated NeProb leaf and the legacy EqMeasureCount sister In_Ico1.
 */
const EQ_SYMM_TO_DUAL_TSUM_BODY =
  "Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond";

/**
 * `(InnerProductSpace.toDual …).symm (∑' … • ∫ … • fderiv … log ℙ(·|·).toReal) = 𝔼[…](… • ∇ log …)`.
 * Clean Expect RHS (In_Ico0); legacy In_Ico1 with let/TODO scaffolding may not match — leave its #1 alone.
 */
function isEqSymmToDualTSumGradLogShape(implyStmts) {
  let u = unwrapParen(implyStmts);
  while (u && (cls(u) === "LeanStatements" || cls(u) === "LeanArgsNewLineSeparated")) u = firstConclusion(u);
  u = unwrapParen(u);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return false;
  const left = unwrapParen(u.args[0]);
  let right = unwrapParen(u.args[1]);
  while (right && (cls(right) === "LeanStatements" || cls(right) === "LeanArgsNewLineSeparated")) {
    right = firstConclusion(right);
    right = unwrapParen(right);
  }
  // RHS must be a clean Expect (𝔼[…](…)); noisy let/TODO scaffolding → not this Body override
  if (!(cls(right) === "LeanArgsSpaceSeparated" && cls(right.args?.[0]) === "LeanGetElem"
      && cls(right.args[0].args?.[0]) === "LeanToken" && right.args[0].args[0].text === "𝔼")) {
    return false;
  }
  let hasSymm = false, hasToDual = false, hasFderiv = false, hasLog = false;
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty" && cls(n.args?.[1]) === "LeanToken") {
      const prop = n.args[1].text || "";
      if (prop === "symm") hasSymm = true;
      if (prop === "toDual") hasToDual = true;
      if (prop === "log") hasLog = true;
    }
    if (cls(n) === "LeanToken") {
      const tx = n.text || "";
      if (tx === "fderiv") hasFderiv = true;
      if (tx === "symm") hasSymm = true;
      if (tx === "toDual") hasToDual = true;
    }
    for (const a of n.args || []) walk(a);
  })(left);
  return hasSymm && hasToDual && hasFderiv && hasLog;
}

function eqSymmToDualTSumBodyName(implyStmts) {
  return isEqSymmToDualTSumGradLogShape(implyStmts) ? EQ_SYMM_TO_DUAL_TSUM_BODY : "";
}

/**
 * Body: 𝔼[(γ^id) @ fun ... (... • ∇log π)] = ∫ ((γ^id) @ fun ... (... • ∇log π)) ∂μ
 * Prefer ExpectDot/eq/Integral_Dot_FunSMul_GradLogProbCond —
 * not ExpectFunPowDot / Integral_Ext_FunPowDot / Integral_ExtDot.
 * of-tail: Ae_GtInftySup + All_Measurable; NeProb stays Lean h2 (no Diff/NeProb cluster).
 * (FunPowDot / ExtDot / AeGtInftySup / All_MeasurableFun remain alts.)
 */
const EXPECT_DOT_EQ_INTEGRAL_EXT_DOT = "ExpectDot/eq/Integral_Dot_FunSMul_GradLogProbCond";

/** Peel statement wrappers / have / indent scaffolding. */
function peelStmt(node) {
  let u = node;
  for (let i = 0; i < 14; i++) {
    u = unwrapParen(u);
    const c = cls(u);
    if (
      c === "LeanArgsIndented" ||
      c === "LeanStatements" ||
      c === "LeanArgsNewLineSeparated" ||
      c === "LeanArgsCommaSeparated"
    ) {
      const kids = (u.args || []).filter((a) => cls(a) !== "LeanLineComment");
      if (kids.length === 1) {
        u = kids[0];
        continue;
      }
      if (c === "LeanArgsIndented" || c === "LeanStatements" || c === "LeanArgsNewLineSeparated") {
        u = firstConclusion(u);
        continue;
      }
    }
    if (c === "LeanArgsSpaceSeparated" && (u.args || []).length === 1) {
      u = u.args[0];
      continue;
    }
    break;
  }
  return unwrapParen(u);
}

/** Peel statement wrappers / have scaffolding to a top-level `A = B`. */
function peelImplyEq(implyStmts) {
  const u = peelStmt(implyStmts);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return null;
  return u;
}

function isExpectAppNode(node) {
  const u = unwrapParen(node);
  return cls(u) === "LeanArgsSpaceSeparated"
    && cls(u.args?.[0]) === "LeanGetElem"
    && cls(u.args[0].args?.[0]) === "LeanToken"
    && u.args[0].args[0].text === "𝔼";
}

function isIntegralAppNode(node) {
  const u = unwrapParen(node);
  if (cls(u) === "Lean_int") return true;
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "Lean_int") return true;
  return false;
}

/**
 * GradLogProbCond in either sugar:
 * - nabla (pi.log) / isGradLogProbCond
 * - flat nabla Real.log (P).toReal (this ExpectDot=Integral ExtDot leaf)
 */
function hasGradLogProbInTree(node) {
  let found = false;
  (function walk(n, d) {
    if (!n || typeof n !== "object" || found || d > 16) return;
    if (isGradLogProbCond(n)) { found = true; return; }
    if (cls(n) === "LeanArgsSpaceSeparated" && (n.args || []).length >= 2) {
      const gb = gradientBody(n);
      if (gb) {
        let hasLog = false, hasProb = false;
        (function w2(x, e) {
          if (!x || typeof x !== "object" || e > 10) return;
          if (cls(x) === "LeanToken" && x.text === "log") hasLog = true;
          if (cls(x) === "LeanProperty" && cls(x.args?.[1]) === "LeanToken" && x.args[1].text === "log") hasLog = true;
          if (matchProbApp(x)) hasProb = true;
          for (const a of x.args || []) w2(a, e + 1);
        })(gb, 0);
        if (hasLog && hasProb) { found = true; return; }
      }
    }
    for (const a of n.args || []) walk(a, d + 1);
  })(node, 0);
  return found;
}

/** DotPow / FunPowDot integrand whose tree contains GradLog ProbCond. */
function isDotPowWithGradLog(node) {
  const u = peelStmt(node);
  if (!(isFunPowDotApp(u) || isDotPowIdApp(u))) return false;
  return hasGradLogProbInTree(u);
}

/**
 * Expect[...](FunPowDot/DotPow with GradLog) = Integral(Dot/FunSMul GradLog).
 * Body rejects ExpectFunPowDot / Integral_ExtDot naming for this leaf.
 */
function isExpectDotEqIntegralExtDotShape(implyStmts) {
  const eq = peelImplyEq(implyStmts);
  if (!eq) return false;
  const left = peelStmt(eq.args[0]);
  const right = peelStmt(eq.args[1]);
  if (!isExpectAppNode(left) || !isIntegralAppNode(right)) return false;
  const expectBody = peelStmt(left.args[1]);
  let intNode = peelStmt(right);
  if (cls(intNode) === "LeanArgsSpaceSeparated" && cls(intNode.args?.[0]) === "Lean_int") {
    intNode = peelStmt(intNode.args[0]);
  }
  let intBody = intNode.args?.[intNode.args.length - 1];
  if (cls(intBody) === "LeanArgsSpaceSeparated") {
    const bs = (intBody.args || []).filter((x) => cls(x) !== "Lean_partial" && cls(x) !== "LeanPartial");
    if (bs.length === 1) intBody = bs[0];
    else if (bs.length >= 1) {
      const head = peelStmt(bs[0]);
      if (isFunPowDotApp(head) || isDotPowIdApp(head)) intBody = head;
    }
  }
  intBody = peelStmt(intBody);
  let intCore = intBody;
  if (cls(intCore) === "LeanArgsSpaceSeparated" && (intCore.args || []).length >= 2) {
    const head = peelStmt(intCore.args[0]);
    if (isFunPowDotApp(head) || isDotPowIdApp(head)) intCore = head;
  }
  return isDotPowWithGradLog(expectBody) && isDotPowWithGradLog(intCore);
}

function expectDotEqIntegralExtDotBodyName(implyStmts) {
  return isExpectDotEqIntegralExtDotShape(implyStmts) ? EXPECT_DOT_EQ_INTEGRAL_EXT_DOT : "";
}


/**
 * Body: 𝔼[∑ (γ^t * Q) • ∇logℙ] = ∫ ∑ (γ^t * Q) • ∇logℙ
 * Prefer ExpectSum_SMulMulPow/eq/Integral_Sum_SMul_GradLogProbCond —
 * MulPow on ExpectSum LHS (γ^t * Q); GradLogProbCond on Integral RHS (ExpectDot-like).
 * Demote ExpectSum_SMul_GradLogProbCond/eq/Integral_Sum_SMul and fused
 * ExpectSum_SMulMulPow_GradLogProbCond stems for this shape.
 * of: IsPolicyTrajectory (as on live path).
 */
const EXPECT_SUM_SMUL_EQ_INTEGRAL_SUM_SMUL =
  "ExpectSum_SMulMulPow/eq/Integral_Sum_SMul_GradLogProbCond";

/** Peel wrappers down to a Lean_sum, or null. */
function peelToSum(node) {
  let u = peelStmt(node);
  for (let i = 0; i < 8; i++) {
    const c = cls(u);
    if (c === "Lean_sum") return u;
    if (c === "LeanParenthesis" && (u.args || []).length === 1) {
      u = peelStmt(u.args[0]);
      continue;
    }
    if (
      (c === "LeanArgsNewLineSeparated" || c === "LeanStatements" || c === "LeanArgsIndented") &&
      (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1
    ) {
      u = peelStmt((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
      continue;
    }
    break;
  }
  return cls(u) === "Lean_sum" ? u : null;
}

/** ∑ …, (lhs • GradLog…) — MulPow (γ^t * Q) lives on ExpectSum LHS stem. */
function isSumSMulGradLog(node) {
  const sum = peelToSum(node);
  if (!sum) return false;
  let body = peelStmt(sum.args?.[sum.args.length - 1]);
  for (let i = 0; i < 6; i++) {
    const c = cls(body);
    if (c === "Lean_bullet") break;
    if (c === "LeanParenthesis" && (body.args || []).length === 1) {
      body = peelStmt(body.args[0]);
      continue;
    }
    if (
      c === "LeanArgsNewLineSeparated" ||
      c === "LeanStatements" ||
      c === "LeanArgsIndented"
    ) {
      const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
      body = peelStmt(kids.length === 1 ? kids[0] : firstConclusion(body));
      continue;
    }
    break;
  }
  if (cls(body) !== "Lean_bullet" || (body.args || []).length !== 2) return false;
  // Expect sugar may match isGradLogProbCond; Integral expanded ProbCond uses tree walk.
  return isGradLogProbCond(body.args[1]) || hasGradLogProbInTree(body.args[1]) || hasGradLogProbInTree(body);
}

/**
 * Expect[...](Sum • GradLog) = Integral(Sum • GradLog).
 * Body: ExpectSum_SMulMulPow.eq.Integral_Sum_SMul_GradLogProbCond (split stem).
 */
function isExpectSumEqIntegralSumSMulShape(implyStmts) {
  const eq = peelImplyEq(implyStmts);
  if (!eq) return false;
  const left = peelStmt(eq.args[0]);
  const right = peelStmt(eq.args[1]);
  if (!isExpectAppNode(left) || !isIntegralAppNode(right)) return false;
  if (!isSumSMulGradLog(left.args?.[1])) return false;
  let intNode = peelStmt(right);
  if (cls(intNode) === "LeanArgsSpaceSeparated" && cls(intNode.args?.[0]) === "Lean_int") {
    intNode = peelStmt(intNode.args[0]);
  }
  if (cls(intNode) !== "Lean_int") return false;
  const sumR =
    (intNode.args || []).find((a) => cls(peelStmt(a)) === "Lean_sum") ||
    (intNode.args || []).find((a) => peelToSum(a));
  return !!sumR && isSumSMulGradLog(sumR);
}

function expectSumSMulEqIntegralSumSMulBodyName(implyStmts) {
  return isExpectSumEqIntegralSumSMulShape(implyStmts) ? EXPECT_SUM_SMUL_EQ_INTEGRAL_SUM_SMUL : "";
}

/**
 * `max⁻¹[i : …] e` / `min⁻¹[…] e` — ArgMax / ArgMin binder ops (SYMBOL_NAME), not Get-eval.
 * Never fuse the body (`GetArgMaxProbCond`); ProbCond / Mul / Prod stay separate path segments.
 */
function isArgMaxMinGetElem(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanGetElem" || cls(u.args?.[0]) !== "LeanToken") return false;
  const t = u.args[0].text || "";
  return t === "max⁻¹" || t === "min⁻¹";
}
function argMaxMinTokenName(node) {
  const u = unwrapParen(node);
  const t = cls(u) === "LeanGetElem" ? u.args?.[0]?.text : "";
  return t === "max⁻¹" ? "ArgMax" : t === "min⁻¹" ? "ArgMin" : "";
}
/** Applied `max⁻¹[…] body` / `min⁻¹[…] body`. */
function isArgMaxMinApp(node) {
  const u = unwrapParen(node);
  return cls(u) === "LeanArgsSpaceSeparated" && isArgMaxMinGetElem(u.args?.[0]) && (u.args || []).length >= 2;
}
function argMaxMinBody(node) {
  const u = unwrapParen(node);
  if (!isArgMaxMinApp(u)) return null;
  let b = unwrapParen(u.args[1]);
  while (cls(b) === "LeanColon") b = unwrapParen(b.args?.[0]); // `(ℙ… : ℝ)`
  return b;
}
/** Peel wrappers down to a Mul, or null. */
function peelToMul(node) {
  let u = peelStmt(node);
  for (let i = 0; i < 8; i++) {
    const c = cls(u);
    if (c === "LeanMul") return u;
    if (c === "LeanParenthesis" && (u.args || []).length === 1) {
      u = peelStmt(u.args[0]);
      continue;
    }
    if (
      (c === "LeanArgsNewLineSeparated" || c === "LeanStatements" || c === "LeanArgsIndented") &&
      (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1
    ) {
      u = peelStmt((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
      continue;
    }
    break;
  }
  return cls(u) === "LeanMul" ? u : null;
}
/** RHS body is `ℙ * ∏ ℙ(·|·)` (naive Bayes argmax rewrite). */
function isMulProbProdProbCond(node) {
  const u = peelToMul(node) || unwrapParen(node);
  if (cls(u) !== "LeanMul" || (u.args || []).length !== 2) return false;
  let left = unwrapParen(u.args[0]);
  let right = unwrapParen(u.args[1]);
  while (cls(left) === "LeanColon") left = unwrapParen(left.args?.[0]);
  while (cls(right) === "LeanColon") right = unwrapParen(right.args?.[0]);
  const leftProb = matchProbApp(left);
  if (!leftProb || nameProbEvent(leftProb) !== "Prob") return false;
  // `∏ j, (ℙ(·|·) : ℝ)`
  let prod = right;
  while (cls(prod) === "LeanColon") prod = unwrapParen(prod.args?.[0]);
  if (cls(prod) !== "Lean_prod") return false;
  let pbody = unwrapParen(prod.args?.[prod.args.length - 1]);
  while (cls(pbody) === "LeanColon") pbody = unwrapParen(pbody.args?.[0]);
  return nameProbApp(pbody) === "ProbCond";
}
/**
 * `ℙ * ∏ ℙ(·|·)` → MulProb_Prod_ProbCond (underscore before Prod_ProbCond).
 * Never MulProbProd_ProbCond (fuses Prob into Prod).
 */
function mulProbProdProbCondName(node) {
  return isMulProbProdProbCond(node) ? "MulProb_Prod_ProbCond" : "";
}
/**
 * `(ℙ * ∏ ℙ(·|·)) / ℙ` → DivMulProb_Prod_ProbCond.
 * Cond is binary: do not camel-glue the denominator Prob onto ProbCond
 * (`…ProbCondProb`) and do not emit `…ProbCond__Prob`.
 */
function divMulProbProdProbCondName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanDiv" || (u.args || []).length !== 2) return "";
  if (!isMulProbProdProbCond(u.args[0])) return "";
  // denominator is a separate unconditional Prob (slice atom still reads Prob, not ProbS)
  if (nameProbApp(u.args[1]) !== "Prob") return "";
  return "DivMulProb_Prod_ProbCond";
}
/** Illegal fuse: Cond's 2nd arg camel-glued (`…ProbCondProb`) or double-underscored (`…ProbCond__Prob`). */
function hasIllegalDivMulProbProdCond(path) {
  const s = String(path || "");
  return /DivMulProbProd_ProbCondProb/.test(s) || /ProbCond__Prob/.test(s);
}
/**
 * Locate the imply `LeanEq` even when a multiline RHS body is a sibling under
 * `LeanArgsIndented` (max⁻¹[i] ⏎ body parses as Eq(L, bare max⁻¹) + Mul sibling).
 * Returns { eq, rhsBody } where rhsBody is the ArgMax body (app arg or indented sibling).
 */
function findArgMaxImplyEq(implyStmts) {
  const direct = peelImplyEq(implyStmts);
  if (direct) {
    const right = peelStmt(direct.args[1]);
    if (isArgMaxMinApp(right)) return { eq: direct, rhsBody: argMaxMinBody(right) };
    return { eq: direct, rhsBody: null };
  }
  // Statements → … → LeanArgsIndented[LeanEq(…, bare max⁻¹), NewLineSeparated(Mul)]
  let u = implyStmts;
  for (let i = 0; i < 10 && u; i++) {
    u = unwrapParen(u);
    const c = cls(u);
    if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") {
      const kids = (u.args || []).filter((a) => cls(a) !== "LeanLineComment" && cls(a) !== "Lean_have" && cls(a) !== "Lean_let");
      const ind = kids.find((a) => cls(a) === "LeanArgsIndented");
      if (ind) { u = ind; continue; }
      if (kids.length === 1) { u = kids[0]; continue; }
      break;
    }
    if (c === "LeanArgsIndented") {
      const args = u.args || [];
      const eq = args.find((a) => cls(a) === "LeanEq");
      if (!eq || (eq.args || []).length !== 2) return null;
      const right = unwrapParen(eq.args[1]);
      if (isArgMaxMinApp(right)) return { eq, rhsBody: argMaxMinBody(right) };
      // bare max⁻¹[i] GetElem: body is the next indented sibling
      if (isArgMaxMinGetElem(right) && argMaxMinTokenName(right) === "ArgMax") {
        const eqIdx = args.indexOf(eq);
        const sib = eqIdx >= 0 ? args[eqIdx + 1] : null;
        const mul = sib ? peelToMul(sib) : null;
        return { eq, rhsBody: mul };
      }
      return { eq, rhsBody: null };
    }
    break;
  }
  return null;
}
/**
 * Body: max⁻¹ ProbCond = max⁻¹ (Mul Prob * Prod ProbCond).
 * Prefer ArgMax_ProbCond/eq/ArgMax_Mul_Prod_ProbCond (underscore join; Prob left implicit on Mul).
 * Legacy ArgMax/eq/ArgMax and Eq/ArgMax/Mul/Prod_ProbCond stay alts.
 * Never GetArgMaxProbCond / ArgMaxProbCond CamelCase fusion.
 */
const ARGMAX_PROBCOND_EQ_ARGMAX_MUL_PROD =
  "ArgMax_ProbCond/eq/ArgMax_Mul_Prod_ProbCond";
const ARGMAX_EQ_ARGMAX = "ArgMax/eq/ArgMax";
const ARGMAX_EQ_MUL_PROD_PROBCOND = "Eq/ArgMax/Mul/Prod_ProbCond";
function isArgMaxProbCondEqMulProdShape(implyStmts) {
  const found = findArgMaxImplyEq(implyStmts);
  if (!found) return false;
  const left = peelStmt(found.eq.args[0]);
  if (!isArgMaxMinApp(left) || argMaxMinTokenName(left.args[0]) !== "ArgMax") return false;
  const lb = argMaxMinBody(left);
  if (nameProbApp(lb) !== "ProbCond") return false;
  return !!found.rhsBody && isMulProbProdProbCond(found.rhsBody);
}
function argMaxEqArgMaxBodyName(implyStmts) {
  return isArgMaxProbCondEqMulProdShape(implyStmts) ? ARGMAX_PROBCOND_EQ_ARGMAX_MUL_PROD : "";
}
/**
 * Illegal CamelCase fuse of ArgMax with ProbCond (GetArgMaxProbCond / ArgMaxProbCond).
 * Underscored ArgMax_ProbCond / ArgMax_Mul_Prod_ProbCond stay legal.
 */
function hasIllegalGetArgMaxProbCond(path) {
  const s = String(path || "");
  return /(^|\/)GetArgMaxProbCond(?=\/|$)/.test(s) || /(^|\/)ArgMaxProbCond(?=\/|$)/.test(s);
}

/**
 * Matrix Fin-entry sugar `[i < n, j < n] body` → LeanStack (comma of two Lean_lt); Tensor
 * `[i < n] body` → LeanStack(single lt) with matrixFinBinders null.
 * Prefer DetStack_Mul_Sum_Mul_Pow_Sub for sugar; DetOfFunMul_Sum_Mul_Pow_Sub for Matrix.of fun.
 * Choose / Range / other Pows omitted; bare DetOf / DetLtI are wrong for this spine.
 */
const DET_STACK_MUL_SUM_MUL_POW_SUB = "DetStack_Mul_Sum_Mul_Pow_Sub";
const DET_STACK_MUL_SUM_EQ_POW_SUB_MUL =
  DET_STACK_MUL_SUM_MUL_POW_SUB + "/eq/PowSub__Mul";
const DET_OF_FUN_MUL_SUM_MUL_POW_SUB = "DetOfFunMul_Sum_Mul_Pow_Sub";
const DET_OF_FUN_MUL_SUM_EQ_POW_SUB_MUL =
  DET_OF_FUN_MUL_SUM_MUL_POW_SUB + "/eq/PowSub__Mul";

/** Matrix ofFun Fin binders on a LeanStack (`matrixFinBinders()` or structural comma-of-two-lt). */
function matrixFinBindersOf(stack) {
  if (cls(stack) !== "LeanStack") return null;
  if (typeof stack.matrixFinBinders === "function") {
    const b = stack.matrixFinBinders();
    if (b && b.length === 2) return b;
  }
  const bound = stack.bound ?? stack.args?.[0];
  if (cls(bound) !== "LeanArgsCommaSeparated") return null;
  const parts = (bound.args || []).filter((x) => cls(x) !== "LeanCaret");
  if (
    parts.length !== 2 ||
    !parts.every((p) => cls(p) === "Lean_lt" && cls(p.args?.[0]) === "LeanToken")
  ) {
    return null;
  }
  return parts;
}

function peelEntryStmt(node) {
  let body = unwrapParen(node);
  if (cls(body) === "LeanStatements" || cls(body) === "LeanArgsNewLineSeparated") {
    body = unwrapParen((body.args || []).find((a) => cls(a) !== "LeanLineComment"));
  }
  return body || null;
}

/** Scope / entry body of Matrix Fin-stack sugar, optionally under `(…).det`. */
function matrixStackEntryBody(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && u.args[1].text === "det") {
    u = unwrapParen(u.args[0]);
  }
  if (cls(u) !== "LeanStack" || !matrixFinBindersOf(u)) return null;
  return peelEntryStmt(u.scope ?? u.args?.[1]);
}

/** Fun body of `Matrix.of fun …`, optionally under `(…).det`. */
function matrixOfFunBody(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && u.args[1].text === "det") {
    u = unwrapParen(u.args[0]);
  }
  if (cls(u) !== "LeanProperty" || cls(u.args?.[0]) !== "LeanToken" || u.args[0].text !== "Matrix") return null;
  const prop = u.args[1];
  if (cls(prop) !== "LeanArgsSpaceSeparated" || cls(prop.args?.[0]) !== "LeanToken" || prop.args[0].text !== "of") {
    return null;
  }
  let fun = unwrapParen(prop.args[1]);
  if (cls(fun) !== "Lean_fun") return null;
  let body = fun.args?.[fun.args.length - 1];
  if (cls(body) === "LeanRightarrow" || cls(body) === "Lean_mapsto") body = body.args?.[body.args.length - 1];
  return peelEntryStmt(body);
}

/** `(h : ℝ) ^ (i - j : ℤ)` — Pow whose exponent is Sub (colon ascriptions peeled). */
function isPowOfSub(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanPow" || (u.args || []).length !== 2) return false;
  let exp = unwrapParen(u.args[1]);
  if (cls(exp) === "LeanColon") exp = unwrapParen(exp.args?.[0]);
  return cls(exp) === "LeanSub";
}

/** Nested Mul chain contains a Pow_Sub factor (Sum body `… * (h)^ (i - j)`). */
function mulChainHasPowSub(node) {
  const seen = new Set();
  function walk(n) {
    n = unwrapParen(n);
    if (!n || typeof n !== "object" || seen.has(n)) return false;
    seen.add(n);
    if (isPowOfSub(n)) return true;
    if (cls(n) === "LeanMul") return walk(n.args?.[0]) || walk(n.args?.[1]);
    if (cls(n) === "LeanColon") return walk(n.args?.[0]);
    if (cls(n) === "LeanArgsNewLineSeparated" || cls(n) === "LeanStatements") {
      return (n.args || []).some((a) => cls(a) !== "LeanLineComment" && walk(a));
    }
    return false;
  }
  return walk(node);
}

/** Entry Mul(·, Sum(… Mul … Pow_Sub …)) → abbrev `Mul_Sum_Mul_Pow_Sub`. */
function isMulSumMulPowSubEntry(body) {
  if (!body || cls(body) !== "LeanMul" || (body.args || []).length !== 2) return false;
  const right = unwrapParen(body.args[1]);
  if (cls(right) !== "Lean_sum") return false;
  let sumBody = unwrapParen(right.args?.[right.args.length - 1]);
  if (cls(sumBody) === "LeanArgsNewLineSeparated" || cls(sumBody) === "LeanStatements") {
    sumBody = unwrapParen((sumBody.args || []).find((a) => cls(a) !== "LeanLineComment"));
  }
  return cls(sumBody) === "LeanMul" && mulChainHasPowSub(sumBody);
}

function isDetStackMulSumMulPowSubShape(node) {
  return isMulSumMulPowSubEntry(matrixStackEntryBody(node));
}

function isDetOfFunMulSumMulPowSubShape(node) {
  return isMulSumMulPowSubEntry(matrixOfFunBody(node));
}

/**
 * `( [i < n, j < n] … ).det` → DetStack_Mul_Sum_Mul_Pow_Sub;
 * `(Matrix.of fun …).det` → DetOfFunMul_Sum_Mul_Pow_Sub.
 * Stack sugar wins over OfFun when both could apply (they should not).
 */
function detMatrixEntryMulSumMulPowSubName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken" || u.args[1].text !== "det") return "";
  if (isDetStackMulSumMulPowSubShape(u)) return DET_STACK_MUL_SUM_MUL_POW_SUB;
  if (isDetOfFunMulSumMulPowSubShape(u)) return DET_OF_FUN_MUL_SUM_MUL_POW_SUB;
  return "";
}

/** RHS `(x - l) ^ (d * n)` → PowSub__Mul. */
function isPowSubMulExpr(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanPow" || (u.args || []).length !== 2) return false;
  return cls(unwrapParen(u.args[0])) === "LeanSub" && cls(unwrapParen(u.args[1])) === "LeanMul";
}

function detMatrixEntryEqPowSubMulBodyName(implyStmts) {
  const eq = peelStmt(implyStmts);
  if (cls(eq) !== "LeanEq" || (eq.args || []).length !== 2) return "";
  if (!isPowSubMulExpr(eq.args[1])) return "";
  if (isDetStackMulSumMulPowSubShape(eq.args[0])) return DET_STACK_MUL_SUM_EQ_POW_SUB_MUL;
  if (isDetOfFunMulSumMulPowSubShape(eq.args[0])) return DET_OF_FUN_MUL_SUM_EQ_POW_SUB_MUL;
  return "";
}

/** Expect of DotPow_Id @ fun of (adv bullet GradLogProbCond). */
function expectDotFunSMulGradLogName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return "";
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼")) return "";
  if (!isDotPowIdApp(u.args[1])) return "";
  const mat = unwrapParen(u.args[1]);
  let right = unwrapParen(mat.args[1]);
  if (cls(right) === "Lean_fun") {
    const arrow = right.args?.[right.args.length - 1];
    if (cls(arrow) === "LeanRightarrow" || cls(arrow) === "Lean_mapsto") right = unwrapParen(arrow.args?.[arrow.args.length - 1]);
    else right = unwrapParen(right.args?.[right.args.length - 1]);
  }
  // Multi-line fun bodies may be LeanStatements / NewLineSeparated
  while (right && (cls(right) === "LeanParenthesis" || cls(right) === "LeanStatements" || cls(right) === "LeanArgsNewLineSeparated")) {
    right = cls(right) === "LeanParenthesis" ? unwrapParen(right) : firstConclusion(right);
  }
  if (cls(right) !== "Lean_bullet" || (right.args || []).length !== 2) return "";
  if (!isGradLogProbCond(right.args[1])) return "";
  const adv = unwrapParen(right.args[0]);
  const hasDotPow = (n, d) => {
    if (!n || d > 6) return false;
    const x = unwrapParen(n);
    if (isDotPowIdApp(x)) return true;
    return (x.args || []).some((a) => hasDotPow(a, d + 1));
  };
  // Body: ExpectDot_FunSMul_ (underscore after ExpectDot) for Mul+DotPow and plain DotPow adv
  // (Subset_Ico and In_Icc/In_Ico siblings). Long MulFunPowDot stays as alt only.
  if (cls(adv) === "LeanMul" && hasDotPow(adv, 0)) return "ExpectDot_FunSMul_GradLogProbCond";
  return "ExpectDot_FunSMul_GradLogProbCond";
}

function gradientBody(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 2) return null;
  const head = u.args[0];
  const nabla = "∇";
  const isGradHead =
    (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === nabla) ||
    (cls(head) === "LeanToken" && head.text === nabla);
  if (!isGradHead) return null;
  const rest = u.args.slice(1);
  if (rest.length === 1) return rest[0];
  // Flat juxtaposition: Grad GetElem Expect GetElem body is 3+ space-separated args.
  return appSlice(u, rest);
}

function preAlts(node, opts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  // Matrix Fin-stack / of-fun Mul_Sum … Pow_Sub .det → DetStack_… / DetOfFun… (not DetLtI / bare DetOf)
  {
    const detEntry = detMatrixEntryMulSumMulPowSubName(node);
    if (detEntry) {
      return canon ? [detEntry] : uniq([detEntry, ...nameExprAltsBase(node, opts)]);
    }
  }
  // IsPolicyTrajectory path atom (Body override: not All_Eq; All_Eq remains alt for legacy)
  if (opts.asGiven && c === "LeanArgsSpaceSeparated" && cls(args[0]) === "LeanToken" && args[0].text === "IsPolicyTrajectory") {
    return canon ? ["IsPolicyTrajectory"] : uniq(["IsPolicyTrajectory", "All_Eq"]);
  }
  // GradExpect of Expect…: prefer GradExpectDotPow_Id over GradExpect_DotPow_Id (Body override)
  {
    const gb = gradientBody(node);
    if (gb) {
      if (isExpectDotPowId(gb)) return canon ? ["GradExpectDotPow_Id"] : uniq(["GradExpectDotPow_Id", "GradExpect_DotPow_Id", "GradExpect"]);
      const x = A(gb);
      const ranked = [];
      for (const y of x) {
        ranked.push("Grad" + y);
        if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
          ranked.push("GradExpect_" + y.slice("Expect".length)); // legacy snake
        }
        ranked.push("Grad_" + y);
      }
      return ranked.length ? uniq(ranked) : ["Grad"];
    }
  }

  // `sup[t, ω] |r t ω| < ∞` → GtInftySup (short for LtSup__Infty)
  if (isSupLtInfty(node)) return canon ? ["GtInftySup"] : supBoundAlts(node);
  if (isBddAboveSup(node)) return canon ? ["GtInftySup"] : uniq([...supBoundAlts(node), ...nameExprAltsBase(node, opts)]);
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
      // policy-gradient Expect of DotPow_Id / DotFunSMul_GradLogProbCond / SMul_GradLogProbCond
      {
        const pg = expectDotFunSMulGradLogName(node);
        // Expect is unary → CamelCase fusion (ExpectAdd / ExpectDotPow_Id); never Expect_* snake
        if (pg) {
          // FunSMul is Body canon for Subset_Ico and In_Icc/In_Ico siblings.
          // Do not enumerate shorter ExpectDot_SMul (byBestToWorst would steal #1).
          const fun = "ExpectDot_FunSMul_GradLogProbCond";
          const legacy = ["ExpectDotFunSMul_GradLogProbCond", "ExpectDotFunMulFunPowDot_SMul_GradLogProbCond"];
          return canon ? [pg] : uniq([pg, fun, ...legacy]);
        }
        const smulPg = expectSMulGradLogNames(node, canon);
        if (smulPg.length) return smulPg;
        if (isExpectDotPowId(node)) return canon ? ["ExpectDotPow_Id"] : uniq(["ExpectDotPow_Id", "ExpectDot"]);
      }
      // conditional 𝔼[a : π](X | C) → ExpectCond* CamelCase (Body: ExpectCond, not Expect_Cond).
      // Non-cond Expect stays CamelCase unary (ExpectAdd / ExpectMul) below.
      const body = expectCondBody(args[1]);
      if (body) {
        const x = A(body);
        const cond = x.length ? x.map((y) => "ExpectCond" + y) : ["ExpectCond"];
        // body may be left out (DotExpectCond); keep bare ExpectCond near the front (node caps)
        return canon ? cond.slice(0, 1) : uniq([...cond.slice(0, 2), "ExpectCond", "Expect", ...cond]);
      }
      const b = A(args[1]);
      // unary Expect: CamelCase only (ExpectAdd); never Expect_Add
      return b.length ? uniq(b.map((y) => "Expect" + y)) : ["Expect"];
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
    // in Random/, `∫ ω, f ω ∂μ` is an expectation: Random/MulExpect/eq/ExpectMul, Random/Expect/le/ExpectAbs
    // Expect unary CamelCase: Integral_Mul → ExpectMul (never Expect_Mul); IntegralMul → ExpectMul
    const asExpect = (xs) => {
      if (canon || opts.section !== "Random") return xs;
      const extra = [];
      for (const x of xs) {
        if (x.startsWith("Integral_")) extra.push("Expect" + x.slice("Integral_".length));
        else if (x.startsWith("Integral")) extra.push("Expect" + x.slice("Integral".length));
      }
      return uniq([...xs, ...extra]);
    };
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
  // GAE: (1 - ell) * ((ell ^ id) @ fun k => (gamma ^ range ...) @ ...) -> MulSub1_Dot_FunDotPow_Range
  if (c === "LeanMul" && isMulSub1DotFunDotPowRange(node)) {
    return canon
      ? ["MulSub1_Dot_FunDotPow_Range"]
      : uniq(["MulSub1_Dot_FunDotPow_Range", "MulSub1_FunPowDot", "MulSub1FunPowDot", "MulSub1_DotFunPow", ...nameExprAltsBase(node, opts)]);
  }
  if (c === "LeanMul" && isMulSub1FunPowDot(node)) {
    return canon
      ? ["MulSub1_FunPowDot"]
      : uniq(["MulSub1_FunPowDot", "MulSub1FunPowDot", "MulSub1_DotFunPow", ...nameExprAltsBase(node, opts)]);
  }
  if (c === "LeanMatMul" && isDotFunDotPowRangeApp(node)) {
    return canon
      ? ["Dot_FunDotPow_Range"]
      : uniq(["Dot_FunDotPow_Range", "FunPowDot", "DotPow_Id", "Dot", ...nameExprAltsBase(node, opts)]);
  }
  if (c === "LeanMatMul" && isFunPowDotApp(node)) {
    return canon
      ? ["FunPowDot"]
      : uniq(["FunPowDot", "DotPow_Id", "Dot", ...nameExprAltsBase(node, opts)]);
  }
  if (c === "LeanMatMul" && isDotPowRangeApp(node)) {
    return canon
      ? ["DotPow_Range"]
      : uniq(["DotPow_Range", "Dot", ...nameExprAltsBase(node, opts)]);
  }
  if (c === "LeanMatMul" && isDotPowIdApp(node)) {
    return canon
      ? ["DotPow_Id"]
      : uniq(["DotPow_Id", "Dot", ...nameExprAltsBase(node, opts)]);
  }
  return null;
}

/** Preferred renderings added on top of the generic ones. */
function postAlts(node, opts, alts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  if (c === "LeanMul" && chainRuleProdName(node)) return uniq([chainRuleProdName(node), ...alts]);
  if (c === "LeanMul" && jointCondMulName(node)) return uniq([jointCondMulName(node), ...alts]);
  if (c === "Lean_land" && probJointStepConjName(node)) return uniq([probJointStepConjName(node), ...alts]);
  if (c === "LeanPow" && cls(args[1]) === "LeanToken" && args[1].text === "2") {
    const b = A(args[0]);
    const sq = b.length ? b.flatMap((y) => ["Square" + y, "Square_" + y]) : ["Square"];
    return uniq([...sq, ...alts]);
  }
  if (c === "Lean_sum" || c === "Lean_prod") {
    const arityRange = sumRangeArityName(node, opts);
    if (arityRange) alts = uniq([arityRange, ...alts]);
    const sname = sumDomainName(node);
    if (sname) {
      const tag = (c === "Lean_prod" ? "Prod" : node.superscript === "'" ? "TSum" : "Sum") + sname;
      const b = A(args[args.length - 1]);
      const extra = b.length ? b.flatMap((y) => [tag + "_" + y, tag + y]) : [tag];
      // Icc/Ioo preferred in canon; Finset.range asGiven uses SumRange__ (above); plain SumRange is alt-only
      const preferDom = /^I[co][co]$/.test(sname);
      alts = preferDom
        ? uniq(extra.flatMap((e, i) => (i < alts.length ? [e, alts[i]] : [e])).concat(alts.slice(extra.length)))
        : uniq([...alts, ...(canon ? [] : extra)]);
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
    // omit one side: ExpectSMulExpectCondDotPow_Id / ExpectSMul_GradLogProbCond (In_Ico0)
    for (const l of L) if (l) extra.push("SMul" + l);
    for (const r of R) if (r) extra.push("SMul_" + r);
    return uniq([...alts, ...extra]);
  }
  return alts;
}

const NODE_ALT_CAP = 1000;
/**
 * `x ⟂ᵢ[π] y` → Indep, conditional `(x ⟂ᵢ[π] y) | z` → CondIndep (Random/…/of/CondIndep/CondIndep).
 * Returns "" for anything else.
 */
function indepAtom(node) {
  // the left side of `a ⟂ᵢ[π] b | c` spanning two lines is wrapped in LeanArgsNewLineSeparated
  const strip = (n) => {
    let u = unwrapParen(n);
    while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
      u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
    }
    return u;
  };
  const u = strip(node);
  if (cls(u) === "Lean_perp") return "Indep";
  if (cls(u) === "LeanBitOr" && cls(strip(u.args?.[0])) === "Lean_perp") return "CondIndep";
  return "";
}

/**
 * `∀ t, ∀ _ : Measurable (y t), P` — an inner ∀ over an anonymous hypothesis binder is just an implication
 * guard, so it is not a second quantifier in the name (All_CondIndep, not All_All_CondIndep).
 * Returns the body with such guard quantifiers peeled off.
 */
function isGuardForall(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_forall" || (u.args || []).length !== 2) return false;
  const colon = u.args[0];
  return cls(colon) === "LeanColon" && cls(colon.args?.[0]) === "LeanToken" && colon.args[0].text === "_" && isPropHyp(colon.args?.[1]);
}
function peelGuardForalls(node) {
  let n = node;
  while (isGuardForall(n)) n = unwrapParen(n).args[1];
  return n;
}

/**
 * Expect_Cond → ExpectCond (anywhere); other Expect_* unary prefix → CamelCase (Expect_Add → ExpectAdd).
 * GradExpect_* -> GradExpect* (fuse, match ExpectDotPow_Id); AddExpect_* / *_Expect untouched.
 */
function demoteExpectSnake(name) {
  if (!name) return name;
  name = name.replaceAll("Expect_Cond", "ExpectCond");
  if (name.startsWith("Expect_")) name = "Expect" + name.slice("Expect_".length);
  if (name.startsWith("GradExpect_")) return "GradExpect" + name.slice("GradExpect_".length);
  return name;
}

function nameExprAlts(node, opts = {}) {
  if (!node) return [];
  const pre = preAlts(node, opts, false);
  const alts = postAlts(node, opts, pre ?? nameExprAltsBase(node, opts), false).map(demoteExpectSnake);
  return alts.length > NODE_ALT_CAP ? alts.slice(0, NODE_ALT_CAP) : alts;
}

function nameExpr(node, opts = {}) {
  if (!node) return "";
  const pre = preAlts(node, opts, true);
  const base = pre ? pre[0] || "" : nameExprBase(node, opts);
  return demoteExpectSnake(postAlts(node, opts, base ? [base] : [], true)[0] || "");
}

function unwrapParen(node) {
  let n = node;
  while (cls(n) === "LeanParenthesis") n = n.args?.[0];
  return n;
}

/** Peel paren / angle wrappers (structure/coercion args like s[t] angle fun). */
function unwrapAngle(node) {
  let n = node;
  while (n) {
    if (cls(n) === "LeanParenthesis") { n = n.args?.[0]; continue; }
    if (cls(n) === "LeanAngleBracket" && (n.args || []).length === 1) { n = n.args[0]; continue; }
    break;
  }
  return n;
}

/** fun after paren/angle peel -- drop hole Fun args on leaf apps. */
function isBareFunNode(node) {
  return cls(unwrapAngle(node)) === "Lean_fun";
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

/**
 * Peel `⇑` / Fun coercions wrapping a bvar quotation head of a GetElem slice
 * (`(⇑«x.bvar»)[:n]`). Body: Lean_land joints of such slices are ProbJoint, not ProbS
 * (trailing S must not read as a second Prob).
 */
function bvarHead(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanUparrow") u = unwrapParen(u.args?.[0]);
  return u;
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
 * Random-variable names of this lemma: functions out of a probability space
 * (`{x : Ω → α}` / `{s : ℕ → Ω → S}` once `Ω` is the domain of an
 * `IsProbabilityMeasure` / `PSpace` measure) and trajectory coordinates of
 * `{M : Model Θ S A}` (`ℕ → ℝ × S × A`). A comma tuple or `JointRandomSymbol`
 * of those names is a joint, the same way `∧` is; a pair of other terms is not.
 */
let RV_NAMES = new Set();

function collectRvNames(root) {
  const nodes = [];
  (function gather(n) {
    if (!n || typeof n !== "object") return;
    nodes.push(n);
    for (const k of n.args || []) gather(k);
  })(root);
  const peel = (n) => {
    let x = n;
    while (cls(x) === "LeanParenthesis") x = x.args?.[0];
    return x;
  };
  const text = (n) => strStmt(n).trim();
  const headIs = (n, name) => {
    const u = peel(n);
    const h = cls(u) === "LeanArgsSpaceSeparated" ? u.args?.[0] : u;
    const t = cls(h) === "LeanToken" ? h.text : cls(h) === "LeanProperty" && cls(h.args?.[1]) === "LeanToken" ? h.args[1].text : "";
    return t === name || (t && t.endsWith("." + name));
  };
  const colonsOf = (n) => {
    if (cls(n) !== "LeanParenthesis" && cls(n) !== "LeanBrace") return [];
    const a = n.args?.[0];
    if (cls(a) === "LeanColon") return [a];
    if (cls(a) === "LeanArgsSpaceSeparated") return (a.args || []).filter((c) => cls(c) === "LeanColon");
    return [];
  };
  const measures = new Map();
  for (const n of nodes) {
    for (const col of colonsOf(n)) {
      const rhs = peel(col.args?.[1]);
      if (headIs(rhs, "Measure") && cls(rhs) === "LeanArgsSpaceSeparated" && (rhs.args || []).length >= 2) {
        const dom = text(peel(rhs.args[1]));
        const lhs = text(col.args?.[0]);
        if (dom && lhs) measures.set(lhs, dom);
      }
    }
  }
  const probDomains = new Set();
  const addProbMeasure = (measureName) => {
    if (!measureName) return;
    const m = text(peel(measureName));
    if (measures.has(m)) probDomains.add(measures.get(m));
  };
  const probMeasureApp = (n0) => {
    const a = peel(n0);
    if (cls(a) !== "LeanArgsSpaceSeparated" || (a.args || []).length < 2) return null;
    if (!headIs(a, "IsProbabilityMeasure") && !headIs(a, "PSpace")) return null;
    return a.args[1];
  };
  for (const n of nodes) {
    if (cls(n) === "LeanBracket") addProbMeasure(probMeasureApp(n.args?.[0]));
    else if (cls(n) === "LeanParenthesis" && cls(n.args?.[0]) === "LeanColon") addProbMeasure(probMeasureApp(n.args[0].args?.[1]));
  }
  for (const n of nodes) {
    for (const col of colonsOf(n)) {
      const ty = peel(col.args?.[1]);
      if (cls(ty) !== "LeanArgsSpaceSeparated" || (ty.args || []).length < 4 || !headIs(ty, "Model")) continue;
      const S = text(peel(ty.args[ty.args.length - 2]));
      const A = text(peel(ty.args[ty.args.length - 1]));
      if (S && A) probDomains.add(`ℕ → ℝ × ${S} × ${A}`);
    }
  }
  // expanded trajectory Ω without a `Model` binder: `{r : ℕ → (ℕ → ℝ × S × A) → ℝ}`
  for (const n of nodes) {
    for (const col of colonsOf(n)) {
      (function walk(t) {
        const u = peel(t);
        if (cls(u) !== "Lean_rightarrow") return;
        const dom = peel(u.args?.[0]);
        if (isTrajectorySampleSpace(dom)) probDomains.add(text(dom));
        walk(u.args?.[1]);
      })(col.args?.[1]);
    }
  }
  const rvs = new Set();
  for (const n of nodes) {
    for (const col of colonsOf(n)) {
      const ty = peel(col.args?.[1]);
      if (cls(ty) !== "Lean_rightarrow") continue;
      let last = ty;
      while (cls(peel(last.args?.[1])) === "Lean_rightarrow") last = peel(last.args[1]);
      const dom = text(peel(ty.args?.[0]));
      const lastDom = text(peel(last.args?.[0]));
      if (!probDomains.has(dom) && !probDomains.has(lastDom)) continue;
      (function addNames(x) {
        const y = peel(x);
        if (cls(y) === "LeanToken") rvs.add(y.text);
        else if (cls(y) === "LeanArgsSpaceSeparated") for (const a of y.args || []) addNames(a);
      })(col.args?.[0]);
    }
  }
  return rvs;
}

function setRvNames(root) {
  RV_NAMES = root ? collectRvNames(root) : new Set();
}

/** `(a, b)` / `(a, b, c)` comma tuple, or null. */
function commaParts(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanArgsCommaSeparated" && (u.args || []).length >= 2) return u.args;
  return null;
}

/**
 * Body of a conditional expectation argument `X | C` / `X | C0, C1, …`.
 * Lean parses `𝔼[…](g F | X, Z)` as comma outside `|`: `((g F | X), Z)`.
 * Returns the left of `|` (the integrand); condition atoms are never path-spelled.
 */
function expectCondBody(arg) {
  const u = unwrapParen(arg);
  if (cls(u) === "LeanBitOr" && (u.args || []).length === 2 && cls(unwrapParen(u.args[0])) !== "Lean_perp") {
    return u.args[0];
  }
  const parts = commaParts(u);
  if (!parts) return null;
  const head = unwrapParen(parts[0]);
  if (cls(head) === "LeanBitOr" && (head.args || []).length === 2 && cls(unwrapParen(head.args[0])) !== "Lean_perp") {
    return head.args[0];
  }
  return null;
}

/** `𝔼[… : π](… | …)` application (σ-algebra / condSigma sugar). */
function isExpectCondApp(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return false;
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼")) return false;
  return !!expectCondBody(u.args[1]);
}

/** Bare Expect / ExpectCond heads. Legacy Expect_Cond still matched. */
function isBareExpectFamily(n) {
  return n === "Expect" || n === "ExpectCond" || n === "Expect_Cond";
}

/** `JointRandomSymbol a b` including a right-nested chain, flattened, or null. */
function jrsParts(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 3) return null;
  const h = u.args[0];
  const t = cls(h) === "LeanToken" ? h.text : cls(h) === "LeanProperty" && cls(h.args?.[1]) === "LeanToken" ? h.args[1].text : "";
  if (t !== "JointRandomSymbol" && !(t && t.endsWith(".JointRandomSymbol"))) return null;
  const out = [];
  for (const a of u.args.slice(1)) {
    const inner = jrsParts(a);
    if (inner) out.push(...inner);
    else out.push(a);
  }
  return out.length >= 2 ? out : null;
}

/** A term that is one of this lemma's random variables (not an arbitrary expression). */
function isRvTerm(node) {
  const u = unwrapParen(node);
  if (!u) return false;
  if (commaParts(u) || jrsParts(u)) return isJointRvTuple(u);
  const c = cls(u);
  if (c === "LeanToken") return RV_NAMES.has(u.text);
  if (c === "LeanGetElem") return isRvTerm(u.args?.[0]); // `r[t + 1:]`
  if (c === "LeanArgsSpaceSeparated") {
    const h = u.args?.[0];
    if (cls(h) === "LeanToken") return RV_NAMES.has(h.text);
    if (cls(h) === "LeanGetElem") return isRvTerm(h);
    return false;
  }
  return false;
}

/** Pair / triple (or nested `JointRandomSymbol`) of random variables.
 * Prefer RV_NAMES hits; fall back to single-variable sides so `⇀`-typed binders
 * (In_Ico0 remigration) still yield Eq_Joint / All_Eq_Joint like `→` binders.
 */
function isJointRvTuple(node) {
  const parts = commaParts(node) || jrsParts(node);
  if (!parts || parts.length < 2) return false;
  if (parts.every((p) => isRvTerm(p))) return true;
  return parts.every((p) => isRvTerm(p) || isSingleVarSide(p));
}

/**
 * Argument of `Measurable (…)` that should read `MeasurableJoint` (joint_rv / product).
 * RV tuples when `RV_NAMES` is set; otherwise any ≥2-tuple of single-variable sides
 * (`Measurable (x, y)` with only `Ω → α` binders and no `Measure`).
 */
function isMeasurableJointArg(node) {
  const parts = commaParts(node) || jrsParts(node);
  if (!parts || parts.length < 2) return false;
  if (parts.every((p) => isRvTerm(p))) return true;
  return parts.every((p) => isRvTerm(p) || isSingleVarSide(p));
}

/** `Measurable (x, y)` / `Measurable (r, a, s)` / `Measurable (r t, s t, a t)` → MeasurableJoint. */
function measurableJointName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 2) return "";
  const head = u.args[0];
  let text = "";
  if (cls(head) === "LeanToken") text = head.text || "";
  else if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken") text = head.args[0].text || "";
  if (!/^(AE)?(Strongly)?Measurable$/.test(text)) return "";
  if (!isMeasurableJointArg(u.args[u.args.length - 1])) return "";
  return nameToken(text) + "Joint";
}

/** `(· t)` / `·`: an anonymous cdot section, not a named variable. */
function isCdotSection(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanToken") return u.text === "·";
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken") return u.args[0].text === "·";
  return false;
}

/** One variable: `x`, `x t`, `x (t + 1)`, `x[n]`. Not a tuple, not a cdot section, not a numeral. */
function isSingleVarSide(node) {
  const u = unwrapParen(node);
  if (!u || isCdotSection(u) || commaParts(u) || jrsParts(u)) return false;
  const ident = (t) => typeof t === "string" && t !== "·" && !/^-?\d+$/.test(t) && (/^[A-Za-z_]/.test(t) || /^[^\x00-\x7F]/.test(t));
  if (cls(u) === "LeanToken") return ident(u.text);
  if (cls(u) === "LeanGetElem") return isSingleVarSide(u.args?.[0]);
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken") return ident(u.args[0].text);
  return false;
}

/**
 * `A = B` where one side is a joint of random variables (tuple or JointRandomSymbol)
 * and the other is a `·` section or a single variable. Orientation does not matter.
 * Spelled `Eq_Joint` next to `Eq` (so `∀ t, …` also yields `All_Eq_Joint`).
 */
function eqJointSides(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return false;
  const [a, b] = u.args;
  const other = (n) => isCdotSection(n) || isSingleVarSide(n);
  return (isJointRvTuple(a) && other(b)) || (isJointRvTuple(b) && other(a));
}

/**
 * Joint spelling of an independence atom when an argument is a joint of random variables.
 * Left → camel `…Joint` (`IndepJoint`, `CondIndepJoint`); right/conditioner → snake
 * `…_Joint` (`Indep_Joint`, `CondIndep_Joint` — Markov `r[t+1:] ⟂ᵢ (s,a) | s'`, corpus
 * `CondIndep_Joint.of.All_EqJoint`); both → `…Joint_Joint`. Empty when there is no such joint.
 */
function indepJointAlt(node) {
  const strip = (n) => {
    let u = unwrapParen(n);
    while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
      u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
    }
    return u;
  };
  const u = strip(node);
  let perp = null, cond = null, base = "";
  if (cls(u) === "Lean_perp") { perp = u; base = "Indep"; }
  else if (cls(u) === "LeanBitOr" && cls(strip(u.args?.[0])) === "Lean_perp") {
    perp = strip(u.args[0]); cond = u.args?.[1]; base = "CondIndep";
  } else return "";
  const left = isJointRvTuple(perp.args?.[0]);
  const right = isJointRvTuple(perp.args?.[1]);
  const cj = !!(cond && isJointRvTuple(cond));
  if (!left && !right && !cj) return "";
  let name = base;
  if (left) name += "Joint";
  // right/cond: snake `_Joint` for both Indep and CondIndep (never camel CondIndepJoint)
  if (right || cj) name += "_Joint";
  return name;
}

/** Probability-event name, counting a top-level RV tuple as a joint when `tuples` is set. */
function probEventName(event, tuples) {
  const joint = (n) => eventHasAnd(n) || (tuples && isJointRvTuple(n));
  const e = unwrapParen(event);
  if (cls(e) === "LeanBitOr") {
    const left = unwrapParen(e.args?.[0]);
    const right = unwrapParen(e.args?.[1]);
    const leftAnd = joint(left);
    const rightAnd = joint(right);
    if (leftAnd && !rightAnd) return "ProbCondJoint";
    if (rightAnd && !leftAnd) return "ProbCond_Joint";
    if (leftAnd && rightAnd) return "ProbCondJoint_Joint";
    return "ProbCond";
  }
  if (joint(e)) return "ProbS";
  return "Prob";
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
  return probEventName(event, false);
}

function nameProbApp(node) {
  const event = matchProbApp(node);
  if (!event) return "";
  return nameProbEvent(event);
}

/**
 * Joint of sequence slices with their observed values: `x[:n] = «x.bvar»[:n] ∧ y[:n] = «y.bvar»[:n]`.
 * Such a joint reads ProbJoint (ProbJointGetSliceS), not ProbS, in Random/ProbJoint/eq/Mul_Prod_MulProbSCond/….
 */
function isBvarSliceJointEvent(event) {
  const conj = [];
  const flat = (n) => {
    const u = unwrapParen(n);
    if (cls(u) === "Lean_land") (u.args || []).forEach(flat);
    else conj.push(u);
  };
  flat(event);
  const isSlice = (n) => cls(n) === "LeanGetElem" && cls(n.args?.[1]) === "LeanColon";
  return conj.length >= 2 && conj.every((c) => {
    if (cls(c) !== "LeanEq" || (c.args || []).length !== 2) return false;
    const [l, r] = c.args.map(unwrapParen);
    // peel ⇑ on either side: `(⇑x)[:n] = (⇑«x.bvar»)[:n]` (DiscreteHMM Eq_LogProbJoint / All_Lt0ProbJoint)
    return isSlice(l) && isSlice(r) && isBvarQuotation(bvarHead(r.args[0]));
  });
}
/**
 * Point-and-slice ∧-joint: `x = «x.bvar» ∧ y[:m] = «y.bvar»[:m]`.
 * Not a single-variable Prob, and not two slices (`isBvarSliceJointEvent`); still a ProbJoint.
 */
function isBvarPointSliceJointEvent(event) {
  const conj = [];
  const flat = (n) => {
    const u = unwrapParen(n);
    if (cls(u) === "Lean_land") (u.args || []).forEach(flat);
    else conj.push(u);
  };
  flat(event);
  if (conj.length < 2) return false;
  const isSlice = (n) => cls(n) === "LeanGetElem" && cls(n.args?.[1]) === "LeanColon";
  let points = 0, slices = 0;
  for (const c of conj) {
    if (cls(c) !== "LeanEq" || (c.args || []).length !== 2) return false;
    const [l, r] = c.args.map(unwrapParen);
    if (isSlice(l) && isSlice(r) && isBvarQuotation(bvarHead(r.args[0]))) slices++;
    else if (!isSlice(l) && !isSlice(r) && isBvarQuotation(bvarHead(r))) points++;
    else return false;
  }
  return points >= 1 && slices >= 1;
}
/** ∧-joint that reads ProbJoint (two bvar slices, or a point atom with a bvar slice). */
function isProbJointEvent(event) {
  return isBvarSliceJointEvent(event) || isBvarPointSliceJointEvent(event);
}
/**
 * Bare `ℙ[π](x = «x.bvar» ∧ y[:m] = «y.bvar»[:m]) ≠ 0` → NeProbJoint__0.
 * Point-and-slice is a ProbJoint (not NeProbS_0). Joint is binary → `__0` (never NeProbJoint_0);
 * `Ne0ProbJoint` stays an alt (same pattern as All_GtProbJoint__0).
 */
function neProbJoint0GivenName(typeNode) {
  let u = unwrapParen(typeNode);
  while (cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") {
    const kids = (u.args || []).filter((a) => cls(a) !== "LeanLineComment");
    u = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  if (cls(u) === "Lean_forall") return ""; // ∀ … NeProb stays All_NeProb_0 / slice-joint alts
  if (cls(u) !== "Lean_ne" && cls(u) !== "LeanNe") return "";
  const right = unwrapParen(u.args?.[1]);
  if (cls(right) !== "LeanToken" || right.text !== "0") return "";
  let left = unwrapParen(u.args?.[0]);
  if (cls(left) === "LeanColon") left = unwrapParen(left.args[0]);
  const ev = matchProbApp(left);
  return ev && nameProbEvent(ev) === "ProbS" && isBvarPointSliceJointEvent(ev) ? "NeProbJoint__0" : "";
}

/** `ℙ(a | b) * ℙ(c) * ∏ i ∈ s, ℙ(d | e) * ℙ(f | g)` — chain-rule factorization: the leading factors are absorbed. */
function chainRuleProdName(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "LeanMul" || (n.args || []).length !== 2) return "";
  const head = unwrapParen(n.args[0]);
  const prod = unwrapParen(n.args[1]);
  if (cls(head) !== "LeanMul" || (head.args || []).length !== 2 || cls(prod) !== "Lean_prod") return "";
  let body = unwrapParen(prod.args[prod.args.length - 1]);
  while ((cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") && (body.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
    body = unwrapParen((body.args || []).find((a) => cls(a) !== "LeanLineComment"));
  }
  if (cls(body) !== "LeanMul" || (body.args || []).length !== 2) return "";
  const nm = (x) => { const ev = matchProbApp(x); return ev ? nameProbEvent(ev) : ""; };
  return nm(head.args[0]) === "ProbCond" && nm(head.args[1]) === "Prob" && nm(body.args[0]) === "ProbCond" && nm(body.args[1]) === "ProbCond"
    ? "Mul_Prod_MulProbSCond" : "";
}

/**
 * `ℙ[π](s[:0+1] = «s.bvar»[:0+1] ∧ a[:0] = «a.bvar»[:0]) = ℙ[π](s 0 = «s.bvar» 0) ∧
 *   ∀ t, ℙ[π](slice-joint) = ℙ[π](slice-joint) * (ℙ(a | s) * ℙ(s' | s ∧ a))` — the chain-rule recursion of a
 * bvar-slice joint (Random/EqProbJoint/All_Eq_Mul_MulProbSCond/of/All_CondIndep/…). Deliberately narrow.
 */
function probJointStepConjName(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "Lean_land" || (n.args || []).length !== 2) return "";
  const strip = (x) => {
    let u = unwrapParen(x);
    while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
      u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
    }
    return u;
  };
  const prob = (x) => { const ev = matchProbApp(strip(x)); return ev ? { ev, name: nameProbEvent(ev) } : null; };
  const joint = (x) => { const p = prob(x); return !!p && p.name === "ProbS" && isBvarSliceJointEvent(p.ev); };
  const eq2 = (x) => { const u = strip(x); return cls(u) === "LeanEq" && (u.args || []).length === 2 ? u.args : null; };
  const mul2 = (x) => { const u = strip(x); return cls(u) === "LeanMul" && (u.args || []).length === 2 ? u.args : null; };
  const base = eq2(n.args[0]);
  if (!base || !joint(base[0]) || prob(base[1])?.name !== "Prob") return "";
  const all = strip(n.args[1]);
  if (cls(all) !== "Lean_forall") return "";
  const step = eq2(peelGuardForalls(all.args[all.args.length - 1]));
  if (!step || !joint(step[0])) return "";
  const m = mul2(step[1]);
  if (!m || !joint(m[0])) return "";
  const conds = mul2(m[1]);
  return conds && prob(conds[0])?.name === "ProbCond" && prob(conds[1])?.name === "ProbCond_Joint"
    ? "EqProbJoint/All_Eq_Mul_MulProbSCond" : "";
}

/** Structural signature of a node (class, token text, children) for comparing two sub-trees. */
function nodeSig(n) {
  if (!n || typeof n !== "object") return String(n);
  return cls(n) + (n.text !== undefined ? ":" + n.text : "") + "(" + (n.args || []).map(nodeSig).join(",") + ")";
}

/**
 * `ℙ[π](x[:t + 1] = «x.bvar»[:t + 1] ∧ y[t] = «y.bvar»[t]) * ℙ[π](x[t + 1:n] = «x.bvar»[t + 1:n] | y[t] = «y.bvar»[t])` —
 * the forward × backward product of a hidden Markov model cut at time t: a JOINT probability of an observed bvar
 * slice and the hidden state at t times the CONDITIONAL probability of the observed future given that same state
 * (Random/Sum_Mul_ProbCond/eq/Prob/of/IsDiscreteHMM). The joint factor is left implicit (not spelled `ProbS`), so the
 * product reads `Mul_ProbCond` instead of `MulProbSProbCond`. Deliberately narrow: both factors must pin the same
 * hidden state at t (`y[t] = «y.bvar»[t]`, or the bare-function forms `y[t] = «y.bvar» t` / `y t = «y.bvar» t`).
 * Closed slices may be written on `Fun` (`x[:…]`, via `Fun.getSlice`) or on a coercion (`(⇑x)[:…]`).
 */
function jointCondMulName(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "LeanMul" || (n.args || []).length !== 2) return "";
  const lEv = matchProbApp(n.args[0]);
  const rEv = matchProbApp(n.args[1]);
  if (!lEv || !rEv || nameProbEvent(lEv) !== "ProbS" || nameProbEvent(rEv) !== "ProbCond") return "";
  const isSlice = (x) => cls(x) === "LeanGetElem" && cls(x.args?.[1]) === "LeanColon";
  const eq2 = (x) => { const u = unwrapParen(x); return cls(u) === "LeanEq" && (u.args || []).length === 2 ? u.args.map(unwrapParen) : null; };
  // `(⇑«x.bvar»)[:…]` / `«x.bvar»[:…]` — Fun coercions wrap the bvar quotation
  const sliceEq = (x) => {
    const e = eq2(x);
    return !!e && isSlice(e[0]) && isSlice(e[1]) && isBvarQuotation(bvarHead(e[1].args[0]));
  };
  // `y[t] = «y.bvar» t` / `y t = «y.bvar» t` / `y[t] = «y.bvar»[t]`
  const stateEq = (x) => {
    const e = eq2(x);
    if (!e || isSlice(e[0])) return false;
    const rhs = e[1];
    if (cls(rhs) === "LeanArgsSpaceSeparated" && isBvarQuotation(rhs.args?.[0])) return true;
    if (cls(rhs) === "LeanGetElem" && !isSlice(rhs) && isBvarQuotation(bvarHead(rhs.args?.[0]))) return true;
    return false;
  };
  const conj = [];
  (function flat(x) { const u = unwrapParen(x); if (cls(u) === "Lean_land") (u.args || []).forEach(flat); else conj.push(u); })(lEv);
  if (conj.length !== 2 || !sliceEq(conj[0]) || !stateEq(conj[1])) return "";
  if (cls(rEv) !== "LeanBitOr") return "";
  const [fut, given] = rEv.args.map(unwrapParen);
  if (!sliceEq(fut) || !stateEq(given) || nodeSig(given) !== nodeSig(conj[1])) return "";
  return "Mul_ProbCond";
}

/**
 * `«y.bvar»`-quantified hypotheses: DiscreteHMM of-atoms `∀ t («y.bvar»), … = (ℙ(…|…) : ℝ).log`
 * prefer `All_Eq_LogProbCond` (see bvarAllEqLogProbCondName; same All_ policy as All_Lt0ProbJoint).
 * Bare `Eq_LogProbCond` stays an alt. In the HMM log-posterior imply shape
 *   `(∀ t, t + 1 < n → …) ∧ ∀ «y.bvar», -(ℙ(y[:n] = … | x[:n] = …) : ℝ).log = …`
 * hmmBvarAllAlts still widens altMatch for `All_Eq_LogProbCond` / `All_Lt0Prob` / `All_EqNegLogProb`.
 */
function hasBvarBinder(quant) {
  const u = unwrapParen(quant);
  if (cls(u) !== "Lean_forall" || u.superscript === "ᵐ") return false;
  let found = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || found) return;
    if (isBvarQuotation(n)) { found = true; return; }
    for (const a of n.args || []) walk(a);
  })(u.args?.[0]);
  return found;
}
function isHmmNegLogCondShape(implyStmts) {
  const parts = splitTopConjunction(implyStmts);
  if (!parts || parts.length !== 2) return false;
  const strip = (x) => {
    let u = unwrapParen(x);
    while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
      u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
    }
    return u;
  };
  const [steps, post] = parts.map(strip);
  // ∀ t, t + 1 < n → …
  if (cls(steps) !== "Lean_forall" || hasBvarBinder(steps)) return false;
  const imp = strip(steps.args[steps.args.length - 1]);
  if (cls(imp) !== "Lean_rightarrow" || cls(strip(imp.args?.[0])) !== "Lean_lt") return false;
  // ∀ «y.bvar», -(ℙ(… | …) : ℝ).log = …
  if (!hasBvarBinder(post)) return false;
  const eq = strip(post.args[post.args.length - 1]);
  if (cls(eq) !== "LeanEq" || (eq.args || []).length !== 2) return false;
  const lhs = strip(eq.args[0]);
  if (cls(lhs) !== "LeanNeg") return false;
  const lg = strip(lhs.args?.[0]);
  if (cls(lg) !== "LeanProperty" || cls(lg.args?.[1]) !== "LeanToken" || lg.args[1].text !== "log") return false;
  let cond = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || cond) return;
    const ev = matchProbApp(n);
    if (ev) { cond = nameProbEvent(ev) === "ProbCond"; return; }
    for (const a of n.args || []) walk(a);
  })(lg.args[0]);
  return cond;
}
/**
 * Extra alternatives (accepted by altMatch, never enumerated into the displayed suggestions) for a
 * `«y.bvar»`-quantified statement of the isHmmNegLogCondShape lemma.
 */
function hmmBvarAllAlts(alts) {
  const out = [];
  for (const b of alts) {
    out.push("All_" + b);
    const bare = b.replace(/Prob(?:JointGetSliceS|Joint|S)(?![A-Za-z])/g, "Prob"); // Lt0ProbS → Lt0Prob
    if (bare !== b) out.push("All_" + bare);
    const neg = /^Eq_?NegLogProbCond/.test(b) ? "EqNegLogProb" : ""; // right-hand side and Cond left implicit
    if (neg) out.push("All_" + neg);
  }
  const have = new Set(alts);
  return uniq(out.filter((x) => !have.has(x)));
}

/**
 * Hypothesis `∀ t («y.bvar» : ℕ → Y), 0 < ℙ[π](… ∧ …)` / `(ℙ[π](… ∧ …) : ℝ) > 0`, or lone `∀ «y.bvar», …`:
 * a `∀` over a `«…bvar»` binder (optionally with plain binders like `t`), body a strict positivity
 * comparison of a joint of ≥ 2 bvar-slice equations vs 0. Reads `All_Lt0ProbJoint` (`Lt0` = strictly
 * positive vs 0 — argument order `0 < p` vs `p > 0` does not matter; `Joint` = the two-equation event);
 * ranked first in givenAltLists. `All_GtProbJoint__0` is kept as an alt (`>` / `__0` because Joint is
 * binary); bare `GtProbJoint0` / `GtProbJoint_0` / `GtProbJoint__0` are never emitted (they drop `∀`).
 */
function bvarAllLt0ProbJointName(typeNode) {
  const u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall" || u.superscript === "ᵐ" || !hasBvarBinder(u)) return "";
  let body = unwrapParen(u.args[u.args.length - 1]);
  // multiline `∀ «y.bvar»,\n  0 < ℙ(…)` / `ℙ(…) > 0` wraps the inequality
  while (cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") {
    const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
    body = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  const kind = cls(body);
  if ((kind !== "Lean_lt" && kind !== "Lean_gt") || (body.args || []).length !== 2) return "";
  const left = unwrapParen(body.args[0]);
  const right = unwrapParen(body.args[1]);
  const isZero = (n) => cls(n) !== "LeanToken" ? false : n.text === "0";
  // 0 < p  or  p > 0  (same All_Lt0ProbJoint; never prefer bare GtProbJoint* from argument order)
  let probSide = null;
  if (kind === "Lean_lt" && isZero(left)) probSide = right;
  else if (kind === "Lean_gt" && isZero(right)) probSide = left;
  else return "";
  if (cls(probSide) === "LeanColon") probSide = unwrapParen(probSide.args[0]); // `(ℙ[π](…) : ℝ)`
  const ev = matchProbApp(probSide);
  return ev && nameProbEvent(ev) === "ProbS" && isBvarSliceJointEvent(ev) ? "All_Lt0ProbJoint" : "";
}

/** Bare / underscored-wrong GtProbJoint* atoms that drop `∀` or mis-glue Joint's `__0`. */
function isIllegalGtProbJointAtom(name) {
  return /^(GtProbJoint0|GtProbJoint_0|GtProbJoint__0|All_GtProbJoint0|All_GtProbJoint_0)$/.test(name || "");
}
/** Unary-looking NeProbJoint_0 / NeProbJoint0 (Joint is binary → NeProbJoint__0 / Ne0ProbJoint). */
function isIllegalNeProbJointAtom(name) {
  return /^(NeProbJoint0|NeProbJoint_0)$/.test(name || "");
}

/**
 * Hypothesis `∀ t («y.bvar» : …), lhs = (ℙ[π](… | …) : ℝ).log` (and `∀ i …` with Get-index `i + 1`):
 * a `∀` over a plain binder next to `«…bvar»`, body equality to `.log` of a conditional probability.
 * Prefers `All_Eq_LogProbCond` (drops Get-index `Add_1` noise like Body); bare `Eq_LogProbCond` /
 * `EqAdd_1_LogProbCond` stay alts. Joint-log hyps (`ℙ(… ∧ …).log`) are not this shape.
 */
function bvarAllEqLogProbCondName(typeNode) {
  const u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall" || u.superscript === "ᵐ" || !hasBvarBinder(u)) return "";
  const hasBvar = (n) => { let f = false; (function w(x) { if (!x || typeof x !== "object" || f) return; if (isBvarQuotation(x)) { f = true; return; } for (const a of x.args || []) w(a); })(n); return f; };
  const items = (u.args || []).slice(0, -1).flatMap((b) => (cls(b) === "LeanArgsSpaceSeparated" ? b.args || [] : [b]));
  if (!items.some((b) => !hasBvar(b))) return ""; // needs a plain binder next to the bvar one (∀ t «y.bvar»)
  let body = unwrapParen(u.args[u.args.length - 1]);
  while (cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") {
    const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
    body = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  if (cls(body) !== "LeanEq" || (body.args || []).length !== 2) return "";
  let rhs = unwrapParen(body.args[1]);
  if (cls(rhs) !== "LeanProperty" || cls(rhs.args?.[1]) !== "LeanToken" || rhs.args[1].text !== "log") return "";
  let inner = unwrapParen(rhs.args[0]);
  if (cls(inner) === "LeanColon") inner = unwrapParen(inner.args[0]);
  const ev = matchProbApp(inner);
  return ev && nameProbEvent(ev) === "ProbCond" ? "All_Eq_LogProbCond" : "";
}

/**
 * `∀ θ («s.bvar») («a.bvar»), ℙ[…](…) ≠ 0` (and plain-binder variants): Body / GradExpect Subset_Ico
 * prefers `All_NeProb_0` over the ae-stripped `NeProbS_0` (sibling Random/All_NeProb_0).
 * Legacy `NeProbS_0` / `All_NeProbS_0` stay alts. Returns "" when the body is not Prob ≠ 0.
 */
function allNeProb0GivenName(typeNode) {
  let u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall") return "";
  let body = unwrapParen(u.args[u.args.length - 1]);
  while (cls(body) === "Lean_forall") body = unwrapParen(body.args[body.args.length - 1]);
  while (cls(body) === "Lean_rightarrow") body = unwrapParen(body.args[body.args.length - 1]);
  // multiline given body may be LeanArgsNewLineSeparated / LeanStatements
  while (cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") {
    const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
    body = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  if (cls(body) !== "Lean_ne" && cls(body) !== "LeanNe") return "";
  const right = unwrapParen(body.args?.[1]);
  if (cls(right) !== "LeanToken" || right.text !== "0") return "";
  let left = unwrapParen(body.args?.[0]);
  if (cls(left) === "LeanColon") left = unwrapParen(left.args[0]);
  return matchProbApp(left) ? "All_NeProb_0" : "";
}

/**
 * `∀ …, Differentiable ℝ (fun θ => (ℙ(…|…) : ℝ))` (GradExpect Subset_Ico): Body prefers
 * `All_Differentiable_Prob` (siblings under Random/…/All_Differentiable_Prob/). Bare
 * `All_Differentiable` / `Differentiable_ProbCond` stay alts.
 */
function allDifferentiableGivenName(typeNode) {
  let u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall") return "";
  let body = unwrapParen(u.args[u.args.length - 1]);
  while (cls(body) === "Lean_forall") body = unwrapParen(body.args[body.args.length - 1]);
  while (cls(body) === "Lean_rightarrow") body = unwrapParen(body.args[body.args.length - 1]);
  while (cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") {
    const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
    body = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  if (cls(body) !== "LeanArgsSpaceSeparated") return "";
  const head = body.args?.[0];
  if (cls(head) !== "LeanToken" || head.text !== "Differentiable") return "";
  // Prefer All_Differentiable_Prob when the Differentiable subject mentions ℙ / Prob*
  let hasProb = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || hasProb) return;
    if (matchProbApp(n)) { hasProb = true; return; }
    for (const a of n.args || []) walk(a);
  })(body);
  return hasProb ? "All_Differentiable_Prob" : "All_Differentiable";
}


/**
 * Viterbi shape: a `max[«y.bvar» : Fin n → Y]` big operator over the joint probability of bvar-valued x/y slices.
 * `Max` is the max big operator (not an applied function), so its LHS reads `EqMax_ProbJoint`, not `GetMax`.
 */
function stripStmt(x) {
  let u = unwrapParen(x);
  while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
    u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
  }
  return u;
}
function unwrapAscribed(n) {
  let u = unwrapParen(n);
  while (cls(u) === "LeanColon") u = unwrapParen(u.args?.[0]);
  return u;
}
/** Joint event of equations `slice = «bvar» | slice = «bvar»[:k]` (at least two, one of them a bvar value). */
function isBvarJointEvent(event) {
  const conj = [];
  const flat = (n) => {
    const u = unwrapParen(n);
    if (cls(u) === "Lean_land") (u.args || []).forEach(flat);
    else conj.push(u);
  };
  flat(event);
  const isSlice = (n) => cls(n) === "LeanGetElem" && cls(n.args?.[1]) === "LeanColon";
  return conj.length >= 2 && conj.every((c) => {
    if (cls(c) !== "LeanEq" || (c.args || []).length !== 2) return false;
    const [l, r] = c.args.map(unwrapParen);
    return isSlice(l) && (isBvarQuotation(bvarHead(r)) || (isSlice(r) && isBvarQuotation(bvarHead(r.args[0]))));
  });
}
/** `max[«y.bvar» : …] a b …` → [a, b, …] (the applied arguments), else null. */
function maxBvarOperands(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "LeanArgsSpaceSeparated") return null;
  const head = n.args?.[0];
  if (cls(head) !== "LeanGetElem" || cls(head.args?.[0]) !== "LeanToken" || head.args[0].text !== "max") return null;
  const bind = head.args?.[1];
  if (cls(bind) !== "LeanColon" || !isBvarQuotation(bind.args?.[0])) return null;
  return n.args.slice(1);
}
/** `(ℙ[π](joint) : ℝ)` with a bvar joint event of x/y slices → true. */
function isBvarProbJoint(node, log = false) {
  let u = unwrapParen(node);
  if (log) {
    if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken" || u.args[1].text !== "log") return false;
    u = u.args[0];
  }
  const ev = matchProbApp(unwrapAscribed(u));
  return !!ev && nameProbEvent(ev) === "ProbS" && isBvarJointEvent(ev);
}
/** Conjunct `max[«y.bvar» : …] (ℙ(joint) : ℝ) = rhs`. */
function isMaxProbJointEq(node) {
  const u = stripStmt(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return false;
  const ops = maxBvarOperands(u.args[0]);
  return !!ops && ops.length === 1 && isBvarProbJoint(ops[0]);
}
/** GetMax → EqMax_ProbJoint (whole component), EqGetMax… → EqMax_ProbJoint…, other GetMax → Max_ProbJoint. */
function fixMaxProbJointName(a) {
  return String(a)
    .replace(/(^|\/)GetMax(?=\/|$)/g, "$1EqMax_ProbJoint")
    .replace(/EqGetMax/g, "EqMax_ProbJoint")
    .replace(/GetMax/g, "Max_ProbJoint");
}
/** Names of functions `s` with a hypothesis `∀ …, s … = (ℙ(joint) : ℝ).log`. */
function logProbJointFnNames(typeNodes) {
  const out = new Set();
  for (const t of typeNodes) {
    let u = stripStmt(t);
    while (cls(u) === "Lean_forall") u = stripStmt(u.args[u.args.length - 1]);
    if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) continue;
    const lhs = unwrapParen(u.args[0]);
    const head = cls(lhs) === "LeanArgsSpaceSeparated" ? lhs.args?.[0] : null;
    if (cls(head) === "LeanToken" && isBvarProbJoint(u.args[1], true)) out.add(head.text);
  }
  return out;
}
/**
 * Hypothesis `∀ t a, x t a = max[«y.bvar» : Fin t → Y] s t (…)` where `s` is the log joint probability
 * (another hypothesis `s t «y.bvar» = (ℙ(joint) : ℝ).log`): reads `All_Eq_Max` (not `All_Eq_GetMaxH`; `All_Eq_Max_LogProbJoint` stays accepted).
 * Returns { name, extras } (extras: accepted spellings that leave the Log implicit) or null.
 */
function maxLogProbJointGiven(typeNode, fns) {
  if (!fns || !fns.size) return null;
  let u = stripStmt(typeNode);
  let all = false;
  if (cls(u) === "Lean_forall") {
    if (u.superscript === "ᵐ" || hasBvarBinder(u)) return null;
    all = true;
    u = stripStmt(u.args[u.args.length - 1]);
  }
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return null;
  const ops = maxBvarOperands(u.args[1]);
  if (!ops || !ops.length || cls(ops[0]) !== "LeanToken" || !fns.has(ops[0].text)) return null;
  const A = all ? "All_" : "";
  return { name: A + "Eq_Max", extras: uniq([A + "Eq_Max_LogProbJoint", A + "Eq_Max_ProbJoint", "Eq_Max", "Eq_Max_LogProbJoint", "Eq_Max_ProbJoint"]) };
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

/**
 * `∀ t («s.bvar» : ℕ → S), V t («s.bvar» t) = …`: a plain `∀` (no `ᵐ`, no reference measure) that binds an
 * ordinary variable (t) next to the `«…bvar»` ones is a genuine universal statement, so it keeps the `All_` tag
 * (Random/…/of/All_Eq_Expect/All_Eq_Expect/In_Ico, cf. All_Lt0ProbJoint); a lone `∀ «y.bvar»,` stays implicit.
 * Probability log bodies prefer `All_Eq_LogProbCond` via bvarAllEqLogProbCondName (DiscreteHMM of-atoms);
 * this helper only tags non-ℙ bodies (expectations, …).
 */
function isMixedBvarForall(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_forall" || u.superscript === "ᵐ" || !hasBvarBinder(u)) return false;
  let measure = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || measure) return;
    const c = cls(n);
    if (c === "Lean_partial" || c === "LeanPartial" || (c === "LeanToken" && (n.text === "ReferenceMeasure" || n.text === "measure"))) { measure = true; return; }
    for (const a of n.args || []) walk(a);
  })(u.args?.[0]);
  if (measure) return false;
  let prob = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || prob) return;
    if (matchProbApp(n)) { prob = true; return; }
    for (const a of n.args || []) walk(a);
  })(u.args?.[u.args.length - 1]);
  if (prob) return false;
  const items = (u.args || []).slice(0, -1).flatMap((b) => (cls(b) === "LeanArgsSpaceSeparated" ? b.args || [] : [b]));
  const hasBvar = (n) => { let f = false; (function w(x) { if (!x || typeof x !== "object" || f) return; if (isBvarQuotation(x)) { f = true; return; } for (const c of x.args || []) w(c); })(n); return f; };
  return items.some((b) => !hasBvar(b));
}

const MIRROR_REL = { Lt: "Gt", Gt: "Lt", Le: "Ge", Ge: "Le" };
/** `0 < _` → Gt_0, `1 ≤ _` → Ge_1 (literal on the left, hole on the right). */
function mirroredFocus(tag, left) {
  return MIRROR_REL[tag] && /^-?\d+$/.test(left) ? snakeFocus(MIRROR_REL[tag], left) : "";
}

const GUARD_REL = new Set(["Lean_lt", "Lean_gt", "Lean_le", "Lean_ge", "Lean_in", "LeanIn", "Lean_notin"]);

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

function splitTopConjunction(node, flattenRight = false) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n || cls(n) !== "Lean_land") return null;
  const [left, right] = n.args || [];
  if (!left || !right) return null;
  const leftParts = splitTopConjunction(left, flattenRight);
  // Default: only flatten left (historic). `flattenRight` also splits right-nested
  // `A ∧ (B ∧ C)` — used only for pure equation conjunctions (see implyAltsOf).
  if (!flattenRight) return [...(leftParts || [left]), right];
  const rightParts = splitTopConjunction(right, flattenRight);
  return [...(leftParts || [left]), ...(rightParts || [right])];
}


/**
 * Identifiers introduced only in the imply block (`let x' := …`, named `have h := …`)
 * must not appear as path tokens (Body). Treat them as binder leaves — same as
 * signature braces (`{e x' : …}` on the Viterbi sibling). Nested binders inside
 * the let/have value are still walked.
 */
function collectImplyIntroducedIdents(node, out = new Set()) {
  if (!node || typeof node !== "object") return out;
  const c = cls(node);
  if (c === "Lean_let" || c === "Lean_have") {
    const head = node.args?.[0];
    let binder = null;
    if (cls(head) === "LeanAssign") {
      const lhs = head.args?.[0];
      binder = cls(lhs) === "LeanColon" ? lhs.args?.[0] : lhs;
    } else if (cls(head) === "LeanColon") {
      binder = head.args?.[0];
    } else if (cls(head) === "LeanToken") {
      binder = head;
    }
    for (const t of cls(binder) === "LeanToken" ? [binder]
      : cls(binder) === "LeanArgsSpaceSeparated" ? binder.args || []
      : []) {
      if (cls(t) === "LeanToken" && t.text && t.text !== "_") out.add(t.text);
    }
  }
  for (const a of node.args || []) collectImplyIntroducedIdents(a, out);
  return out;
}

/** Top-level imply conjunct that is an equation (A = B), after statement wrappers. */
function isEqConjunct(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  return cls(n) === "LeanEq";
}

function firstConclusion(node) {
  const args = node?.args || [];
  const meaningful = args.filter((a) => {
    const c = cls(a);
    return c && c !== "LeanLineComment" && c !== "Lean_have" && c !== "Lean_let";
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
  if (isSupLtInfty(node) || isBddAboveSup(node)) return "GtInftySup";
  if (isCoeAscription(node)) return "Coe" + nameExpr(node.args[0], opts);

  // Local `have` / `let` in imply is scaffolding — never a path atom.
  // `let`-bound names are also binder leaves (collectImplyIntroducedIdents).
  if (name === "Lean_have" || name === "Lean_let") return "";
  if (isBvarQuotation(node)) return "";
  // Grad of body: binder / point omitted
  {
    const gb = gradientBody(node);
    if (gb) {
      if (isExpectDotPowId(gb)) return "GradExpectDotPow_Id";
      const y = nameExpr(gb, opts);
      if (!y) return "Grad";
      // Fuse Grad + ExpectAdd -> GradExpectAdd (not GradExpect_Add)
      if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
        return "Grad" + y;
      }
      return joinHeadChild("Grad", y);
    }
  }

  // prefer CondIndep_Joint / IndepJoint / Indep_Joint over bare CondIndep / Indep
  if (indepAtom(node)) return indepJointAlt(node) || indepAtom(node);

  // ℙ[π](E) / ℙ[π](E | C) → Prob / ProbS / ProbCond*
  {
    const probName = nameProbApp(node);
    if (probName) {
      const ev = matchProbApp(node);
      return probName === "ProbS" && ev && isProbJointEvent(ev) ? "ProbJoint" : probName;
    }
  }

  if (name === "LeanStatements" || name === "LeanArgsNewLineSeparated") {
    return nameExpr(firstConclusion(node), opts);
  }

  if (CLASS_TOKEN[name]) {
    // Arith ops stay Camel (DivLeftRight) / Prob idioms — not Left/div/Right paths.
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanMatMul"]);
    if (!ARITH.has(name)) {
    const tag = CLASS_TOKEN[name];
    const args = node.args || [];
    if (name === "Lean_exists" && node.unique) {
      const core = nameExpr(existsRestConjunct(node) || args[args.length - 1], opts);
      return core ? core + "/Unique" : "Unique";
    }
    if (name === "Lean_exists" || name === "Lean_forall") {
      const bodyNode = name === "Lean_forall" ? peelGuardForalls(args[args.length - 1]) : args[args.length - 1];
      const body = nameExpr(bodyNode, opts);
      if (!body) return tag;
      // `∀ᵐ ω, HasSum ∧ ‖ExtDot…‖ ≤ bound` → All_And_LeNormExt… (drop HasSum; bound not spelled)
      if (isAeQuantifier(node) && !isMixedBvarForall(node) && node.superscript === "ᵐ") {
        const andLe = aeAndLeNormExtName(bodyNode, opts);
        if (andLe) return andLe;
        // ∀ᵐ ω, ∀ k, ‖r k ω‖ ≤ |R| → All_LeNorm_Abs (not AeNorm/le/AbsR)
        if (body === "LeNorm_Abs") return "All_LeNorm_Abs";
        if (/^All_LeNorm/.test(body)) return body;
        // ∀ᵐ ω, GradLogProbCond = GradLogProb → Ae_EqGradLogProbCond (not AeGradLogProbCond/eq/GradLogProb)
        const eqAtom = aeEqAtom(body);
        if (eqAtom) return eqAtom;
        return "Ae" + body;
      }
      if (isAeQuantifier(node) && !isMixedBvarForall(node)) return body;
      const rest = existsRestConjunct(node);
      const multi = ""; // `∀ x y` is usually spelled All (Iterates/Any_Ge_0AndAll_LeNormSub_MulNormSub); All_All kept as alternative
      // ∃ C, 0 ≤ C ∧ Q → Any_Ge_0AndQ, relations inline (Any_Ge_0AndAll_LeNormSub_MulNormSub)
      if (guardRestConjunct(args[args.length - 1]) && name === "Lean_exists") { const g = nameExpr(args[args.length - 1], { ...opts, asGiven: true }); if (g && !g.includes("/")) return tag + "_" + g; }
      if (rest) {
        const restName = nameExpr(rest, opts);
        if (restName) return tag + "_And_" + restName;
      }
      if (!body.includes("/") && /^Eq/.test(body)) return multi + tag + "_" + body; // ∀ i, f i = g i → All_Eq
      // `∀ t, τ ≤ t → P t` with a named bound τ keeps the implication (Matrix/All_Imp_LeNorm/…/ForwardSolvesCriticEquation);
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
    const arityRange = sumRangeArityName(node, opts);
    if (arityRange) return arityRange;
    const dom = sumDomainName(node);
    // interval: keep SumIcc; imply `range` stays bare Sum (AbsSum/le/Sum_Abs)
    const keepDom = dom && /^I[co][co]$/.test(dom);
    const tag = (node.superscript === "'" ? "TSum" : "Sum") + (keepDom ? dom : "");
    const args = node.args || [];
    const body = nameExpr(args[args.length - 1], opts);
    return body ? tag + "_" + body : tag;
  }
  // LeanStack: operator "Stack". Matrix ofFun = comma-of-two-lt (matrixFinBinders);
  // Tensor = single lt / nested Stack — never name binders as LtI.
  if (name === "LeanStack") {
    const scope = peelEntryStmt(node.scope ?? node.args?.[1]);
    if (matrixFinBindersOf(node) && isMulSumMulPowSubEntry(scope)) return "Stack_Mul_Sum_Mul_Pow_Sub";
    const body = nameExpr(scope, opts);
    return body ? "Stack_" + body : "Stack";
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
    if (cls(unwrapParen(arg)) === "LeanSub") {
      // |a - (∑)/card| → AbsSub_Div_Sum (keep mean Div_Sum; never AbsSub alone for that shape)
      const subR = nameExpr(unwrapParen(arg).args?.[1], opts);
      if (subR && /^Div_Sum/.test(subR)) return wrapPrefix + "Sub_" + subR;
      return wrapPrefix + "Sub";
    }
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
    // ‖x + y‖ → NormAdd; |R| / |M.env.R| → AbsR (simple id glued); ‖ExtDot…‖ → NormExtDot…
    if (!inner) return wrapPrefix;
    const u = unwrapParen(arg);
    if (CLASS_TOKEN[cls(u)] || isSimpleArg(arg, opts) || /^(Ext|Get)[A-Z]/.test(inner)) return wrapPrefix + inner;
    return wrapPrefix + "_" + inner;
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
    // Bare-token or module-path receiver (ns.f / A.B.C) -> prop only; structured value -> PropReceiver.
    // Without the module-path case, `ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule` became
    // `KwF4gRRTateChainRuleKwF4gRRTate` (prop + parent-ns).
    const obj = node.args?.[0];
    const prop = node.args?.[1];
    const propName = cls(prop) === "LeanToken" ? nameToken(prop.text || "") || nameExpr(prop, opts) : nameExpr(prop, opts);
    if (cls(obj) === "LeanToken" || isModulePathReceiver(obj)) return propName || "";
    const objName = nameExpr(obj, opts);
    if (objName && propName) return propName + objName;
    return propName || objName || "";
  }
  if (name === "LeanParenthesis" || name === "LeanAngleBracket") return nameExpr(node.args?.[0], opts);
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
    const mj = measurableJointName(node);
    if (mj) return mj; // Measurable (r, a, s) → MeasurableJoint (joint_rv)
    // deriv^[n] f y → DerivN (drop hole args; never ExtIterateDerivN)
    {
      const dn = derivPowAppName(node);
      if (dn) return dn;
    }
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
    // max⁻¹[i] e / min⁻¹[i] e → ArgMax / ArgMin (never GetArgMaxProbCond; body is a separate segment)
    {
      const am = argMaxMinTokenName(args[0]);
      if (am && isArgMaxMinGetElem(args[0])) return am;
    }
    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headName = nameExpr(head, opts);
      if (headName) {
        const pref = applyEvalPrefix(head);
        let acc = pref ? joinHeadChild(pref, headName) : headName;
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
        // Integrable ((γ ^ id) @ r[t:]) → IntegrableDotPow_Id (op compound glued; not Integrable_DotPow_Id)
        if (!isSimpleArg(argNode, opts)) {
          if (ARITH_OP.has(cls(unwrapParen(argNode)))) return joinHeadChild(headName, arg);
          return headName + "_" + arg;
        }
        return headName + arg;
      }
      if (headName && argNames.length === 0) return headName;
      if (headName && argNames.length > 1) return headName + "_" + argNames.reduce(joinDigits);
    }
    // Head was a hole (leaf GetElem / binder): drop bare fun args so
    // s[t] angle fun stays a hole and (...).exp -> Exp (not ExpFun / ExpH).
    const named = args
      .map((a) => [a, nameExpr(a, opts)])
      .filter(([a, n]) => n && !(n === "Fun" && isBareFunNode(a)))
      .map(([, n]) => n);
    if (named.length === 0) return "";
    if (named.length === 1) return named[0];
    return named.join("");
  }
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ") || name === "LeanMatMul") {
    if (name === "LeanMul" && isMulSub1DotFunDotPowRange(node)) return "MulSub1_Dot_FunDotPow_Range";
    if (name === "LeanMul" && isMulSub1FunPowDot(node)) return "MulSub1_FunPowDot";
    if (name === "LeanMatMul" && isDotFunDotPowRangeApp(node)) return "Dot_FunDotPow_Range";
    if (name === "LeanMatMul" && isFunPowDotApp(node)) return "FunPowDot";
    if (name === "LeanMatMul" && isDotPowRangeApp(node)) return "DotPow_Range";
    if (name === "LeanMatMul" && isDotPowIdApp(node)) return "DotPow_Id";
    let tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    // deriv^[n] → DerivN (not IterateDerivN); second derivative f'' is Deriv2
    if (name === "LeanPow") {
      const dn = derivPowName(node);
      if (dn) return dn;
    }
    if (name === "LeanPow" && cls(args[1]) === "LeanBracket") tag = "Iterate";
    if (name === "LeanNeg") {
      const body = nameExpr(args[0], opts);
      return body ? "Neg" + body : "Neg";
    }
    if (name === "LeanMul") {
      const mulProd = mulProbProdProbCondName(node);
      if (mulProd) return mulProd;
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
    if (name === "LeanDiv") {
      const divMul = divMulProbProdProbCondName(node);
      if (divMul) return divMul;
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
    // mean `(∑ …) / card` → Div_Sum (Sum/card); never bare Sum in SquareSub_Div_Sum / LeAbsSSub_Div_Sum
    if (name === "LeanDiv" && left && /^(Sum|TSum)/.test(left) && (!right || /^Card/.test(right))) {
      return "Div_" + left;
    }
    // Pow (Sub …) (Mul …) → PowSub__Mul (binary Pow args split by `__`; never flat PowSubMul / PowSub_Mul)
    if (name === "LeanPow" && left && right
        && ARITH_OP.has(cls(unwrapParen(args[0]))) && ARITH_OP.has(cls(unwrapParen(args[1])))) {
      return tag + left + "__" + right;
    }
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
  // if h : P then A else B (dite): skip the proof binder/condition -- only then/else are path-relevant.
  if (name === "LeanIte") {
    const args = node.args || [];
    const start = cls(args[0]) === "LeanColon" ? 1 : 0;
    for (let i = start; i < args.length; i++) {
      const n = nameExpr(args[i], opts);
      if (n) return n;
    }
    return "";
  }
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return "Prob";
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "∇") return "Grad";
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

/**
 * Join an `All`/`Any` tag to a body spelling.
 * Equality atoms keep the underscore (`All_Eq`, `All_Eq_Joint`); never camel `AllEq` / `AllEqJoint`.
 * Other bodies still allow camel beside snake (`AllOr` / `All_Or`).
 */
function withQuantTag(tag, body) {
  const snaked = tag + "_" + body;
  if (/^Eq/.test(body)) return [snaked];
  return [snaked, tag + body];
}

/** Legacy camel `EqJoint` / `All_EqJoint` (accepted by altMatch, not suggested). */
function legacyEqJointAlts(alts) {
  const out = [];
  for (const a of alts) {
    if (a === "Eq_Joint") out.push("EqJoint");
    if (a === "All_Eq_Joint") out.push("All_EqJoint");
  }
  return uniq(out);
}

function nameExprAltsBase(node, opts = {}) {
  if (!node) return [];
  const name = cls(node);
  if (isCoeAscription(node)) {
    const inner = nameExprAlts(node.args[0], opts);
    return inner.length ? uniq(inner.map((x) => "Coe" + x)) : ["Coe"];
  }

  if (name === "Lean_have" || name === "Lean_let" || isBvarQuotation(node)) return [];
  {
    const gb = gradientBody(node);
    if (gb) {
      if (isExpectDotPowId(gb)) return uniq(["GradExpectDotPow_Id", "GradExpect_DotPow_Id", "GradExpect"]);
      const x = nameExprAlts(gb, opts);
      const ranked = [];
      for (const y of x) {
        ranked.push("Grad" + y);
        if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
          ranked.push("GradExpect_" + y.slice("Expect".length)); // legacy snake
        }
        ranked.push("Grad_" + y);
      }
      return ranked.length ? uniq(ranked) : ["Grad"];
    }
  }

  if (indepAtom(node)) {
    const base = indepAtom(node);
    const joint = indepJointAlt(node);
    // joint first (CondIndep_Joint / Indep_Joint); never camel CondIndepJoint for a right joint
    return joint && joint !== base ? [joint, base] : [base];
  }
  {
    const mj = measurableJointName(node);
    if (mj) return uniq([mj, mj.replace(/Joint$/, "")]); // MeasurableJoint + Measurable
  }

  // ℙ[π](E) probability idioms. A top-level RV tuple is a joint the same way `∧` is,
  // but only as an extra spelling: the `∧`-only name stays canonical.
  const probName = nameProbApp(node);
  if (probName) {
    // Body: bvar-slice or point-and-slice Lean_land joint → ProbJoint (not ProbS).
    // Keep ProbJointGetSliceS as alt for two-slice joints; demote ProbS for remigration.
    const ev = matchProbApp(node);
    const joint = probName === "ProbS" && ev && isProbJointEvent(ev);
    const base = joint
      ? (isBvarSliceJointEvent(ev) ? ["ProbJoint", "ProbJointGetSliceS"] : ["ProbJoint"])
      : [probName];
    const withTuples = ev ? probEventName(ev, true) : "";
    return withTuples && withTuples !== probName ? uniq([...base, withTuples]) : base;
  }

  if (name === "LeanStatements" || name === "LeanArgsNewLineSeparated") {
    return nameExprAlts(firstConclusion(node), opts);
  }

  if (CLASS_TOKEN[name]) {
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanMatMul"]);
    if (!ARITH.has(name)) {
      const tag = CLASS_TOKEN[name];
      const args = node.args || [];
      if (name === "Lean_exists" && node.unique) {
        const core = nameExprAlts(existsRestConjunct(node) || args[args.length - 1], opts);
        return core.length ? uniq(core.map((c) => c + "/Unique")) : ["Unique"];
      }
      if (name === "Lean_exists" || name === "Lean_forall") {
        const bodyNode = name === "Lean_forall" ? peelGuardForalls(args[args.length - 1]) : args[args.length - 1];
        const bodyAlts = nameExprAlts(bodyNode, opts);
        const rest = existsRestConjunct(node);
        const guardAlts = rest ? nameExprAlts(rest, opts).map((r) => tag + "_And_" + r) : [];
        if (!bodyAlts.length) return uniq([...guardAlts, tag]);
        if (isAeQuantifier(node) && !isMixedBvarForall(node)) {
          // `∀ᵐ x ∂μ, P` → AeP preferred (AeTendsto, AeAll_…); All_P / bare P kept (Random/All_Summable)
          // HasSum ∧ ‖ExtDot…‖ ≤ bound → All_And_LeNormExt… ranked first
          // ∀ᵐ ω, ∀ k, ‖r…‖ ≤ |R| → All_LeNorm_Abs ranked first (not AeNorm/le/AbsR)
          // ∀ᵐ ω, L = R → Ae_EqL preferred (All_Ae_EqGradLogProbCond under ∀t); AeL/eq/R kept lower
          const andLe = node.superscript === "ᵐ" ? aeAndLeNormExtName(bodyNode, opts) : "";
          const leNormAbs = node.superscript === "ᵐ" && bodyAlts.some((b) => b === "LeNorm_Abs" || b === "All_LeNorm_Abs")
            ? ["All_LeNorm_Abs"]
            : [];
          const eqAtoms = node.superscript === "ᵐ"
            ? bodyAlts.map(aeEqAtom).filter(Boolean)
            : [];
          const aeAlts = node.superscript === "ᵐ"
            ? [...(andLe ? [andLe] : []), ...leNormAbs, ...eqAtoms, ...bodyAlts.map((b) => "Ae" + b), ...bodyAlts.map((b) => tag + "_" + b), ...bodyAlts, ...guardAlts]
            : [...bodyAlts, ...guardAlts];
          return uniq(aeAlts);
        }
        if (quantArity(node) >= 2 && !node.__singleQuant) {
          node.__singleQuant = true;
          let single;
          try { single = nameExprAlts(node, opts); } finally { delete node.__singleQuant; }
          // `∀ x y, P` → All_All_P (distinct from `∀ x, P`); Eq* → All_All_Eq (never All_AllEq)
          const inner = nameExprAlts(bodyNode, opts);
          const tagged = inner.filter((b) => !b.includes("/")).flatMap((b) => withQuantTag(tag + "_" + tag, b));
          const rel = inner.filter((b) => b.includes("/") || /^(Prob|DivProb|MulProb)/.test(b));
          return uniq([...single.slice(0, 300), ...tagged.slice(0, 300), ...single.slice(300), ...rel, ...guardAlts, ...tagged.slice(300)]);
        }
        if (bodyAlts.some(b => b.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(b))) {
          // `∀ i ∈ s, f i = g i` → All_Eq (Finset/Sum/of/All_Eq, Kernel/All_Eq); never AllEq
          const eqT = bodyAlts.filter((b) => !b.includes("/") && /^Eq/.test(b)).flatMap((b) => withQuantTag(tag, b));
          // relational bodies usually read `A/eq/B`; a one-atom rendering may still take the tag (All_AeLeCondExp)
          const tagged = bodyAlts.filter((b) => !b.includes("/")).flatMap((b) => withQuantTag(tag, b));
          return uniq([...eqT, ...tagged.slice(0, 200), ...bodyAlts, ...guardAlts, ...tagged.slice(200)]);
        }
        const out = [];
        for (const b of bodyAlts) out.push(...withQuantTag(tag, b));
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
    const arityRange = sumRangeArityName(node, opts);
    const dom = sumDomainName(node);
    const keepDom = dom && /^I[co][co]$/.test(dom);
    const tag = (node.superscript === "'" ? "TSum" : "Sum") + (keepDom ? dom : "");
    const args = node.args || [];
    const bodyAlts = nameExprAlts(args[args.length - 1], opts);
    const base = !bodyAlts.length ? [tag] : bodyAlts.flatMap((b) => [tag + "_" + b, tag + b]);
    return uniq(arityRange ? [arityRange, ...base] : base);
  }
  // LeanStack → Stack_… (Matrix Fin sugar / Tensor); never LtI from binders
  if (name === "LeanStack") {
    const scope = peelEntryStmt(node.scope ?? node.args?.[1]);
    if (matrixFinBindersOf(node) && isMulSumMulPowSubEntry(scope)) {
      return uniq(["Stack_Mul_Sum_Mul_Pow_Sub", "Stack"]);
    }
    const bodyAlts = nameExprAlts(scope, opts);
    if (!bodyAlts.length) return ["Stack"];
    return uniq(bodyAlts.flatMap((b) => ["Stack_" + b, "Stack" + b]).concat(["Stack"]));
  }

  // Wrapper ops: Norm, Abs, Ceil, Floor
  const WRAP_OP_PREFIX = { LeanNorm: "Norm", LeanAbs: "Abs", LeanCeil: "Ceil", LeanFloor: "Floor" };
  const wrapPrefix = WRAP_OP_PREFIX[name];
  if (wrapPrefix !== undefined) {
    const arg = node.args?.[0];
    if (cls(unwrapParen(arg)) === "LeanSub") {
      const subRAlts = nameExprAlts(unwrapParen(arg).args?.[1], opts);
      const withDiv = subRAlts.filter((r) => /^Div_Sum/.test(r)).map((r) => wrapPrefix + "Sub_" + r);
      return uniq([...withDiv, wrapPrefix + "Sub"]);
    }
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
    // |R| / |M.env.R| (token / property): AbsR only — never Abs_R
    if (isSimpleArg(arg, opts)) return uniq(innerAlts.map((i) => wrapPrefix + i));
    const out = [];
    for (const i of innerAlts) {
      out.push(wrapPrefix + i);
      out.push(wrapPrefix + "_" + i);
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
    // Module-path receivers match bare-token: last segment only (no Prop+ParentNs glue).
    if (cls(obj) === "LeanToken" || isModulePathReceiver(obj)) return propAlts;
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

  if (name === "LeanParenthesis" || name === "LeanAngleBracket") return nameExprAlts(node.args?.[0], opts);

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
    const mj = measurableJointName(node);
    if (mj) return uniq([mj, mj.replace(/Joint$/, "")]);
    {
      const dn = derivPowAppName(node);
      if (dn) return [dn];
    }
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
    // max⁻¹[i] e / min⁻¹[i] e → ArgMax / ArgMin only (never GetArgMaxProbCond / ArgMaxProbCond fuse)
    {
      const am = argMaxMinTokenName(args[0]);
      if (am && isArgMaxMinGetElem(args[0])) return [am];
    }

    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headAlts = nameExprAlts(head, opts);
      if (headAlts.length) {
        const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
        const pref = applyEvalPrefix(head);
        let acc = pref ? cartJoin([pref], headAlts, joinHeadChild) : headAlts.slice();
        // applied power `(κ ^ n) s` may read without Get/Ext: PowKernelMat
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

    // Generic: cartesian product of all arg alts (drop bare Fun on hole-head apps)
    const argAltLists = args
      .map((a) => [a, nameExprAlts(a, opts).filter((n) => !(n === "Fun" && isBareFunNode(a)))])
      .map(([, alts]) => alts)
      .filter((a) => a.length);
    if (!argAltLists.length) return [];
    if (argAltLists.length === 1) return argAltLists[0];
    let acc = argAltLists[0];
    for (let i = 1; i < argAltLists.length; i++) {
      acc = cartJoin(acc, argAltLists[i], (a, b) => a + b);
    }
    return uniq(acc);
  }

  // Arithmetic ops: Sub, Add, Mul, Div, Pow, Neg
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ") || name === "LeanMatMul") {
    if (name === "LeanMul" && isMulSub1DotFunDotPowRange(node)) {
      return uniq(["MulSub1_Dot_FunDotPow_Range", "MulSub1_FunPowDot", "MulSub1FunPowDot", "MulSub1_DotFunPow"]);
    }
    if (name === "LeanMul" && isMulSub1FunPowDot(node)) {
      return uniq(["MulSub1_FunPowDot", "MulSub1FunPowDot", "MulSub1_DotFunPow"]);
    }
    if (name === "LeanMatMul" && isDotFunDotPowRangeApp(node)) {
      return uniq(["Dot_FunDotPow_Range", "FunPowDot", "DotPow_Id", "Dot"]);
    }
    if (name === "LeanMatMul" && isFunPowDotApp(node)) {
      return uniq(["FunPowDot", "DotPow_Id", "Dot"]);
    }
    if (name === "LeanMatMul" && isDotPowRangeApp(node)) {
      return uniq(["DotPow_Range", "Dot"]);
    }
    if (name === "LeanMatMul" && isDotPowIdApp(node)) {
      return uniq(["DotPow_Id", "Dot"]);
    }
    let tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanPow") {
      const dn = derivPowName(node);
      if (dn) return [dn];
    }
    if (name === "LeanPow" && cls(args[1]) === "LeanBracket") tag = "Iterate";
    if (name === "LeanNeg") {
      const bodyAlts = nameExprAlts(args[0], opts);
      if (!bodyAlts.length) return ["Neg"];
      return bodyAlts.map(b => "Neg" + b);
    }
    if (name === "LeanMul") {
      const mulProd = mulProbProdProbCondName(node);
      if (mulProd) return [mulProd];
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
    if (name === "LeanDiv") {
      const divMul = divMulProbProdProbCondName(node);
      if (divMul) return [divMul];
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
    // mean (∑)/card → Div_Sum preferred (SquareSub_Div_Sum / LeAbsSSub_Div_Sum)
    if (name === "LeanDiv") {
      for (const l of leftAlts) {
        if (!l || !/^(Sum|TSum)/.test(l)) continue;
        if (!rightAlts.length || rightAlts.some((r) => !r || /^Card/.test(r))) out.push("Div_" + l);
      }
    }
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
    const powBinArith = name === "LeanPow"
      && ARITH_OP.has(cls(unwrapParen(args[0]))) && ARITH_OP.has(cls(unwrapParen(args[1])));
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
          // Pow(Sub, Mul) → PowSub__Mul first; do not treat PowSubMul / PowSub_Mul as peers
          if (powBinArith) {
            out.push(tag + l + "__" + r);
            continue;
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
    // `@` (Dot.dot) operands are vectors/matrices whose spelling may be omitted, so these come first (node caps):
    // (γ ^ id) @ r[t:] → Dot, (γ ^ id) @ fun k => 𝔼[…](… | …) → Dot_Expect_Cond (Random/Expect_CondDot/eq/Dot_Expect_Cond/of/In_Ico)
    // the `@` itself may also stay implicit, naming its first operand (Random/CondExpPow_Id/of/In_Ico)
    if (name === "LeanMatMul") {
      // same operand on both sides still first (DotDotSRotaryMatrix), then the omissions, then the implicit-`@` spelling
      // (kept near the front: the identity pairs of `=ᵐ` / `=` combine them under node caps), then the rest
      const same = [];
      for (const l of leftAlts) if (l && rightSet.has(l)) same.push(...(pluralSnakeS(l) ? [tag + pluralSnakeS(l)] : []), tag + pluralMidS(l), ...(pluralLetterS(l) ? [tag + pluralLetterS(l)] : []), tag + sameChildS(l));
      if (!leftAlts.length) return uniq([...out, ...rightAlts]);
      const omit = [];
      for (const r of rightAlts) omit.push(tag + "_" + r, tag + r);
      omit.push(tag);
      return uniq([...same, ...omit, ...leftAlts, ...out]);
    }
    return uniq(out);
  }

  if (name === "Lean_bullet") {
    return ["SMul"];
  }

  if (name === "LeanDoubleAngleQuotation") return [];
  if (name === "LeanIte") {
    const args = node.args || [];
    const start = cls(args[0]) === "LeanColon" ? 1 : 0;
    for (let i = start; i < args.length; i++) {
      const alts = nameExprAlts(args[i], opts);
      if (alts.length) return alts;
    }
    return [];
  }
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return ["Prob"];
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "∇") return ["Grad"];
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
      if (cls(n) === "LeanToken" && n.text === "path") return true;
      return Array.isArray(n.args) && n.args.some(walk);
    };
    return walk(a);
  });
}

function extractLemmas(ast) { return (ast.args || []).filter((a) => cls(a) === "Lean_lemma" || cls(a) === "Lean_theorem"); }
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
  // Colon after `-- imply` comment leaves the conclusion as a bare expr under LeanColon
  // (not LeanStatements). Without this, imply falls back to "Imply" and paths become
  // Imply.of.Ne*_0 for trig Mul_/… lemmas (e.g. Cos/eq/Mul_/Sin/Cot.lean).
  let implyStmts = (colon.args || []).find((a) => cls(a) === "LeanStatements");
  if (!implyStmts) {
    const bare = (colon.args || []).find((a) => {
      const c = cls(a);
      return c && c !== "LeanArgsIndented" && c !== "LeanArgsSpaceSeparated" && c !== "LeanLineComment";
    });
    if (bare) implyStmts = bare;
  }
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
  const at = source.indexOf("@[path]");
  const imply = source.indexOf("-- imply", at < 0 ? 0 : at);
  if (imply < 0) return source;
  const m = /:=(\s|$)/.exec(source.slice(imply));
  if (!m) return source;
  return source.slice(0, imply + m.index) + ":= by\n  sorry\n";
}
/**
 * When the full file fails to parse (e.g. `noncomputable section` in P2M ports), keep only the
 * `@[path]` lemma with a sorry proof so naming can still run.
 */
function extractPathLemmaSource(source) {
  const at = source.indexOf("@[path]");
  if (at < 0) return null;
  let body = source.slice(at);
  const imply = body.indexOf("-- imply");
  if (imply >= 0) {
    const m = /:=(\s|$)/.exec(body.slice(imply));
    if (m) body = body.slice(0, imply + m.index) + ":= by\n  sorry\n";
  }
  return "import Mathlib\n\n" + body;
}

function compileLemmaSource(source) {
  // Prefer @[path]-only extract when the file has P2M `noncomputable section` blocks:
  // full-file compile can hang/fail on those, and naming only needs the path lemma.
  const attempts = [];
  const mini = extractPathLemmaSource(source);
  if (mini && /\bnoncomputable\s+section\b/.test(source)) attempts.push(mini);
  attempts.push(source);
  const cut = truncateMainProof(source);
  if (cut !== source) attempts.push(cut);
  if (mini && !attempts.includes(mini)) attempts.push(mini);
  let lastErr;
  for (const src of attempts) {
    try {
      return compile(src);
    } catch (e) {
      lastErr = e;
    }
  }
  throw lastErr;
}

/**
 * Name imply/given path atoms from lemma source without scanning sympy / Lemma folders.
 * Focused regression tests use this (full `suggest` walks ~10k sympy files).
 */
export function namePathAtoms(source) {
  const ast = compileLemmaSource(source);
  const lemma = extractLemma(ast);
  if (!lemma) throw new Error("No Lean_lemma found");
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  for (const r of new Set([sig.indented, sig.nls, sig.implyStmts])) reassociateDotProduct(r);
  const leaves = collectLeafBinders(sig.indented);
  collectLeafBinders(sig.implyStmts, leaves, true);
  collectImplyIntroducedIdents(sig.implyStmts, leaves);
  {
    const bundles = bundleVars(sig.indented);
    for (const r of new Set([sig.nls, sig.implyStmts])) holeBundleProjections(r, bundles, leaves);
  }
  const nameOpts = { leaves, typeLeaves: collectTypeBinders(sig.indented) };
  const imply = nameExpr(sig.implyStmts, nameOpts);
  const givens = extractGivens(sig.nls).filter((h) => h.prop).map((h) => ({
    binder: h.name,
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }),
  }));
  return { imply, givens };
}

/**
 * Definitions files that declare structure / instance / capitalized def / class are not
 * Lemma/ rename candidates (AGENTS: structure/def/instance not legal in Lemma/). Refuse
 * rather than inventing a weak MvPolynomial/Nat path from an incidental lemma.
 */
function stripLeanComments(source) {
  return String(source || "")
    .replace(/\/-([\s\S]*?)-\//g, "\n")
    .replace(/--[^\n]*/g, "");
}

function isDefinitionsDeclHeavy(source) {
  const stripped = stripLeanComments(source);
  const declRe = /(?:^|\n)(?:@[^\n]*\n)*(?:(?:noncomputable|private|protected|scoped|partial|unsafe)\s+)*(?:structure|instance|class)\s+/;
  const capDefRe = /(?:^|\n)(?:@[^\n]*\n)*(?:(?:noncomputable|private|protected|scoped|partial|unsafe)\s+)*def\s+[A-Z]/;
  return declRe.test(stripped) || capDefRe.test(stripped);
}

/**
 * Multi-decl Definitions packages (2+ lemma/theorem) must not whole-dump into a path named
 * from the first incidental lemma (Ideal/Count/eq/... from Dedekind IntegralClosure).
 * Carve a single-primary lemma file first, then re-suggest.
 */
export function isDefinitionsPackage(source) {
  const stripped = stripLeanComments(source);
  const lemmaRe = /(?:^|\n)(?:@[^\n]*\n)*(?:(?:noncomputable|private|protected|scoped)\s+)*(?:lemma|theorem)\s+/g;
  return [...stripped.matchAll(lemmaRe)].length > 1;
}

function definitionsRenameRefuseReason(source) {
  if (isDefinitionsDeclHeavy(source)) {
    return "Structure/def/instance file - leave in Definitions (not a Lemma/ rename candidate)";
  }
  if (isDefinitionsPackage(source)) {
    return "Multi-decl package - leave in Definitions (carve a single primary lemma first)";
  }
  return null;
}

export function suggest(filePath, lemmaName, options = {}) {
  const abs = path.resolve(filePath);
  const source = fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const curTopEarly = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/").split("/")[0];
  if (curTopEarly === "Definitions") {
    const refuse = definitionsRenameRefuseReason(source);
    if (refuse) throw new Error(refuse);
  }
  const ast = compileLemmaSource(source);
  const lemma = extractLemma(ast, lemmaName);
  if (!lemma) throw new Error("No Lean_lemma found");
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  for (const r of new Set([sig.indented, sig.nls, sig.implyStmts])) reassociateDotProduct(r);
  const sections = existingSections();
  // sections are data types: folders named after Prop predicates / value definitions never decide the section
  const curTop = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/").split("/")[0];
  // typeclass folders (NormedSpace, …) are no data types either: they only keep the files already filed there
  // (`exp (t • Q)` with Q : Matrix … is a Matrix lemma elsewhere)
  // topic/unknown never become sections; typeclass folders only stay if this file is still filed there
  const dataSections = sections.filter((s) => {
    if (nonDataFolder(s)) return false;
    // Body 2026-10-24: these 17 are never legal (rename away; no transitional keep)
    if (ILLEGAL_SECTIONS.has(s)) return false;
    if (refusedSectionFolder(s)) return sectionKindMap().get(s) === "type class" && s === curTop;
    return !TYPECLASS_FOLDERS.has(s) || s === curTop;
  });
  const givenTypeNodes = extractGivens(sig.nls).filter((h) => h.prop).map((h) => h.typeNode);
  // …except for a file still filed under the predicate folder that names it: it is named as before (transitional,
  // until that folder is moved to its data-type section)
  const legacyCustom = nonDataFolder(curTop) ? customSection(sections, sig.implyStmts, givenTypeNodes, importSections(source, sections), sig.indented) : null;
  const legacy = !!legacyCustom && nonDataFolder(legacyCustom) && curTop === legacyCustom;
  const custom = legacy ? legacyCustom : customSection(dataSections, sig.implyStmts, givenTypeNodes, importSections(source, dataSections), sig.indented);
  const picked = pickSection(sig.colon, legacy ? sections : dataSections, {
    custom,
    // `import sympy.….vector` → +1.5 for Vector; custom folders (Iterates, …) are decided by customSection only
    imports: [
      ...[...importSections(source, sections).keys()].filter((s) => DATA_TYPE_SECTIONS.has(s) || TYPE_TO_SECTION[s]),
      ...openDataSections(source),
    ],
  });
  const section = picked.section;
  if (curTop === "Definitions" && refusedSectionFolder(section) && !(sectionKindMap().get(section) === "type class" && section === curTop)) {
    throw new Error(
      `Topic/unknown or illegal section "${section}" - leave in Definitions (not a Lemma/ rename candidate)`
    );
  }
  let relCurrent = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
  if (relCurrent.startsWith("..")) relCurrent = path.relative(REPO, abs).replace(/\\/g, "/");
  const leaves = collectLeafBinders(sig.indented);
  collectLeafBinders(sig.implyStmts, leaves, true);
  collectImplyIntroducedIdents(sig.implyStmts, leaves);
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
    // Left-only flatten is the historic default (keeps nested non-eq And intact).
    const partsLeft = splitTopConjunction(sg.implyStmts, false);
    // Full flatten only for pure equation conjunctions `A = B ∧ C = D ∧ …`
    // (Bellman); avoids OOM on Bool/Complex lemmas with deep nested And.
    const partsFull = splitTopConjunction(sg.implyStmts, true);
    const eqConj = partsFull && partsFull.length >= 2 && partsFull.length <= 6 && partsFull.every(isEqConjunct);
    const parts = eqConj ? partsFull : partsLeft;
    if (!parts || parts.length < 2) return joined;
    // `… ∧ max[«y.bvar» : …] ℙ(joint) = …`: Max is the big operator → EqMax_ProbJoint (ranked first, replaces GetMax)
    const fixJ = parts.length === 2 && isMaxProbJointEq(parts[1]) ? fixMaxProbJointName : (x) => x;
    const perConjunct = parts.map((p) => nameExprAlts(p, no).filter(Boolean));
    if (!perConjunct.every((a) => a.length)) return joined.map(fixJ);
    const splitAlts = perConjunct.reduce(
      (acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))),
      [""],
    );
    const res = uniq([...splitAlts, ...joined].map(fixJ));
    // Equation conjunction → prefer `Eq_A/Eq_B/Eq_C` over `Eq_AAndEq_BAndEq_C`.
    if (eqConj && splitAlts.length) {
      // each segment is that conjunct's canonical rendering (nameExpr) when it is among its alternatives
      const canonParts = parts.map((p, i) => {
        const c = sanitizeRelPath(nameExpr(p, no) || "");
        return perConjunct[i].find((x) => sanitizeRelPath(x) === c) || perConjunct[i][0];
      });
      // Parallel =ᵐ to 𝔼[…|…]: prefer repeated `MEq_Expect_Cond` (Bellman), not CondAdd_Mul /
      // camel `MEqExpect` / bare `MEq` — same shape as finite `Eq_Expect/Eq_Expect/Eq_Expect`.
      const meqCondParts = perConjunct.map((alts) => (alts.includes("MEq_Expect_Cond") ? "MEq_Expect_Cond" : ""));
      res.preferred = fixJ(
        meqCondParts.length >= 2 && meqCondParts.every(Boolean)
          ? meqCondParts.join("/")
          : canonParts.join("/"),
      );
      // Keep left-only partial splits accepted (older paths like Eq_Dvd/EqMapAndIsPullback).
      if (partsLeft && partsLeft.length >= 2 && partsLeft.length < partsFull.length) {
        const perL = partsLeft.map((p) => nameExprAlts(p, no).filter(Boolean));
        if (perL.every((a) => a.length)) {
          const leftSplits = perL.reduce((acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))), [""]);
          res.extra = uniq([...(res.extra || []), ...leftSplits.map(fixJ)]);
        }
      }
    }
    if (fixJ === fixMaxProbJointName) {
      // Viterbi: second conjunct → EqMax_ProbJoint (drop `eq/<rhs>`). Prefer All_Eq_Add_MaxAdd
      // (GetElem t+1 → Add_1 noise stays in extras/alts only — same idea as CRF All_Eq_AddLogSumExpAdd).
      const short2 = "EqMax_ProbJoint";
      const short = perConjunct[0].map((x) => String(x).split("/")[0] + "/" + short2);
      const bodyParallel =
        perConjunct[0].some((x) => /MaxAdd|Add_MaxAdd|AddMax/.test(x))
          ? "All_Eq_Add_MaxAdd/EqMax_ProbJoint"
          : "";
      const preferred =
        bodyParallel ||
        short.find((x) => /Add_MaxAdd|MaxAdd/.test(x) && !/Add_1|Add1/.test(x)) ||
        short[0] ||
        "";
      const full = res.slice();
      const out = uniq([
        ...(preferred ? [preferred] : []),
        ...short,
        ...full.filter((x) => !short.includes(x) && x !== preferred),
      ]);
      out.extra = uniq([...(res.extra || []), ...full, ...short]);
      out.preferred = preferred || res.preferred;
      return out;
    }
    if (isHmmNegLogCondShape(sg.implyStmts)) {
      // Body: conjunction → parallel top-level stems (All_Eq_AddLogSumExpAdd/All_EqNegLogProb),
      // not a deep NegLogProbCond.eq.SubLogSumExp… token for only the second conjunct.
      // Imply-let idents (x') are binder leaves (no X' tokens); Get-index noise (Add_1) is
      // dropped in the preferred Body stem — same idea as Viterbi All_Eq_Add_MaxAdd.
      const ex2 = hmmBvarAllAlts(perConjunct[1]);
      const short2 = "All_EqNegLogProb";
      const short = perConjunct[0].map((x) => String(x).split("/")[0] + "/" + short2);
      const bodyParallel =
        perConjunct[0].some((x) => /LogSumExp|AddLogSumExp|ExpSumLog|SumExpLog/.test(x))
          ? "All_Eq_AddLogSumExpAdd/All_EqNegLogProb"
          : "";
      const preferred = bodyParallel || short.find((x) => /AddLogSumExpAdd/.test(x)) || short[0] || "";
      const full = res.slice();
      const out = uniq([
        ...(preferred ? [preferred] : []),
        ...short,
        ...full.filter((x) => !short.includes(x) && x !== preferred),
      ]);
      out.extra = uniq([
        ...(res.extra || []),
        ...full,
        ...perConjunct[0].flatMap((x) => ex2.map((y) => x + "/" + y)),
        // deep NegLogProbCond.eq.… / X' spellings stay accepted for remigration compat
        ...short,
      ]);
      out.preferred = preferred || res.preferred;
      return out;
    }
    return res;
  };
  setRvNames(sig.indented);
  let implyAltsA = implyAltsOf(sig, nameOpts);
  // Body: Eq_SymmToDual In_Ico0 keeps the long fused LHS stem (not SymmToDual/eq/ExpectTSum_SMul).
  {
    const bodySymm = eqSymmToDualTSumBodyName(sig.implyStmts);
    if (bodySymm) {
      implyAltsA = uniq([bodySymm, ...implyAltsA]);
      implyAltsA.preferred = bodySymm;
    }
  }
  // Body: Expect of discounted Fun•∇log = ∫ Dot FunSMul ∇log
  // → ExpectDot/eq/Integral_Dot_FunSMul_GradLogProbCond
  // (not ExpectFunPowDot / Integral_Ext_FunPowDot / Integral_ExtDot).
  {
    const bodyExpectDot = expectDotEqIntegralExtDotBodyName(sig.implyStmts);
    if (bodyExpectDot) {
      implyAltsA = uniq([bodyExpectDot, ...implyAltsA]);
      implyAltsA.preferred = bodyExpectDot;
    }
  }
  // Body: Expect of ∑ (γ^t * Q) • ∇log = ∫ ∑ … • ∇log
  // → ExpectSum_SMulMulPow/eq/Integral_Sum_SMul_GradLogProbCond
  // (MulPow on ExpectSum LHS; GradLog on Integral RHS — not short SMul or fused MulPow_GradLog).
  {
    const bodyExpectSum = expectSumSMulEqIntegralSumSMulBodyName(sig.implyStmts);
    if (bodyExpectSum) {
      implyAltsA = uniq([bodyExpectSum, ...implyAltsA]);
      implyAltsA.preferred = bodyExpectSum;
    }
  }
  // Body: max⁻¹ ProbCond = max⁻¹ (Mul Prob * Prod ProbCond)
  // → ArgMax_ProbCond/eq/ArgMax_Mul_Prod_ProbCond (never GetArgMaxProbCond / ArgMaxProbCond).
  // Legacy ArgMax/eq/ArgMax and Eq/ArgMax/Mul/Prod_ProbCond stay accepted.
  {
    const bodyArgMax = argMaxEqArgMaxBodyName(sig.implyStmts);
    if (bodyArgMax) {
      implyAltsA = uniq([
        bodyArgMax,
        ARGMAX_EQ_ARGMAX,
        ARGMAX_EQ_MUL_PROD_PROBCOND,
        ...implyAltsA,
      ]);
      implyAltsA.preferred = bodyArgMax;
      implyAltsA.extra = uniq([
        ...(implyAltsA.extra || []),
        ARGMAX_EQ_ARGMAX,
        ARGMAX_EQ_MUL_PROD_PROBCOND,
      ]);
    }
  }
  // Body: ([i < n, j < n] … Mul_Sum … Pow_Sub).det = (x - l)^(d * n)
  // → DetStack_Mul_Sum_Mul_Pow_Sub/eq/PowSub__Mul (Matrix.of fun → DetOfFun…; not DetLtI / bare DetOf).
  {
    const bodyDetEntry = detMatrixEntryEqPowSubMulBodyName(sig.implyStmts);
    if (bodyDetEntry) {
      implyAltsA = uniq([bodyDetEntry, ...implyAltsA]);
      implyAltsA.preferred = bodyDetEntry;
    }
  }
  // Canonical rendering (nameExpr) first when it is among the alternatives.
  // (an alternative differing only by the ' between adjacent numbers — Neg1'0 vs Neg10 — is the canonical one)
  const undig = (x) => sanitizeRelPath(x || "").replace(/(\d)'(?=\d)/g, "$1");
  const pickCanon = (alts, preferred) =>
    alts.find((a) => sanitizeRelPath(a) === sanitizeRelPath(preferred || "")) ||
    (preferred ? alts.find((a) => /\d'\d/.test(a) && undig(a) === undig(preferred)) : null) || alts[0] || preferred;
  // Equation conjunctions: prefer slash-separated segments over And-glued nameExpr.
  const implyNameA = pickCanon(implyAltsA, implyAltsA.preferred || nameExpr(sig.implyStmts, nameOpts)) || "Imply";
  // Second pass keeping Greek / subscript letters and Greek projections (`spec.η`, `maxₐ`, `μmin`).
  const passB = (() => {
    KEEP_GREEK = true;
    try {
      const sigB = extractSignature(extractLemma(compileLemmaSource(source), lemmaName));
      for (const r of new Set([sigB.indented, sigB.nls, sigB.implyStmts])) reassociateDotProduct(r);
      const leavesB = collectLeafBinders(sigB.indented);
      collectLeafBinders(sigB.implyStmts, leavesB, true);
      collectImplyIntroducedIdents(sigB.implyStmts, leavesB);
      const bundlesB = bundleVars(sigB.indented);
      for (const r of new Set([sigB.nls, sigB.implyStmts])) holeBundleProjections(r, bundlesB, leavesB);
      const optsB = { leaves: leavesB, typeLeaves: collectTypeBinders(sigB.indented), section };
      setRvNames(sigB.indented);
      const implyAlts = implyAltsOf(sigB, optsB);
      const implyName = pickCanon(implyAlts, implyAlts.preferred || nameExpr(sigB.implyStmts, optsB)) || "Imply";
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
  // drop camel-collapsed MEqExpect* / bare MEq-in-a-chain imply folders (MEqExpectS kept; sole MEq ok);
  // drop GetArgMaxProbCond (ArgMax and ProbCond must stay separate segments);
  // drop DivMulProbProd_ProbCondProb / ProbCond__Prob (Cond is binary; den Prob stays implicit)
  const legalMeqImply = (p) => {
    if (hasIllegalGetArgMaxProbCond(p)) return false;
    if (hasIllegalDivMulProbProdCond(p)) return false;
    if (hasIllegalMeqImply(p)) return false;
    const segs = String(p).split("/").filter(Boolean);
    return !(segs.includes("MEq") && segs.length > 1);
  };
  const implyAlts = uniq([...implyAltsA, ...(passB?.implyAlts || [])]).filter(legalMeqImply);
  const implyExtraAlts = [...(implyAltsA.extra || []), ...(passB?.implyAlts?.extra || [])].filter(legalMeqImply); // accepted, not enumerated
  // lowercase ASCII components (`min/…` from a stripped `μmin`) are not names; soft relations are
  const SOFT = /^(of|is|in|sub|eq|ne|lt|gt|le|ge|dvd|ae[A-Za-z]*)$/;
  const lowerComp = (p) => sanitizeRelPath(p || "").split("/").some((c) => /^[a-z]/.test(c) && !SOFT.test(c));
  let preferB = !!passB && passB.implyName !== implyNameA && lowerComp(implyNameA) && !lowerComp(passB.implyName);
  let implyName = preferB ? passB.implyName : implyNameA;
  if (hasIllegalMeqImply(implyName) || hasIllegalGetArgMaxProbCond(implyName) || hasIllegalDivMulProbProdCond(implyName)) {
    implyName = implyAlts.find((a) => !hasIllegalMeqImply(a) && !hasIllegalGetArgMaxProbCond(a) && !hasIllegalDivMulProbProdCond(a)) || implyName;
  }
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
  // Body ExpectDot=Integral Dot FunSMul leaf: keep All_Measurable in of-tail (prefer over All_MeasurableFun);
  // Ae_GtInftySup (underscore) preferred over fused AeGtInftySup; NeProb stays Lean-h₂ (no Diff/NeProb cluster).
  const expectDotIntegralExtDotShape = isExpectDotEqIntegralExtDotShape(sig.implyStmts);
  const hyps = extractGivens(sig.nls).map((h, idx) => {
    h = { ...h, idx };
    const t = unwrapParen(h.typeNode);
    const structLike = cls(t) === "LeanToken" || (cls(t) === "LeanArgsSpaceSeparated" && cls(t.args?.[0]) === "LeanToken");
    const usedInConcl = (h.names || [h.name]).some((n) => conclTokenSet.has(n));
    // IsPolicyTrajectory / other Is* stay givens even when used as h.stage_eq in imply scaffolding
    if (h.prop && structLike && conclNames.has(h.name) && !/^Is[A-Z]/.test(typeHead(t))) return { ...h, prop: false };
    if (h.prop && structLike && dataHeads.has(typeHead(t)) && !/^Is[A-Z]/.test(typeHead(t))) return { ...h, prop: false };
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
      // so may measurability side conditions of an expectation (Random/Expect_CondDot/eq/Dot_Expect_Cond, Random/Expect_CondMul/eq/Mul_Expect_Cond)
      if (conclTokenSet.has("𝔼") && /^(AE)?(Strongly)?Measurable$/.test(typeHead(b))) {
        // joint `Measurable (r, s, a)` may be omitted from Bellman / Expect paths (kept as optional alt)
        const jn = nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "";
        if (/MeasurableJoint/.test(jn)) return { ...h, optional: true, canonSkip: true };
        // Body ExpectDot=∫Dot FunSMul GradLog: keep ∀ Measurable (fun …) as All_Measurable in of-tail
        // (optional so cart still accepts omitting it; not canonSkip).
        if (expectDotIntegralExtDotShape && /MeasurableFun|Measurable/.test(jn)) {
          return { ...h, optional: true };
        }
        return { ...h, optional: true };
      }
    }
    return h;
  });
  /** `All_MEq_Expect_CondDotPow` → `All_MEq_Expect_CondDot` when that alt exists (Bellman siblings). */
  const preferMeqExpectCondDot = (name, alts) => {
    if (!name || !/MEq.*CondDotPow/.test(name)) return name;
    const short = name.replace(/CondDotPow/g, "CondDot");
    return alts.includes(short) ? short : name;
  };
  // Generate ALL given name alternatives (reverse order for path); pass-B (Greek) renderings appended
  const hmmShape = isHmmNegLogCondShape(sig.implyStmts);
  const logJointFns = logProbJointFnNames(hyps.filter((h) => h.prop).map((h) => h.typeNode));
  let givenAltLists = [...hyps.filter((h) => h.prop)].reverse().map((h) => {
    const b = passB?.givens?.[h.idx];
    const altsA = nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean);
    const nameA = nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given";
    const lt0Joint = bvarAllLt0ProbJointName(h.typeNode); // All_Lt0ProbJoint, ranked first for this shape
    const logProbCond = bvarAllEqLogProbCondName(h.typeNode); // All_Eq_LogProbCond (not bare / Add_1)
    // point∧slice ℙ ≠ 0 → NeProbJoint__0 (Joint binary; not NeProbS_0 / NeProbJoint_0)
    const neJoint0 = neProbJoint0GivenName(h.typeNode);
    // Body: All_NeProb_0 / All_Differentiable_Prob beat ae-stripped NeProbS_0 / Differentiable_ProbCond
    const neProb0 = allNeProb0GivenName(h.typeNode);
    const allDiff = allDifferentiableGivenName(h.typeNode);
    const bodyPrefer = lt0Joint || logProbCond || neJoint0 || neProb0 || allDiff || null;
    const bodyLegacy = [
      // All_GtProbJoint__0 = same positivity fact with `>` / binary Joint `__0` (never bare GtProbJoint*)
      ...(lt0Joint ? ["All_GtProbJoint__0"] : []),
      ...(logProbCond ? ["Eq_LogProbCond", "EqAdd_1_LogProbCond"] : []),
      // Ne0ProbJoint alt; live NeProbS_0 stays accepted while remigrating (never NeProbJoint_0)
      ...(neJoint0 ? ["Ne0ProbJoint", "NeProbS_0", "NeProb_0"] : []),
      ...(neProb0 ? ["NeProbS_0", "All_NeProbS_0", "NeProb_0"] : []),
      ...(allDiff ? ["All_Differentiable", "Differentiable_ProbCond", "All_Differentiable_ProbCond", "Differentiable"] : []),
    ];
    // max over the log joint probability (`x' t a = max[«y.bvar» …] s t …`): All_Eq_Max replaces GetMax
    const maxLog = maxLogProbJointGiven(h.typeNode, logJointFns);
    const dropIllegalJoint = (xs) =>
      xs.filter((x) => !isIllegalGtProbJointAtom(x) && !isIllegalNeProbJointAtom(x));
    const allAlts = maxLog
      ? uniq([maxLog.name, ...dropIllegalJoint([...altsA, ...(b?.alts || [])].filter((x) => !/GetMax/.test(x)))])
      : uniq(dropIllegalJoint([...(bodyPrefer ? [bodyPrefer] : []), ...altsA, ...bodyLegacy, ...(b?.alts || [])]));
    const rawName = maxLog?.name || bodyPrefer || nameA;
    const rawNameB = maxLog?.name || bodyPrefer || (b ? pickCanon(b.alts, b.name) : null);
    return {
      binder: h.name,
      optional: !!h.optional,
      canonSkip: !!h.canonSkip,
      alts: allAlts,
      extraAlts: uniq([
        ...(maxLog ? maxLog.extras : hmmShape && hasBvarBinder(h.typeNode) ? hmmBvarAllAlts(allAlts) : []),
        ...legacyEqJointAlts(allAlts),
      ]), // accepted, not enumerated
      name: preferMeqExpectCondDot(rawName, allAlts),
      nameB: rawNameB ? preferMeqExpectCondDot(rawNameB, allAlts) : null,
      chain: classChain(h.typeNode),
    };
  });
  const instAltLists = extractInstanceHyps(sig.indented).reverse().map((h) => ({
    binder: h.name,
    alts: nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean),
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given",
    chain: classChain(h.typeNode),
  }));
  // of-tail is plain reverse(Lean givens), except:
  // Body GradExpect FunSMul: Lean h₂ NeProb / h₃ Diff → path Diff before NeProb (plain reverse).
  // Body Eq_SymmToDual In_Ico0: Lean puts NeProb earlier than Diff; still cluster
  // All_Differentiable_Prob/All_NeProb_0 like FunSMul (NeProb immediately after Diff in the path).
  // Body ExpectDot=∫Dot FunSMul: NeProb stays Lean h₂ — do NOT cluster next to Diff (keeps
  // …/Diff/Ae_GtInftySup/All_Measurable/All_NeProb_0/IsPolicyTrajectory/In_Ico0).
  if (!expectDotIntegralExtDotShape) {
    const isNe = (g) => (g.alts || []).includes("All_NeProb_0") || g.name === "All_NeProb_0";
    const isDiffProb = (g) => (g.alts || []).includes("All_Differentiable_Prob") || g.name === "All_Differentiable_Prob";
    const iDiff = givenAltLists.findIndex(isDiffProb);
    const iNe = givenAltLists.findIndex(isNe);
    if (iDiff >= 0 && iNe >= 0 && iNe !== iDiff + 1) {
      const [ne] = givenAltLists.splice(iNe, 1);
      const iDiff2 = givenAltLists.findIndex(isDiffProb);
      givenAltLists.splice(iDiff2 + 1, 0, ne);
    }
  }
  // Body ExpectDot leaf: prefer All_Measurable over All_MeasurableFun; Ae_GtInftySup over AeGtInftySup.
  if (expectDotIntegralExtDotShape) {
    for (const g of givenAltLists) {
      const alts = g.alts || [];
      if (alts.some((a) => /MeasurableFun/.test(a)) || /MeasurableFun/.test(g.name || "")) {
        const preferred = (g.name || "").replace(/MeasurableFun/g, "Measurable");
        const mapped = alts.map((a) => a.replace(/MeasurableFun/g, "Measurable"));
        g.alts = uniq(["All_Measurable", preferred, ...mapped, ...alts].filter(Boolean));
        g.name = preferred.includes("Measurable") && !/MeasurableFun/.test(preferred) ? preferred : "All_Measurable";
        if (g.nameB) g.nameB = String(g.nameB).replace(/MeasurableFun/g, "Measurable");
      }
      if (alts.includes("AeGtInftySup") || g.name === "AeGtInftySup" || alts.includes("Ae_GtInftySup")) {
        g.alts = uniq(["Ae_GtInftySup", "AeGtInftySup", ...alts]);
        g.name = "Ae_GtInftySup";
        if (g.nameB) g.nameB = "Ae_GtInftySup";
      }
    }
  }
  // Body: keep In_Ico0 / In_Ico1 leaf suffix when the file is already filed under that name
  // (Ico 0 1 otherwise prefers bare In_Ico; sisters disambiguate with 0/1).
  {
    const curLeaf = String(relCurrent).replace(/\\/g, "/").replace(/\.lean$/, "").split("/").pop() || "";
    if (/^In_Ico[01]$/.test(curLeaf)) {
      for (const g of givenAltLists) {
        if (!(g.alts || []).some((a) => /^In_?Ico/.test(a))) continue;
        g.alts = uniq([curLeaf, ...(g.alts || [])]);
        g.name = curLeaf;
        if (g.nameB) g.nameB = curLeaf;
      }
    }
  }
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
  const implySet = altSet(implyExtraAlts.length ? [...implyAlts, ...implyExtraAlts] : implyAlts);
  const gSets = givenAltLists.map((g) => { const s = g.alts.length ? altSet(g.extraAlts?.length ? [...g.alts, ...g.extraAlts] : g.alts) : new Set(["Given"]); if (g.optional) s.__optional = true; return s; });
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
  // Canonical first among free paths, then shortest — unless the canonical rendering is overlong (Windows MAX_PATH).
  // Paths already occupied by another lemma under Lemma/ rank below free alternatives (sibling rename collisions).
  const tooLong = (p) => ("Lemma/" + p).length > PATH_WARN_LEN;
  const preferCanon = true;
  const currentNorm = relCurrent.startsWith("Lemma/") ? relCurrent.slice(6) : relCurrent;
  const pathTakenByOther = (p) => {
    const norm = String(p).replace(/\\/g, "/");
    if (norm === currentNorm) return false;
    try { return fs.existsSync(path.join(LEMMA_ROOT, norm)); } catch { return false; }
  };
  const sorted = allPaths.sort((a, b) =>
    (pathTakenByOther(a) - pathTakenByOther(b)) ||
    (preferCanon ? (b === relPath) - (a === relPath) : 0) ||
    byBestToWorst(a, b));
  // every component must be a valid Lean module-name component (no leading digit, identifier characters)
  const validSorted = sorted.filter(validModulePath);
  const suggestions = validSorted.length ? validSorted : sorted;
  const moduleName = relPath.replace(/\.lean$/, "").split(/[/\\]/).join(".");
  const suggestedPath = suggestions[0] || relPath.replace(/\\/g, "/");
  const result = {
    file: abs,
    currentPath: currentNorm,
    suggestedPath,
    suggestions,
    moduleName,
    section,
    sectionScore: picked.score,
    sectionTokens: picked.tokens,
    imply: { name: implyPath, chain: implyChain },
    givensLeanOrder: hyps.map((h) => ({ binder: h.name, prop: h.prop, name: maxLogProbJointGiven(h.typeNode, logJointFns)?.name || bvarAllLt0ProbJointName(h.typeNode) || bvarAllEqLogProbCondName(h.typeNode) || neProbJoint0GivenName(h.typeNode) || allNeProb0GivenName(h.typeNode) || allDifferentiableGivenName(h.typeNode) || nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) })),
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
  // camel `MEqExpect_*` / bare `MEq` / chain-local `MEqExpect` as imply folders are never consistent
  {
    const curRest = result.currentPath.replace(/^[^/]+\//, "").replace(/\.lean$/, "");
    const ofAt = curRest.indexOf("/of/");
    const curImply = ofAt >= 0 ? curRest.slice(0, ofAt) : curRest;
    const segs = curImply.split("/").filter(Boolean);
    const multi = segs.length > 1;
    const badBareMeq = segs.includes("MEq") && multi;
    if (hasIllegalMeqImply(curImply) || badBareMeq) {
      result.consistent = {
        ok: false,
        reason: "illegal MEq imply token (use MEq_Expect_* / MEqExpectS, not MEqExpect / bare MEq)",
        existing: result.currentPath,
        suggested: result.suggestedPath,
      };
      result.warnings.push("current imply path uses illegal MEq token(s): " +
        segs.filter((s) => isIllegalMeqImplySeg(s, multi) || s === "MEq").join(", "));
    }
  }
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

/** Shortest ASCII bytes first; tie-break lexicographic. Occupied-path demotion is applied by the caller. */
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
  console.log("suggestions (" + r.suggestions.length + ", best→worst: free paths first, then shortest ASCII bytes):");
  for (const s of r.suggestions) {
    const taken = s !== r.currentPath && fs.existsSync(path.join(LEMMA_ROOT, s));
    console.log("  - Lemma/" + s + "  [" + Buffer.byteLength(s, "utf8") + " B" + (taken ? ", taken" : "") + "]" + (("Lemma/" + s).length > PATH_WARN_LEN ? "  ⚠ long" : ""));
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
