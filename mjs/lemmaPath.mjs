
import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import { compile } from "../js/parser/lean.js";
import { strStmt } from "../js/parser/lean/utility.js";
import { loadSectionKindMap } from "./lemmaSectionKind.mjs";
import {
  pathCombineMulChoices,
  pathEqCombineChoices,
  pathEqInfixChoices,
  pathEqFlatStem,
  pathAndInfixChoices,
  pathImpInfixChoices,
  pathUniqKeepEmpty,
  escapeHoleReLit,
  wrapHoleOpt,
  storedHoleOpt,
} from "../js/parser/lean/pathChoices.js";
import { holeRegexAltFill, collectHoleRegexAlternatives } from "../js/parser/lean/holeRegexAlternatives.js";

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
  MeasurableSet: "Measure",
  MeasurableSpace: "Measure",
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
  CurveDivisor: "Finsupp",

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
  l1Space: "Matrix",
  L1Space: "Matrix",
  l2Space: "Matrix",
  lpSpace: "Matrix",
  WithLp: "Matrix",
  PiLp: "Matrix",
  EuclideanSpace: "Matrix",

  Bool: "Bool",
  Hyperreal: "Hyperreal",
  "ℝ*": "Hyperreal",
  ZMod: "ZMod",
  StochasticVec: "Matrix",
  RowStochastic: "Matrix",
  StochasticIrreducible: "Matrix",
  Stationary: "Matrix",
  Aperiodic: "Matrix",
  DoeblinMinorization: "Matrix",
  Simplex: "Matrix",
  broadcast: "Matrix",
};

const SECTION_WEIGHT = {
  StochasticVec: 2, RowStochastic: 2, StochasticIrreducible: 2, Stationary: 2,
  Aperiodic: 2, DoeblinMinorization: 2, Simplex: 2, broadcast: 2,
  MeasurableSpace: 0,
};

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
  LeanInv: "Inv",

  LeanPow: "Pow",
  LeanDvd: "Dvd",
  Lean_in: "In",
  LeanIn: "In",
  Lean_notin: "NotIn",

  LeanInf: "Inf",
  Lean_cdotp: "Dot",

  LeanMatMul: "Dot",

  Lean_subseteq: "Subset",

  Lean_approx: "XEq",

};

function cls(n) { return n?.constructor?.name || ""; }

const BIG_OP_CLASS_CACHE = new Map();
function isBigOp(node) {
  const c = cls(node);
  if (!c) return false;
  if (BIG_OP_CLASS_CACHE.has(c)) return BIG_OP_CLASS_CACHE.get(c);
  let big = false;
  for (let p = Object.getPrototypeOf(node); p; p = Object.getPrototypeOf(p)) {
    const n = p.constructor?.name;
    if (n === "LeanQuantifier") break;
    if (n === "LeanBigOperator") { big = true; break; }
  }
  BIG_OP_CLASS_CACHE.set(c, big);
  return big;
}

function bigOpDomainAtom(node) {
  if (!isBigOp(node)) return "";
  const op = String(node?.operator || "");
  const base = op.replace(/'+$/, "");
  if (base === "∏") return "Prod";
  if (base === "∑") return op === base ? "Sum" : "TSum";
  return "";
}

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

let REPO_DECLS = null;
function repoDecls() {
  if (REPO_DECLS) return REPO_DECLS;
  REPO_DECLS = {
    structs: new Map(),

    structInfo: new Map(),

    typeAbbrevs: new Set(),

    abbrevHeads: new Map(),

    propDecls: new Set(),

    dataDecls: new Set(),

    valueDefs: new Set(),

    members: new Map(),

    parents: new Map(),

  };
  return REPO_DECLS;
}

let LEMMA_FOLDERS = null;
function lemmaFolders() {
  if (!LEMMA_FOLDERS) { try { LEMMA_FOLDERS = fs.readdirSync(LEMMA_ROOT, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name); } catch { LEMMA_FOLDERS = []; } }
  return LEMMA_FOLDERS;
}
function structSection(name, sections = lemmaFolders()) {
  const info = repoDecls().structInfo.get(name);
  if (!info || info.prop) return null;
  if (sections.includes(name) || sections.some((s) => !DATA_TYPE_SECTIONS.has(s) && name.startsWith(s) && /[A-Z]/.test(name.charAt(s.length)))) return null;
  const SCALAR = new Set(["Real", "Nat", "Int", "Rat", "Complex"]);
  for (const ty of repoDecls().structs.get(name)?.values() || []) { const sec = TYPE_TO_SECTION[ty]; if (sec && !SCALAR.has(sec)) return null; }
  for (const n of [...info.ns].reverse()) if (DATA_TYPE_SECTIONS.has(n) && sections.includes(n)) return n;
  return null;
}

function nonDataFolder(name) {
  const { propDecls, dataDecls, valueDefs } = repoDecls();
  if (DATA_TYPE_SECTIONS.has(name) || TYPE_TO_SECTION[name] || dataDecls.has(name)) return false;
  return propDecls.has(name) || valueDefs.has(name);
}

function memberType(T, f, k = 0) {
  const { members, parents } = repoDecls();
  const t = members.get(T)?.get(f);
  if (t) return t;
  const p = parents.get(T);
  return p && k < 4 ? memberType(p, f, k + 1) : null;
}

function abbrevSection(name) {
  const { abbrevHeads } = repoDecls();
  for (let t = name, k = 0; t && k < 5; k++) {
    if (TYPE_TO_SECTION[t]) return TYPE_TO_SECTION[t];
    t = abbrevHeads.get(t);
  }
  return null;
}

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

function bundleVars(indented, explicitOnly = false) {
  const { structs } = repoDecls();
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

function binderTypeHead(typeNode) {
  let h = unwrapParen(typeNode);
  if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
  if (cls(h) === "LeanProperty" && cls(h.args?.[1]) === "LeanToken") return h.args[1].text || "";
  return cls(h) === "LeanToken" ? (h.text || "") : "";
}

function addColonBinderNames(colonNode, out) {
  if (cls(colonNode) !== "LeanColon") return;
  const b = colonNode.args?.[0];
  for (const x of cls(b) === "LeanToken" ? [b] : b?.args || []) {
    if (cls(x) === "LeanToken" && x.text && x.text !== "_") out.add(x.text);
  }
}

function bindersTypedAs(node, typeName, out = new Set()) {
  if (!node || typeof node !== "object") return out;
  const c = cls(node);
  if (c === "LeanBrace" || c === "LeanParenthesis" || c === "LeanBracket") {
    const a = node.args?.[0];
    if (cls(a) === "LeanColon" && binderTypeHead(a.args?.[1]) === typeName) addColonBinderNames(a, out);
  }
  for (const a of node.args || []) bindersTypedAs(a, typeName, out);
  return out;
}

function isBinderMeasureProj(node, opts) {
  if (cls(node) !== "LeanProperty") return false;
  const obj = node.args?.[0];
  const prop = node.args?.[1];
  if (cls(prop) !== "LeanToken" || prop.text !== "measure") return false;
  if (cls(obj) !== "LeanToken") return false;
  return isLeafName(obj.text, opts?.leaves);
}

function propertyParts(n) {
  if (cls(n) === "LeanToken") return [n.text];
  if (cls(n) !== "LeanProperty") return null;
  const l = propertyParts(n.args?.[0]);
  const r = propertyParts(n.args?.[1]);
  return l && r ? [...l, ...r] : null;
}

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
    if (cls(n) === "LeanMul" && n.subscript === "ᵥ" && !n.isLeftSubscript
        && cls(args[0]) === "Lean_cdotp" && args[0].subscript === "ᵥ" && parent) {
      const dot = args[0];
      const [a, b] = dot.args || [];
      const vec = args[1];
      n.args = [b, vec];
      if (b) b.parent = n;
      if (vec) vec.parent = n;
      dot.args = [a, n];
      if (a) a.parent = dot;
      n.parent = dot;
      dot.parent = parent;
      parent.args[idx] = dot;
      walk(n, dot, 1);
      return;
    }
    for (let i = 0; i < args.length; i++) walk(args[i], n, i);
  })(root, null, -1);
}

function holeBundleProjections(root, bundles, leaves) {
  if (!bundles.size) return;
  const { structs } = repoDecls();
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

function sectionLemmaFiles(section) {
  const dir = path.join(LEMMA_ROOT, section);
  const out = [];
  if (!section || !fs.existsSync(dir)) return out;
  const walk = (d) => {
    let ents;
    try { ents = fs.readdirSync(d, { withFileTypes: true }); } catch { return; }
    for (const e of ents) {
      const fp = path.join(d, e.name);
      if (e.isDirectory()) walk(fp);
      else if (e.isFile() && e.name.endsWith(".lean") && !e.name.endsWith(".echo.lean")) out.push(fp);
    }
  };
  walk(dir);
  return out;
}

function isSingletonSection(section, abs) {
  const files = sectionLemmaFiles(section);
  const absN = abs ? path.resolve(abs) : "";
  const already = absN && files.some((f) => path.resolve(f) === absN);
  const after = already ? files.length : files.length + 1;
  return after <= 1;
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

function isTrajectorySampleSpace(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_rightarrow" || (u.args || []).length !== 2) return false;
  const left = unwrapParen(u.args[0]);
  if (!(cls(left) === "LeanToken" && (left.text === "ℕ" || left.text === "Nat"))) return false;
  const right = unwrapParen(u.args[1]);
  if (cls(right) !== "Lean_times") return false;
  let hasReal = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || hasReal) return;
    if (cls(n) === "LeanToken" && (n.text === "ℝ" || n.text === "Real")) hasReal = true;
    for (const a of n.args || []) walk(a);
  })(right);
  return hasReal;
}

function isSampleSpaceDomain(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanToken" && (u.text === "Ω" || u.text === "Omega")) return true;
  return isTrajectorySampleSpace(u);
}

function hasRandomAstCues(node) {
  if (bindersTypedAs(node, "Model").size > 0) return true;
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "Lean_rightarrow") {
      if (isSampleSpaceDomain(n.args?.[0])) {
        found = true;
        return;
      }
    }
    if (cls(n) === "LeanToken") {
      const t = n.text;
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
      if (structBinderTypes(node).get(t) === "Random") rv = true;
      if (t === "ℙ" || t === "𝔼" || /PSpace$/.test(t) || /\.bvar$/.test(t) || isSfBvarText(t)) prob = true;
    }
    if (Array.isArray(n.args)) for (const c of n.args) walk(c);
  };
  walk(node);
  return rv && prob;
}

function hasMeasureLawCues(node) {
  const LAW = new Set([
    "chiSquare", "gaussianReal", "fisherReal", "gammaMeasure", "sumSqGaussians",
  ]);
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "LeanToken" && typeof n.text === "string" && LAW.has(n.text)) {
      found = true;
      return;
    }
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && n.args[0].text === "Measure") {
      found = true;
      return;
    }
    if (cls(n) === "LeanColon") {
      let ty = unwrapParen(n.args?.[1]);
      if (cls(ty) === "LeanArgsSpaceSeparated") ty = ty.args?.[0];
      if (cls(ty) === "LeanToken" && ty.text === "Measure") {
        found = true;
        return;
      }
    }
    for (const a of n.args || []) walk(a);
  };
  walk(node);
  return found;
}

function hasHyperrealNsaCues(node) {
  const NSA_PRED = new Set([
    "Infinitesimal", "InfinitesimalPos", "InfinitesimalNeg",
    "Infinite", "InfinitePos", "InfiniteNeg", "NotInfinite",
    "stdPart",
  ]);
  const NSA_CONST = new Set(["epsilon", "omega"]);
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "LeanToken" && typeof n.text === "string" && NSA_PRED.has(n.text)) {
      found = true;
      return;
    }
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && n.args[0].text === "Hyperreal") {
      const p = n.args[1];
      const name =
        cls(p) === "LeanToken" ? p.text :
        (cls(p) === "LeanArgsSpaceSeparated" && cls(p.args?.[0]) === "LeanToken" ? p.args[0].text : "");
      if (NSA_PRED.has(name) || NSA_CONST.has(name)) { found = true; return; }
    }
    if (cls(n) === "Lean_rightarrow") {
      const rhs = unwrapParen(n.args?.[1]);
      if (cls(rhs) === "LeanPosPart" || cls(rhs) === "LeanNegPart") {
        const arg = unwrapParen(rhs.args?.[0] ?? rhs.arg);
        if (cls(arg) === "LeanToken" && arg.text === "0") { found = true; return; }
      }
    }
    for (const a of n.args || []) walk(a);
  };
  walk(node);
  return found;
}

function hasComplexICues(node) {
  let found = false;
  const walk = (n) => {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "LeanToken" && n.text === "I") { found = true; return; }
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && n.args[0].text === "Complex") {
      const p = n.args[1];
      const name =
        cls(p) === "LeanToken" ? p.text :
        (cls(p) === "LeanArgsSpaceSeparated" && cls(p.args?.[0]) === "LeanToken" ? p.args[0].text : "");
      if (name === "I") { found = true; return; }
    }
    for (const a of n.args || []) walk(a);
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
      else if (structSection(ns)) put("st:" + ns, w);
    }
  }
  if (c === "LeanProperty" && cls(node.args?.[0]) === "LeanToken" && /^[A-Z]/.test(node.args[0].text || "") && structSection(node.args[0].text)) put("st:" + node.args[0].text, w);
  if (c === "LeanProperty" && cls(node.args?.[1]) === "LeanToken") {
    const p = nameToken(node.args[1].text || "");
    if (TYPE_TO_SECTION[p] === p) put("." + p, w);
  }
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

let SECTION_KIND_MAP = null;
function sectionKindMap() {
  if (!SECTION_KIND_MAP) SECTION_KIND_MAP = loadSectionKindMap();
  return SECTION_KIND_MAP;
}

export function refusedSectionFolder(name) {
  if (DATA_TYPE_SECTIONS.has(name) || TYPE_TO_SECTION[name]) return false;
  const kind = sectionKindMap().get(name);
  return kind !== "data type";
}

function customSection(sections, conclNode, givenTypes, importDecls = new Map(), binders = null) {
  const custom = sections.filter((s) => !DATA_TYPE_SECTIONS.has(s) && !TYPE_TO_SECTION[s] && !refusedSectionFolder(s));
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
  {
    let h = conclNode;
    while (h && (cls(h) === "LeanStatements" || cls(h) === "LeanParenthesis" || cls(h) === "Lean_land")) h = cls(h) === "LeanStatements" ? (h.args || []).find((a) => cls(a) !== "LeanLineComment") : h.args?.[0];
    const bundled = binders ? bundleVars(binders) : new Map();
    const projArg = (a) => { const p = propertyParts(unwrapParen(a)); return !!p && p.length >= 2 && bundled.has(p[0]); };
    if (cls(h) === "LeanArgsSpaceSeparated" && cls(h.args?.[0]) === "LeanToken" && custom.includes(h.args[0].text) && !h.args.slice(1).some(projArg)) return h.args[0].text;
  }
  const folderOf = (ty) => custom.includes(ty) ? ty : custom.filter((s) => ty.startsWith(s) && /[A-Z]/.test(ty.charAt(s.length))).sort((a, b) => b.length - a.length)[0] || null;
  if (binders) {
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
  const conclTokens = (n, out = []) => {
    if (!n || typeof n !== "object") return out;
    if (cls(n) === "LeanToken" && typeof n.text === "string") out.push(n.text);
    const kids = n.args || [];
    const q = cls(n) === "Lean_exists" || cls(n) === "Lean_forall";
    for (const a of q ? kids.slice(-1) : kids) conclTokens(a, out);
    return out;
  };
  for (const t of conclTokens(conclNode)) { if (custom.includes(t) || custom.includes(t.split(".")[0])) return custom.includes(t) ? t : t.split(".")[0]; }
  for (const t of conclTokens(conclNode)) if (/^[A-Z]/.test(t) && repoDecls().structs.has(t)) { const f = folderOf(t); if (f) return f; }
  for (const g of givenTypes) {
    let h = unwrapParen(g);
    if (cls(h) === "LeanArgsSpaceSeparated") h = h.args?.[0];
    if (cls(h) === "LeanGetElem") h = h.args?.[0];
    const s = cls(h) === "LeanToken" ? match(h.text) : null;
    if (s) return s;
    if (cls(h) === "LeanToken") for (const [sec, names] of importDecls) if (custom.includes(sec) && names.has(h.text)) return sec;
  }
  for (const t of conclTokens(conclNode)) {
    const last = t.includes(".") ? t.slice(t.lastIndexOf(".") + 1) : t;
    if (!/^[a-z]/.test(last) || !(last.includes("_") || /[A-Z]/.test(last))) continue;
    const camel = nameTokenRaw(last);
    if (custom.includes(camel)) return camel;
    const f = folderOf(camel);
    if (f && givenTypes.some((g) => tokensOf(g).some((x) => /^[a-z]/.test(x) && nameTokenRaw(x) === f))) return f;
  }
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
  for (const t of conclTokens(binders)) if (custom.includes(t)) return t;
  return null;
}

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

function importSections(_source, _sections) {
  return new Map();
}

function genericSection(sigNode, tokens, existing) {
  const pick = (s) => (existing.has(s) ? s : "Nat");
  if (hasNode(sigNode, (n) => cls(n) === "LeanToken" && /^(Set\.)?I(cc|co|oc|oo)$/.test(n.text || ""))) return pick("Set");
  if (["Field", "GroupWithZero", "DivisionRing", "IsStrictOrderedRing", "LinearOrderedField"].some((t) => tokens.has(t)) && !hasNode(sigNode, (n) => cls(n) === "LeanAbs")) return pick("Rat");
  if (hasNode(sigNode, (n) => cls(n) === "LeanAbs") || ["AddGroup", "AddCommGroup", "Ring", "CommRing", "LinearOrderedAddCommGroup"].some((t) => tokens.has(t))) return pick("Int");
  return "Nat";
}

function pickSection(sigNode, sections, extra = {}) {
  if (extra.custom && !isSingletonSection(extra.custom, extra.file)) {
    return { section: extra.custom, score: "custom", tokens: [...collectTokens(sigNode)].sort() };
  }
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
    else if (!TYPE_TO_SECTION[t] && structTypes.has(t)) { sec = structTypes.get(t); raw = STRUCT_BINDER_WEIGHT; }

    else if (!TYPE_TO_SECTION[t] && repoDecls().abbrevHeads.has(t)) { sec = abbrevSection(t); raw = 1; }

    else { sec = TYPE_TO_SECTION[t]; raw = t === sec ? 3 : SECTION_WEIGHT[t] ?? 1; }
    if (!sec) continue;
    const scalarField = tokens.has("ℂ") || tokens.has("ℝ") || tokens.has("ℚ")
      || tokens.has("Complex") || tokens.has("Real") || tokens.has("Rat");
    const index = sec === "Nat" || sec === "Int" || (sec === "Fin" && scalarField);
    if (index && tokens.size > 0) raw = Math.min(raw, 1) * 0.5;
    const x = w === 0 ? raw * 0.5 : w === 2 && !index ? raw + 0.5 : raw;
    add(sec, x);
  }
  if (hasNode(sigNode, (n) => cls(n) === "LeanNorm" || cls(n) === "Lean_sqrt" || (cls(n) === "LeanToken" && n.text === "π"))) add("Real", 1);
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
  const importAdded = new Map();
  for (const s of extra.imports || []) {
    if (!scores.has(s)) scores.set(s, 0);
    add(s, 1.5);
    importAdded.set(s, (importAdded.get(s) ?? 0) + 1.5);
  }
  const concl = conclusionNode(sigNode);
  if (concl && (cls(concl) === "LeanEq" || cls(concl) === "Lean_le") && concl.superscript === "ᶠ") add("Filter", 3);
  if (concl && CLASS_TOKEN[cls(concl)] && (concl.args || []).length === 2 &&
      concl.args.every((a) => { const u = unwrapParen(a); return (cls(u) === "Lean_sum" || cls(u) === "Lean_prod") && (u.args || []).some((b) => cls(b) === "Lean_in"); })) {
    add("Finset", 2);
  }
  const hasVecMul = (n) => !!n && typeof n === "object" && (subscriptedMulAtom(n) !== null || (n.args || []).some(hasVecMul));
  if (hasVecMul(sigNode) && scores.has("Matrix")) scores.set("Matrix", scores.get("Matrix") + 2);
  const LP_EMBED = new Set(["ofL1", "ofLp", "toL1", "toLp"]);
  if (LP_EMBED.has(conclusionLhsHeadToken(sigNode)) && scores.has("Matrix"))
    scores.set("Matrix", scores.get("Matrix") + 2);
  if (tokens.has("AbsoluteValue") && scores.has("AbsoluteValue"))
    scores.set("AbsoluteValue", scores.get("AbsoluteValue") + 5);
  if (tokens.has("List") && scores.has("List")) scores.set("List", scores.get("List") + 2);
  if (hasRandomAstCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 5);
  if (hasRandomVariableCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 4);
  if (!hasRandomAstCues(sigNode) && !hasRandomVariableCues(sigNode) &&
      scores.has("Measure") && hasMeasureLawCues(sigNode)) {
    add("Measure", 5);
    if ((scores.get("Real") ?? 0) > 2) scores.set("Real", 2);
  }
  if ((scores.get("Hyperreal") ?? 0) > 0 && hasHyperrealNsaCues(sigNode)) {
    add("Hyperreal", 5);
    if ((scores.get("Real") ?? 0) > 2) scores.set("Real", 2);
  }
  if ((scores.get("Complex") ?? 0) > 0 && hasComplexICues(sigNode)) {
    add("Complex", 5);
    if ((scores.get("Real") ?? 0) > 2) scores.set("Real", 2);
  }
  {
    const INTERVAL = /^(Set\.)?I(cc|co|oc|oo|ci|ic|oi|io)$/;
    const isSetCons = (n) => {
      const u = unwrapParen(n);
      const k = cls(u);
      return isSetBuilder(u) || k === "Lean_cup" || k === "Lean_cap" ||
        (k === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken" && INTERVAL.test(u.args[0].text || ""));
    };
    if (concl && (cls(concl) === "LeanEq" || cls(concl) === "Lean_subseteq") && (concl.args || []).length === 2 && concl.args.every(isSetCons)) add("Set", 8);
    if (concl && (cls(concl) === "Lean_in" || cls(concl) === "LeanIn") && isSetCons(concl.args?.[1])) {
      const cond = setBuilderCond(concl.args[1]);
      let head = cond ? unwrapParen(cond) : null;
      if (cls(head) === "LeanArgsSpaceSeparated") head = head.args?.[0];
      if (cls(head) === "LeanToken" && /^(MeasurableSet|Measurable)$/.test(head.text || "") && scores.has("Measure")) {
        add("Measure", 5);
      } else {
        add("Set", 1);
      }
    }
    const conclIsSetFocus = !!(concl && (
      ((cls(concl) === "LeanEq" || cls(concl) === "Lean_subseteq") && (concl.args || []).length === 2 && concl.args.every(isSetCons)) ||
      ((cls(concl) === "Lean_in" || cls(concl) === "LeanIn") && isSetCons(concl.args?.[1]))
    ));
    if (!conclIsSetFocus && tokens.has("ℝ") && (scores.get("Set") ?? 0) > 1 &&
        hasNode(sigNode, (n) => cls(n) === "LeanToken" && INTERVAL.test(n.text || ""))) {
      scores.set("Set", 1);
    }
    if (!conclIsSetFocus && scores.has("Measure") && (scores.get("Set") ?? 0) > 0 &&
        (tokens.has("MeasurableSet") || tokens.has("Measurable"))) {
      scores.set("Set", 0);
    }
  }
  {
    const realAnalysis = [...tokens].some((t) => /^(ContinuousOn|deriv)$/.test(t));
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
  {
    const isMatrixOf = (n) => {
      if (cls(n) !== "LeanProperty" || cls(n.args?.[0]) !== "LeanToken" || n.args[0].text !== "Matrix") return false;
      const p = n.args[1];
      if (cls(p) === "LeanToken" && p.text === "of") return true;
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
  if (scores.has("Polynomial") && hasNode(sigNode, (n) =>
    cls(n) === "LeanGetElem" && cls(n.args?.[1]) === "LeanToken" && n.args[1].text === "X")) {
    add("Polynomial", 4);
  }
  {
    const hasMvP = hasNode(sigNode, (n) => cls(n) === "LeanToken" && n.text === "MvPolynomial");
    if (hasMvP && scores.has("MvPolynomial")) {
      add("MvPolynomial", 4);
      if ((scores.get("Fin") ?? 0) > 1) scores.set("Fin", 1);
      if ((scores.get("Ideal") ?? 0) > 1) scores.set("Ideal", 1);
    }
  }
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
  const matrixExp = (n) => {
    if (!n || typeof n !== "object") return false;
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken" && /^(Real|Complex)$/.test(n.args[0].text || "")) return false;
    if (cls(n) === "LeanToken" && (n.text === "exp" || n.text === "NormedSpace.exp")) return true;
    return (n.args || []).some(matrixExp);
  };
  if (scores.has("NormedSpace") && matrixExp(sigNode) &&
      hasNode(sigNode, (n) => cls(n) === "LeanToken" && n.text === "Matrix")) add("NormedSpace", 8);
  if (concl && tokens.has("ℝ") && hasNode(concl, (n) => cls(n) === "Lean_lim")) add("Real", 3);
  if (concl && tokens.has("ℝ") && hasNode(concl, (n) => cls(n) === "LeanArgsSpaceSeparated" && cls(n.args?.[0]) === "LeanToken" && /^(sSup|sInf)$/.test(n.args[0].text || "") &&
      hasNode(n.args[1], (m) => cls(m) === "LeanToken" && m.text === "''"))) add("Real", 3);
  const existing = new Set(sections);
  const sigScore = (s) => (scores.get(s) ?? 0) - (importAdded.get(s) ?? 0);
  const rank = (s) => [scores.get(s) ?? 0, depths.get(s) ?? -1];
  const better = (a, b) => {
    const aSig = sigScore(a) > 0, bSig = sigScore(b) > 0;
    if (aSig !== bSig) return aSig;
    const [as, ad] = rank(a);
    const [bs, bd] = rank(b);
    if (as !== bs) return as > bs;
    if (ad !== bd) return ad > bd;

    if (existing.has(a) !== existing.has(b)) return existing.has(a);
    return a < b;
  };
  const usable = candidates.filter((s) => !isSingletonSection(s, extra.file));
  let best = usable[0] || sections[0] || "Nat";
  for (const s of usable) if (better(s, best)) best = s;
  if (!(scores.get(best) > 0) && existing.has("Nat") && !isSingletonSection("Nat", extra.file)) {
    best = genericSection(sigNode, tokens, existing);
  }
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
  if (indepAtom(typeNode)) return true;
  if (cls(unwrapParen(typeNode)) === "LeanDistributed") return true;
  const name = cls(typeNode);
  if (["Lean_forall","Lean_exists","Lean_lt","Lean_gt","Lean_le","Lean_ge","LeanEq","Lean_ne","LeanNe","Lean_leftrightarrow","Lean_land","Lean_lor","Lean_lnot","Lean_in","LeanIn","Lean_notin","Lean_subseteq","LeanDistributed"].includes(name)) return true;
  if (name === "Lean_rightarrow") {
    const args = typeNode.args || [];
    return isPropHyp(args[0]) || isPropHyp(args[1]);
  }
  if (name === "LeanArgsSpaceSeparated") {
    let head = typeNode.args?.[0];
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^[A-Z][A-Za-z0-9]+$/.test(head.args[1].text || "") && !TYPE_TO_SECTION[head.args[1].text]) return true;
    if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken") head = head.args[0];

    if (cls(head) === "LeanToken") {
      const t = head.text;
      if (t === "Pairwise" || t === "And" || t === "Or" || t === "Not" || /^Is[A-Z]/.test(t) || /^Has[A-Z]/.test(t)) return true;
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
  mk: "",

};

const SYMBOL_NAME = {
  "𝔼": "Expect", "𝕍𝕒𝕣": "Var", "∇": "Grad", "∅": "Empty", "⊤": "Top", "⊥": "Bot", "∞": "Infty", "π": "Pi", "√": "Sqrt", "𝓝": "",
  "𝒩": "Gaussian",

  "max⁻¹": "ArgMax", "min⁻¹": "ArgMin",
  atTop: "", atBot: "",
};

let KEEP_GREEK = false;
const GREEK_KEEP_RE = /[\u0370-\u03FF\u1F00-\u1FFF\u2090-\u209C\u1D62-\u1D6A\u2080-\u2089]/u;
function nameToken(text) {
  if (!text) return "";
  const t = String(text);
  const last = t.includes(".") ? t.slice(t.lastIndexOf(".") + 1) : t;
  if (SYMBOL_NAME[last] !== undefined) return SYMBOL_NAME[last];
  if (KEEP_GREEK && GREEK_KEEP_RE.test(last)) {
    let s = nameTokenRaw(t);
    if (/^[^\x00-\x7F]/.test(last) && !last.includes("_")) s = last;
    return [...s].filter((ch) => /[\x00-\x7F]/.test(ch) || GREEK_KEEP_RE.test(ch)).join("").replace(/\*+$/, "");
  }
  return nameTokenRaw(t).replace(/[^\x00-\x7F]/g, "").replace(/\*+$/, "");
}

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

function isLeafName(text, leaves) {
  if (!text || text === "_") return true;
  if (!leaves?.size) return false;
  if (leaves.has(text)) return true;
  const named = nameToken(text);
  if (!named) return false;
  for (const leaf of leaves) {
    if (!leaf || leaf === "_") continue;
    if (nameToken(leaf) === named && (text === leaf || text.startsWith(leaf))) return true;
  }
  return false;
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
  if (!noBinders && name === "LeanBracket") {
    const app = node.args?.[0];
    if (cls(app) === "LeanColon") {
      const binders = app.args?.[0];
      if (cls(binders) === "LeanToken") {
        if (binders.text && binders.text !== "_") out.add(binders.text);
      } else if (cls(binders) === "LeanArgsSpaceSeparated") {
        for (const a of binders.args || []) {
          if (cls(a) === "LeanToken" && a.text && a.text !== "_") out.add(a.text);
        }
      }
    } else if (cls(app) === "LeanArgsSpaceSeparated") {
      for (const a of (app.args || []).slice(1)) {
        if (cls(a) === "LeanToken" && a.text && a.text !== "_") out.add(a.text);
      }
    } else if (cls(app) === "Lean_forall" || cls(app) === "Lean_exists") {
    }
  }
  if (name === "Lean_forall" || name === "Lean_exists") {
    const head = node.args?.[0];
    if ((cls(head) === "Lean_in" || cls(head) === "LeanIn") && cls(head.args?.[0]) === "LeanToken") {
      const t = head.args[0].text;
      if (t) out.add(t);
    }
    if (cls(head) === "LeanToken" && head.text) out.add(head.text);
    quantBinderNames(head, out);
    if (cls(head) === "LeanColon" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text) {
      out.add(head.args[0].text);
    }
  }
  if (name === "Lean_int") for (const b of (node.args || []).slice(0, -1)) quantBinderNames(b, out);
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
  if (name === "LeanStack") {
    const binders = matrixFinBindersOf(node);
    const lts = binders || (cls(node.bound ?? node.args?.[0]) === "Lean_lt" ? [node.bound ?? node.args[0]] : []);
    for (const lt of lts) {
      if (cls(lt?.args?.[0]) === "LeanToken" && lt.args[0].text && lt.args[0].text !== "_") out.add(lt.args[0].text);
    }
  }
  if (name === "LeanIte" && cls(node.args?.[0]) === "LeanColon") {
    quantBinderNames(node.args[0].args?.[0], out);
  }
  for (const a of node.args || []) collectLeafBinders(a, out, noBinders);
  return out;
}

function snakeFocus(tag, focus) {
  const f = focus === "One" ? "1" : focus;
  return tag + "_" + f;
}

const NUM_WORD = ["Zero", "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine", "Ten"];
function numberWord(d) {
  const n = Number(d);
  if (String(n) === d && n <= 10) return NUM_WORD[n];
  return [...d].map((c) => NUM_WORD[+c]).join("");
}

function sanitizePathSeg(seg) {
  seg = String(seg || "");
  if (seg === "And__" || seg === "Or__" || seg === "Imp__") return seg;
  seg = seg.replace(/_+$/, "");
  if (seg.startsWith("Expect_") && !/^Expect_(Mul|Div|SMul|Expect)/.test(seg))
    seg = "Expect" + seg.slice("Expect_".length);
  if (seg.startsWith("GradExpect_"))
    seg = "GradExpect" + seg.slice("GradExpect_".length);
  const m = /^(-?)(\d+)(.*)$/s.exec(seg);
  if (!m) return seg;
  return (m[1] ? "Neg" : "") + numberWord(m[2]) + m[3];
}

function validModuleComponentBasic(c) {
  return /^[\p{L}_][\p{L}\p{N}_'!?\u2080-\u209C\u1D62-\u1D6A\u2070-\u207F]*$/u.test(c || "");
}

const HOUSE_SOFTS = [
  { slash: "/ae/", dot: ".ae.", name: "ae" },
  { slash: "/eq/", dot: ".eq.", name: "eq" },
  { slash: "/is/", dot: ".is.", name: "is" },
];

function topLevelIndex(s, needle) {
  const t = String(s || "");
  let depth = 0;
  for (let i = 0; i <= t.length - needle.length; i++) {
    const ch = t[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (depth === 0 && t.startsWith(needle, i)) return i;
  }
  return -1;
}

function splitTopHouse(s) {
  const t = String(s || "");
  for (const soft of HOUSE_SOFTS) {
    let i = topLevelIndex(t, soft.slash);
    if (i >= 0)
      return { left: t.slice(0, i), soft: soft.name, right: t.slice(i + soft.slash.length), delim: soft.slash };
    i = topLevelIndex(t, soft.dot);
    if (i >= 0)
      return { left: t.slice(0, i), soft: soft.name, right: t.slice(i + soft.dot.length), delim: soft.dot };
  }
  return null;
}

function houseSoftOf(name) {
  return HOUSE_SOFTS.find((s) => s.name === name) || null;
}

function houseDelimSlash(soft) {
  return houseSoftOf(soft)?.slash || "/eq/";
}

function houseDelimDot(soft) {
  return houseSoftOf(soft)?.dot || ".eq.";
}

function sourceHasHouseDelim(s) {
  const t = String(s || "");
  return HOUSE_SOFTS.some((soft) => t.includes(soft.slash) || t.includes(soft.dot));
}

function houseDelimLenAt(s, i) {
  const t = String(s || "");
  for (const soft of HOUSE_SOFTS) {
    if (t.startsWith(soft.slash, i)) return soft.slash.length;
    if (t.startsWith(soft.dot, i)) return soft.dot.length;
  }
  return 0;
}

function fuseHouseIdent(s) {
  const t = String(s || "");
  const h = splitTopHouse(t);
  if (!h) return t;
  const mid = h.soft.charAt(0).toUpperCase() + h.soft.slice(1);
  return fuseHouseIdent(h.left) + mid + fuseHouseIdent(h.right);
}

function houseKidsSource(kids) {
  let out = "";
  for (const k of kids || []) {
    if (k.kind === "lit") out += k.v || "";
    else if (k.kind === "group") out += houseKidsSource(k.kids);
  }
  return out;
}

function nestHouseDots(side) {
  return String(side || "").replace(/\(([^()]+)\)/g, (m, inner) => {
    const h = splitTopHouse(inner);
    return h ? "(" + h.left + "." + h.soft + "." + h.right + ")" : m;
  });
}

function seqHasTopHouseLit(parts) {
  for (const p of parts || []) {
    if (p.kind === "lit" && splitTopHouse(p.v)) return true;
  }
  return false;
}

function markNestedHouseGroups(parts) {
  for (const p of parts || []) {
    if (p.kind === "group") {
      p.nestedHouse = seqHasTopHouseLit(p.kids);
      markNestedHouseGroups(p.kids);
    } else if (p.kind === "opt") {
      markNestedHouseGroups(p.alts);
    }
  }
}

function validModuleComponent(c) {
  const s = String(c || "");
  const h = splitTopHouse(s);
  if (h) return validModuleComponent(h.left) && validModuleComponent(h.right);
  return validModuleComponentBasic(s);
}

function unfilledHolePiece(p) {
  const norm = String(p || "")
    .replace(/\\/g, "/")
    .replace(/^Lemma\//, "")
    .replace(/\.lean$/, "");
  const partsOf = (seg) => {
    const h = splitTopHouse(seg);
    return h ? [h.left, h.right] : [seg];
  };
  for (const seg of norm.split("/")) {
    if (!seg) continue;
    for (const part of partsOf(seg)) {
      if (!part || part === "And__" || part === "Or__" || part === "Imp__") continue;
      if (part.endsWith("_")) return part;
    }
  }
  return "";
}
export function givenHoleRegexFromAst(typeNode, opts = {}) {
  return implyHoleRegexFromAst(typeNode, opts);
}

function validModulePath(p) {
  return String(p).replace(/\.lean$/, "").split("/").every(validModuleComponent);
}

function sanitizeRelPath(rel) {
  return String(rel)
    .split("/")
    .map((part) => {
      if (part.endsWith(".lean")) {
        const stem = part.slice(0, -5);
        return sanitizePathSeg(stem) + ".lean";
      }
      return sanitizePathSeg(part);
    })
    .join("/");
}

function endsInUnaryIntervalSum(name) {
  return /(?:T?Sum|Prod)I(?:io|oi|ic|ci)$/.test(name || "");
}
function isBinaryIntervalCtor(name) {
  return /^I[co][co]$/.test(name || "");
}
function joinHeadArgs(headName, argNames) {
  if (!argNames.length) return headName;
  if (isBinaryIntervalCtor(headName)) {
    const [first, ...rest] = argNames;
    let acc = headName + first;
    if (rest.length) acc = acc + "_" + rest.reduce(joinDigits);
    return acc;
  }
  return headName + "_" + argNames.reduce(joinDigits);
}
function joinDigits(a, b) {
  if (/\d$/.test(a) && /^\d/.test(b)) return a + "'" + b;
  if (endsInUnaryIntervalSum(a)) return a + "_" + b;
  return a + b;
}

function isConstNode(node) {
  const n = unwrapParen(node);
  const c = cls(n);
  if (c === "LeanToken") return /^-?\d+(\.\d+)?$/.test(n.text || "") || n.text === "π" || n.text === "∞";
  if (c === "LeanAdd" || c === "LeanSub" || c === "LeanMul" || c === "LeanDiv" || c === "LeanPow" || c === "LeanNeg" || c === "LeanInv" || c === "Lean_sqrt") {
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

function isSingleTokenName(name) {
  return /^[A-Z][a-z0-9]*$/.test(name || "");
}

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
    if (!ascribed && n.args.length === 2 && cls(n.args[1]) === "LeanProperty" && cls(n.args[1].args?.[0]) === "LeanToken" && cls(n.args[1].args?.[1]) === "LeanToken") return true;
    return n.args.slice(1).every((x) => cls(x) === "LeanToken" &&
      (ascribed ? isLeafName(x.text, opts.leaves) : opts.typeLeaves ? opts.typeLeaves.has(x.text) : isLeafName(x.text, opts.leaves)));
  }
  if (c === "LeanArgsSpaceSeparated" && qualHeadText(n.args?.[0]) && cls(n.args[0]) === "LeanProperty" && !ascribed && n.args.length === 2) {
    const x = n.args[1];
    if (cls(x) === "LeanProperty" && cls(x.args?.[0]) === "LeanToken" && cls(x.args?.[1]) === "LeanToken") return true;
  }
  return false;
}

function funBodyUnary(funNode) {
  const f = unwrapParen(funNode);
  const arrow = f?.args?.[f.args.length - 1];
  const body = unwrapParen(arrow?.args?.[arrow.args.length - 1]);
  const c = cls(body);
  if (isBigOp(body)) return true;
  if (c === "LeanPow" && cls(body.args?.[1]) === "LeanToken" && body.args[1].text === "2") return true;
  return c === "LeanArgsSpaceSeparated" && cls(body.args?.[0]) === "LeanToken" && /^[A-Z]/.test(body.args[0].text || "");
}

function condExpArg(node) {
  if (cls(node) !== "LeanGetElem") return null;
  const h = node.args?.[0];
  if (cls(h) === "LeanToken" && (h.text === "ℙ" || h.text === "𝔼")) return null;
  const idx = node.args?.[1];
  if (cls(idx) === "LeanBitOr") return idx.args?.[0];
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

function fnLikeHead(head) {
  const h = unwrapParen(head);
  const c = cls(h);
  return c === "LeanPreimage" || !!condExpArg(h) || isArgMaxMinGetElem(h) || c === "Lean_argmax" || c === "Lean_argmin";
}

function normHead(head, opts) {
  const h = head;
  if (cls(h) === "LeanGetElem" && !condExpArg(h)) {
    const t = h.args?.[0];
    if (cls(t) === "LeanToken" && /^[A-Z]/.test(t.text || "") && !isLeafName(t.text, opts.leaves)) return t;
  }
  return h;
}

const ARITH_OP = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanInv", "LeanMatMul"]);

const COND_SUFFIX = "Cond";
const PROB_COND = "Prob" + COND_SUFFIX;
const EXPECT_COND = "Expect" + COND_SUFFIX;

function isGetIndexNoise(node, opts) {
  const u = unwrapParen(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") {
    const t = u.text || "";
    return !t || t === "_" || isLeafName(t, opts?.leaves);
  }
  if (c === "LeanParenthesis" || c === "LeanColon" || ARITH_OP.has(c))
    return (u.args || []).length > 0 && (u.args || []).every((a) => isGetIndexNoise(a, opts));
  return false;
}

function isBinderGetAtLiteral(node, opts) {
  if (cls(node) !== "LeanGetElem") return false;
  if (!isBinderHole(node.args?.[0], opts)) return false;
  const idx = unwrapParen(node.args?.[1]);
  if (!idx || cls(idx) !== "LeanToken") return false;
  const t = idx.text || "";
  return /^-?\d+(\.\d+)?$/.test(t) || t === "π" || t === "∞";
}

function isQuantBinderHole(node, opts) {
  const u = unwrapParen(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") {
    const t = u.text || "";
    return !t || t === "_" || isLeafName(t, opts?.quantLeaves);
  }
  if (c === "LeanAdjoint" || c === "LeanTranspose" || c === "LeanConj" || c === "LeanInv")
    return isQuantBinderHole(u.args?.[0], opts);
  if (c === "LeanGetElem") {
    return isQuantBinderHole(u.args?.[0], opts) && isGetIndexNoise(u.args?.[1], opts);
  }
  if (c === "LeanParenthesis") return isQuantBinderHole(u.args?.[0], opts);
  return false;
}

function isBinderHole(node, opts) {
  const u = unwrapParen(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") {
    const t = u.text || "";
    return !t || t === "_" || isLeafName(t, opts?.leaves);
  }
  if (c === "LeanAdjoint" || c === "LeanTranspose" || c === "LeanConj" || c === "LeanInv")
    return isQuantBinderHole(u.args?.[0], opts);
  if (c === "LeanGetElem") {
    return isBinderHole(u.args?.[0], opts) && isGetIndexNoise(u.args?.[1], opts);
  }
  if (c === "LeanParenthesis") return isBinderHole(u.args?.[0], opts);
  return false;
}

function unwrapStmt(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  return n;
}

function isHoleyExpr(node, opts) {
  const u = unwrapParen(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") {
    const t = u.text || "";
    return !t || t === "_" || isLeafName(t, opts?.leaves) || /^-?\d+$/.test(t);
  }
  if (c === "LeanAdjoint" || c === "LeanTranspose" || c === "LeanConj" || c === "LeanInv")
    return isQuantBinderHole(u.args?.[0], opts) && isHoleyExpr(u.args?.[0], opts);
  if (c === "LeanGetElem") {
    return isHoleyExpr(u.args?.[0], opts) && isGetIndexNoise(u.args?.[1], opts);
  }
  if (c === "LeanVecNotation") return true;
  if (c === "LeanParenthesis" || c === "LeanColon") return isHoleyExpr(u.args?.[0], opts);
  if (ARITH_OP.has(c)) return (u.args || []).length > 0 && (u.args || []).every((a) => isHoleyExpr(a, opts));
  if (c === "LeanArgsSpaceSeparated") return (u.args || []).length > 0 && (u.args || []).every((a) => isHoleyExpr(a, opts));
  return false;
}

function isHoleAndConjunct(node, opts) {
  const n = unwrapStmt(node);
  if (!n) return true;
  const c = cls(n);
  if (c === "LeanToken") return isLeafName(n.text, opts?.leaves);
  if (c === "Lean_land" || c === "Lean_lor")
    return isHoleAndConjunct(n.args?.[0], opts) && isHoleAndConjunct(n.args?.[1], opts);
  if (c === "Lean_forall" || c === "Lean_exists") {
    const body = c === "Lean_forall"
      ? peelGuardForalls(n.args?.[n.args.length - 1])
      : n.args?.[n.args.length - 1];
    return isHoleAndConjunct(body, opts);
  }
  if (c === "Lean_rightarrow") return isHoleAndConjunct(n.args?.[1], opts);
  if (c === "Lean_lnot") return isHoleAndConjunct(n.args?.[n.args.length - 1], opts);
  if (CLASS_TOKEN[c] && c !== "Lean_land" && c !== "Lean_lor" && c !== "Lean_forall" && c !== "Lean_exists" && c !== "Lean_lnot") {
    const args = n.args || [];
    return args.length > 0 && args.every((a) => isHoleyExpr(a, opts));
  }
  return isHoleyExpr(n, opts);
}

function isAtomicHoleAndConjunct(node, opts) {
  const n = unwrapStmt(node);
  if (cls(n) === "Lean_land" || cls(n) === "Lean_lor") return false;
  return isHoleAndConjunct(node, opts);
}

function isHoleAndTree(node, opts) {
  const n = unwrapStmt(node);
  return cls(n) === "Lean_land" && isHoleAndConjunct(n, opts);
}

function fillHoleAndConjunct(node, opts) {
  const n = unwrapStmt(node);
  if (!n) return "";
  const c = cls(n);
  if (c === "Lean_forall" || c === "Lean_exists" || c === "Lean_rightarrow" || c === "Lean_lnot") return "";
  const filled = nameExpr(n, { ...opts, keepDecorOnBinder: true });
  if (!filled) return "";
  if (!/(?:Mul|MatMul|Adjoint|Transpose|(?:^|_)T(?=_|$)|Conj)/.test(filled)) return "";
  return filled;
}

function fillHoleAndConjunctAlts(node, opts) {
  const n = unwrapStmt(node);
  if (!n) return [];
  const c = cls(n);
  if (c === "Lean_forall" || c === "Lean_exists" || c === "Lean_rightarrow" || c === "Lean_lnot") return [];
  const alts = nameExprAlts(n, { ...opts, keepDecorOnBinder: true });
  return uniq((alts || []).filter((a) => a && /(?:Mul|MatMul|Adjoint|Transpose|(?:^|_)T(?=_|$)|Conj)/.test(a)));
}

function nameAndOr(join, left, right) {
  if (left && right) return left + join + right;
  if (!left && !right) return join + "__";
  if (!left && right) return join + "_" + right;
  if (left && !right) return left + "_" + join;
  return join;
}

function applyEvalPrefix(head) {
  if (fnLikeHead(head)) return "";
  if (cls(unwrapParen(head)) === "LeanVecNotation") return "";
  const h = unwrapParen(head);
  if (cls(h) === "LeanGetElem" && cls(h.args?.[0]) === "LeanToken" && (h.args[0].text === "ℙ" || h.args[0].text === "𝔼")) return "";
  if (cls(h) === "Lean_Expect" || cls(h) === "Lean_Prob" || cls(h) === "Lean_Var") return "";
  return "Get";
}

function aeEqAtom(body) {
  if (!body || typeof body !== "string") return "";
  const m = /^([^/]+)\/eq\/(.+)$/.exec(body);
  if (m) return "Ae_Eq" + m[1];
  if (/^Eq(?![a-z])/.test(body) && !body.includes("/")) return "Ae_" + body;
  return "";
}

function argJoinAlts(acc, a, alts, opts) {
  const u = unwrapParen(a);
  const ac = cls(a);
  const compound = ac !== "LeanToken" && ac !== "LeanProperty" && !(ac === "LeanParenthesis" && cls(u) === "LeanToken");
  const fun = cls(u) === "Lean_fun";
  const simple = isSimpleArg(a, opts) || isConstNode(a);
  const opArg = ARITH_OP.has(cls(u));
  const snake = (h, c) => h + "_" + c;
  let next = compound && (simple || fun)
    ? uniq([...cartJoin(acc, alts, joinHeadChild), ...cartJoin(acc, alts, snake)])
    : cartJoin(acc, alts, compound && !opArg ? snake : joinHeadChild);
  if (fun && alts.includes("Fun")) next = uniq([...cartJoin(acc, ["Fun"], (h, c) => h + c), ...next]);
  if (cls(u) === "LeanProperty") {
    const snakeTok = [];
    for (const h of acc) for (const c of alts) {
      if (isSingleTokenName(h) && isSingleTokenName(c)) snakeTok.push(h + "_" + c);
    }
    if (snakeTok.length) next = uniq([...snakeTok, ...next]);
  }
  const optional = fun || (cls(u) === "LeanToken" && /^\d+$/.test(u.text || ""));
  if (compound && !simple && !fun && opts.__embedHead) next = uniq([...next, ...cartJoin(acc, alts, joinHeadChild)]);
  return optional ? uniq([...next, ...acc]) : next;
}

const CONST_TOKENS = new Set(["univ", "⊤", "⊥", "∅"]);
function leafHeadConstArgs(args, opts) {
  const out = [];
  for (const a of args) {
    const u = unwrapParen(a);
    const c = cls(u);
    const isConst = (c === "LeanProperty" && cls(u.args?.[0]) === "LeanToken" && /^[A-Z]/.test(u.args[0].text || "") && cls(u.args?.[1]) === "LeanToken") ||
      (c === "LeanToken" && CONST_TOKENS.has(u.text) && !isLeafName(u.text, opts.leaves));
    if (!isConst) continue;
    const n = c === "LeanProperty" ? nameToken(u.args[1].text) : nameToken(u.text);
    if (n) out.push(n);
  }
  return out;
}

function rel0VsZeroHoleLeft(tag, left) {
  if (!(tag === "Lt" || tag === "Gt") || !left) return "";
  if (!(/__$/.test(left) || /Joint$/.test(left))) return "";
  const focus = String(left).replace(/__+$/, "");
  if (!focus) return "";
  return (tag === "Lt" ? "Gt0" : "Lt0") + focus;
}

function glueNumSuffix(left, dig) {
  if (/__$/.test(left || "")) return String(dig);
  return (/Joint$/.test(left || "") ? "__" : "_") + dig;
}

function glueRelTail(left, right) {
  if (/^\d+$/.test(right || "")) return glueNumSuffix(left, right);
  if (/__$/.test(left || "")) return right;
  return "_" + right;
}

function leftEndsInBinSnake(node) {
  const u = unwrapParen(node);
  const c = cls(u);
  if (c === "LeanPreimage" || c === "LeanInner") return true;
  if (c === "LeanParenthesis") return leftEndsInBinSnake(u.args?.[0]);
  if (c === "LeanArgsSpaceSeparated") {
    const head = u.args?.[0];
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^(real|toReal)$/.test(head.args[1].text || ""))
      return (u.args || []).slice(1).some(leftEndsInBinSnake);
    if (fnLikeHead(head)) return true;
    return leftEndsInBinSnake(head);
  }
  return false;
}

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

function isSumIntervalDom(name) {
  return /^I(?:[co][co]|ic|io)$/.test(name || "");
}

function intervalCtorName(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanArgsSpaceSeparated") u = unwrapParen(u.args?.[0]);
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && /^I[co][co]$/.test(u.args[1].text || ""))
    return u.args[1].text;
  if (cls(u) === "LeanToken" && /^I[co][co]$/.test(u.text || "")) return u.text;
  return "";
}

function sumDomainName(node) {
  const bind = (node.args || []).slice(0, -1).find((b) => cls(b) === "Lean_in" || cls(b) === "LeanIn");
  if (!bind) return "";
  let set = unwrapParen(bind.args?.[1]);
  if (cls(set) === "LeanArgsSpaceSeparated") set = unwrapParen(set.args?.[0]);
  if (cls(set) === "LeanProperty" && cls(set.args?.[1]) === "LeanToken") {
    const t = set.args[1].text || "";
    if (isSumIntervalDom(t) || t === "range") return nameToken(t);
  }
  if (cls(set) === "LeanToken" && set.text && !/^_/.test(set.text)) {
    const t = set.text;
    if (isSumIntervalDom(t) || t === "range") return nameToken(t);
  }
  return "";
}

function eqSumRangeNumName(node, opts) {
  if (!opts?.asGiven) return "";
  const u = unwrapParen(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return "";
  const rhs = unwrapParen(u.args[1]);
  if (cls(rhs) !== "LeanToken" || !/^\d+$/.test(rhs.text || "")) return "";
  const sum = unwrapParen(u.args[0]);
  if (!bigOpDomainAtom(sum)) return "";
  if (sumDomainName(sum) !== "Range") return "";
  const body = nameExpr(sum.args[sum.args.length - 1], { ...opts, asGiven: false });
  if (body) return "";
  const sumAtom = sumRangeArityName(sum, opts);
  if (!sumAtom) return "";
  return "Eq" + sumAtom + rhs.text;
}
function sumRangeArityName(node, opts) {
  if (!opts?.asGiven) return "";
  const u = unwrapParen(node);
  const tag = bigOpDomainAtom(u);
  if (!tag) return "";
  if (sumDomainName(u) !== "Range") return "";
  const body = nameExpr(u.args[u.args.length - 1], { ...opts, asGiven: false });
  if (body) return "";
  return tag + "Range__";
}

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
function derivPowAppName(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return "";
  return derivPowName(u.args?.[0]);
}

function isIntervalLeafAlt(name) {
  return /^I[co][co](?:0'1|[01])?$/.test(name || "");
}

function isCamelIntervalRel(name) {
  return /^(Ae)?(In|Subset)I[co][co]/.test(name || "");
}

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

function isNamespacedConst(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken") return false;
  const obj = u.args?.[0];
  if (cls(obj) === "LeanToken") return /^[A-Z]/.test(obj.text || "");
  return isModulePathReceiver(obj);
}

function isTypeAscriptionExpr(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanColon") return true;
  if (cls(u) === "LeanArgsSpaceSeparated") return (u.args || []).some((a) => cls(unwrapParen(a)) === "LeanColon");
  return false;
}

const REL_SPLIT_SOFT = "eq|le|lt|gt|ge|ne|sub|is";
const REL_SPLIT_HAS = new RegExp(`/(${REL_SPLIT_SOFT})/`);
const REL_SPLIT_EXACT = new RegExp(`^([^/]+)/(${REL_SPLIT_SOFT})/([^/]+)$`);
const REL_SPLIT_TAG = { eq: "Eq", le: "Le", lt: "Lt", gt: "Gt", ge: "Ge", ne: "Ne", sub: "Subset", is: "Iff" };

function relSplitInline(name) {
  const m = REL_SPLIT_EXACT.exec(name || "");
  if (!m) return "";
  return REL_SPLIT_TAG[m[2]] + m[1] + "_" + m[3];
}

function inlineSlashEq(body) {
  const raw = String(body || "").split(".eq.").join("/eq/");
  const m = /^([^/]+)\/eq\/([^/]+)$/.exec(raw);
  if (!m) return "";
  let left = m[1];
  let prefix = "";
  const q = /^(Any|All)_(.+)$/.exec(left);
  if (q) {
    prefix = q[1] + "_";
    left = q[2];
  }
  if (!left || /^(?:Any|All)_/.test(left)) return "";
  return prefix + "Eq" + left + "_" + m[2];
}

function hasQuantEqSlash(p) {
  const s = String(p || "").replace(/\\/g, "/").replace(/\.lean$/, "").split(".eq.").join("/eq/");
  return /(?:^|\/)(?:Any|All)_[^/]+\/eq\//.test(s);
}

function quantWrapEqBody(tag, body) {
  const inlined = inlineSlashEq(body);
  if (inlined) return /^(?:Any|All)_/.test(inlined) ? inlined : tag + "_" + inlined;
  if (hasQuantEqSlash(body)) return "";
  return "";
}

function mentionsUpdateCol(node) {
  let found = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "LeanToken" && n.text === "updateCol") { found = true; return; }
    for (const a of n.args || []) walk(a);
  })(node);
  return found;
}

function expectProbVarBoundScope(node) {
  const u = unwrapParen(node);
  const c = cls(u);
  if (c !== "Lean_Expect" && c !== "Lean_Prob" && c !== "Lean_Var") return null;
  return { bound: u.bound ?? u.args?.[0] ?? null, scope: u.scope ?? null, kind: c };
}

function legacyExpectProbVarApp(node, opText) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 2) return null;
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === opText))
    return null;
  return { bound: head.args?.[1] ?? null, scope: u.args[1], head, args: u.args };
}

function isVarApp(node) {
  if (expectProbVarBoundScope(node)?.kind === "Lean_Var") return true;
  return !!legacyExpectProbVarApp(node, "𝕍𝕒𝕣");
}

const LIMITS_BIGOP_KIND = {
  Lean_max: "Max",
  Lean_min: "Min",
  Lean_sup: "Sup",
  Lean_inf: "Inf",
  Lean_argmax: "ArgMax",
  Lean_argmin: "ArgMin",
};
const LIMITS_LEGACY_OP_TEXT = {
  max: "Max",
  min: "Min",
  sup: "Sup",
  inf: "Inf",
  "max⁻¹": "ArgMax",
  "min⁻¹": "ArgMin",
};

function limitsBigOpBoundScope(node) {
  const u = unwrapParen(node);
  const c = cls(u);
  if (!LIMITS_BIGOP_KIND[c]) return null;
  const pathToken = u.pathToken;
  return { bound: u.bound ?? u.args?.[0] ?? null, scope: u.scope ?? null, kind: c, pathToken };
}

function legacyLimitsBigOpApp(node, opText) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 2) return null;
  const head = u.args[0];
  if (!(cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === opText))
    return null;
  const pathToken = LIMITS_LEGACY_OP_TEXT[opText] || "";
  return { bound: head.args?.[1] ?? null, scope: u.args[1], head, args: u.args, pathToken, opText };
}

function limitsBigOpFuseName(tok, bodyName) {
  if (!tok) return "";
  if (tok === "ArgMax" || tok === "ArgMin") return tok;
  if (!bodyName) return tok;
  return bodyName === "Mul" ? tok + "_Mul" : tok + bodyName;
}

function relationAlts(node, tag0, opts) {
  const args = node.args || [];
  const ae = node.superscript === "ᵐ";
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
    const pairs = [];
    for (let i = 0; i < L.length; i++) for (let j = 0; j < R.length; j++) pairs.push([i + j, i, j]);
    pairs.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const [, i, j] of pairs) {
      {
        const l = L[i];
        const r = R[j];
        if (!l || !r) continue;
        if (l === r && (tag === "Eq" || tag === "Iff")) out.push(l);

        if (l === r && tag !== "Eq" && tag !== "Iff") out.push(T(tag) + l);

        if (l === r && !l.includes("/")) out.push(T(tag) + (pluralSnakeS(l) || pluralLetterS(l) || pluralMidS(l)));

        {
          if (opts.asGiven && opts.multiGiven && !String(l).includes("/") && !String(r).includes("/")) {
            if (!(/^\d+$/.test(l) && (tag === "Lt" || tag === "Gt")))
              out.push(T(tag) + l + glueRelTail(l, r));
          }
          if (r === "0" && (soft === "gt" || soft === "lt")) out.push(l + "/" + (soft === "gt" ? "Gt_0" : "Lt_0"));
          if (l === "0" && (soft === "gt" || soft === "lt")) out.push(r + "/" + (soft === "lt" ? "Gt_0" : "Lt_0"));
          if (!(opts.asGiven && opts.multiGiven)) out.push(l + "/" + soft + "/" + r);
        }
        if (opts.asGiven && /^Deriv\d+$/.test(l) && r === "0" && (tag === "Lt" || tag === "Gt")) {
          out.push((tag === "Lt" ? "Gt0" : "Lt0") + l);
        }
        if (opts.asGiven && r === "0" && (tag === "Lt" || tag === "Gt")) {
          const rel0 = rel0VsZeroHoleLeft(tag, l);
          if (rel0) out.push(rel0);
        }
        if (opts.asGiven && /^\d+$/.test(r) && leftEndsInBinSnake(args[0])) {
          out.push(T(tag) + r + binSnakeLeftName(args[0], l));
        } else if (opts.asGiven && isNamespacedConst(args[1])) {
          out.push(T(tag) + l + r);
          out.push(T(tag) + l + glueRelTail(l, r));
        } else if (opts.asGiven && (isTypeAscriptionExpr(args[0]) || isTypeAscriptionExpr(args[1]))) {
          out.push(T(tag) + l + r);
          out.push(T(tag) + l + glueRelTail(l, r));
        } else if ((tag === "In" || tag === "Subset") && isIntervalLeafAlt(r)) {
          out.push(T(tag) + l + "_" + r);
        } else {
          out.push(T(tag) + l + r);
          if (!/^\d+$/.test(l)) out.push(l + T(tag) + r);
          if (l !== r && l.startsWith(r)) out.push(T(tag) + l);
          if (!(/^\d+$/.test(l) && (tag === "Lt" || tag === "Gt")))
            out.push(T(tag) + l + glueRelTail(l, r));
        }
      }
    }
    if (!L.length && R.length) {
      for (const r of R) {
        out.push(T(tag) + "_" + r);
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
    if (!L.length && !R.length) {
      const funSide = cls(unwrapParen(args[0])) === "Lean_fun" || cls(unwrapParen(args[1])) === "Lean_fun";
      out.push(!funSide && cls(node) === "Lean_cdotp" ? "Dot__" : T(tag));
    }
    if (tag === "Subset") {
      if (!R.length) for (const l of L) out.push(l);
      if (!L.length) for (const r of R) out.push(r);
      for (const l of L) if (R.includes(l)) out.push(T(tag));
    }
    if (opts.section && L.includes(opts.section) && !gen.__inner) {
      gen.__inner = true;
      try { out.push(...gen(tag, [], R)); } finally { gen.__inner = false; }
    }
    return out;
  };
  const mirror = MIRROR_REL[tag0] && isConstNode(args[0]) && !isConstNode(args[1]);
  if (tag0 === "Eq" && args.every((a) => cls(unwrapParen(a)) === "LeanColon") && args.some((a) => isCoeAscription(unwrapParen(a))))
    return uniq([...gen(tag0, leftAlts, rightAlts), "Coe"]);
  if (cls(unwrapParen(args[0])) === "Lean_lim") {
    const limNode = unwrapParen(args[0]);
    const bodyNode = limNode.args?.[limNode.args.length - 1];
    const bodyCanon = nameExpr(bodyNode, opts);
    const prefer = [];
    if (bodyCanon.startsWith("Prob") && bodyCanon !== "Prob") {
      const head = "Lim_" + bodyCanon;
      for (const r of rightAlts) prefer.push(head + "/" + S(tag0) + "/" + r);
      if (!rightAlts.length) prefer.push(head);
    }
    const limOut = [];
    const bodyAlts = nameExprAlts(bodyNode, opts);
    const lims = bodyAlts.length ? bodyAlts.map((b) => "Lim/" + b) : ["Lim"];
    const rc = isConstNode(args[1]) ? rightAlts : [];
    for (const l of lims) { for (const r of rc) limOut.push(T0(tag0) + "_" + r + "/" + l); limOut.push(T0(tag0) + "/" + l); }
    for (const r of rightAlts) limOut.push(T0(tag0) + "_" + r);
    return uniq([...prefer, ...gen(tag0, leftAlts, rightAlts), ...limOut]);
  }
  const isFun = (n) => cls(unwrapParen(n)) === "Lean_fun";
  const dropped = isFun(args[1]) && !isFun(args[0]) ? gen(tag0, leftAlts, []) : isFun(args[0]) && !isFun(args[1]) ? gen(tag0, [], rightAlts) : [];
  let outR = uniq([...(mirror ? gen(MIRROR_REL[tag0], rightAlts, leftAlts) : []), ...dropped, ...gen(tag0, leftAlts, rightAlts)]);
  if (opts.asGiven && tag0 === "Eq") {
    const eqRange = eqSumRangeNumName(node, opts);
    if (eqRange) {
      outR = uniq([eqRange, ...outR.filter((a) => a !== eqRange && !/^Eq__Sum__Range_?\d+$/.test(a) && !/^EqSumRange_?\d+$/.test(a) && !/^EqSum_?\d+$/.test(a))]);
    }
  }
  if (opts.asGiven && tag0 === "Subset") {
    const iv = intervalCtorName(args[1]);
    if (iv) {
      const pref = "Subset_" + iv;
      outR = uniq([pref, ...outR.filter((a) => a !== pref && !isCamelIntervalRel(a))]);
    }
  }
  if ((tag0 === "In" || tag0 === "Subset") && intervalCtorName(args[1])) {
    outR = outR.filter((a) => !isCamelIntervalRel(a));
  }
  if (opts.asGiven && leftEndsInBinSnake(args[0]) && isConstNode(args[1])) {
    const dig = nameExpr(args[1], opts);
    const tUse = (MIRROR_REL[tag0] && isConstNode(args[0]) && !isConstNode(args[1])) ? MIRROR_REL[tag0] : tag0;
    const pref = (ae ? "Ae" : "") + tUse + dig + "Real_Preimage";
    outR = outR.filter((a) => !/PreimageS/.test(a) && !(/Preimage/.test(a) && /_\d+$/.test(a)));
    if (dig && !outR.includes(pref)) outR.unshift(pref);
  }
  if (tag0 === "Eq" && eqJointSides(node)) {
    const i = outR.indexOf("Eq");
    if (i >= 0) outR.splice(i + 1, 0, "Eq_Joint");
    else outR.push("Eq_Joint");
    outR = uniq(["Eq_Joint", ...outR.filter((a) => a !== "Eq_Joint")]);
  }
  if (tag0 === "Eq" && isVarApp(args[0])) {
    const varEq = outR.filter((a) => a === "EqVar" || a.startsWith("EqVar"));
    outR = uniq([...varEq, ...outR.filter((a) => !varEq.includes(a)), "Eq"]);
  }
  if (!opts.asGiven && tag0 === "Eq" && mentionsUpdateCol(node)) {
    const i = outR.indexOf("EqSMul");
    if (i >= 0) outR = uniq([...outR.slice(0, i + 1), "EqSMul_UpdateCol", ...outR.slice(i + 1)]);
  }
  return outR;
}

const isFunNode = (n) => cls(unwrapParen(n)) === "Lean_fun";
function meqFuse(side) {
  if (!side) return "MEq";
  if (side === "ExpectS" || side.startsWith("ExpectS_")) return "MEq" + side;
  if (side.includes("_")) return "MEq_" + side;
  if (side === "Expect") return "MEqExpect";
  if (/^Expect/.test(side)) return "MEq_" + side;
  return "MEq_" + side;
}
function isIllegalMeqImplySeg(seg, multi = false) {
  if (!seg) return false;
  if (seg === "MEqExpect") return !!multi;

  if (!/^MEqExpect/.test(seg)) return false;
  return !(seg === "MEqExpectS" || seg.startsWith("MEqExpectS_"));
}
function hasIllegalMeqImply(path) {
  const segs = String(path || "").split("/").filter(Boolean);
  const multi = segs.length > 1;
  return segs.some((s) => isIllegalMeqImplySeg(s, multi));
}
function hasIllegalDistributedAddSnake(path) {
  const segs = String(path || "").replace(/\\/g, "/").replace(/\.lean$/, "").split("/").filter(Boolean);
  for (let i = 0; i + 1 < segs.length; i++) {
    if (segs[i] === "Distributed" && segs[i + 1] === "Add") return true;
  }
  return false;
}
function hasIllegalDistributedGaussianLower(path) {
  const segs = String(path || "").replace(/\\/g, "/").replace(/\.lean$/, "").split("/").filter(Boolean);
  return segs.some((s) => /gaussian/.test(s) && !/Gaussian/.test(s) && /Distributed/.test(s));
}
function meqAlts(node, opts) {
  const args = node.args || [];
  const L = nameExprAlts(args[0], opts);
  const R = nameExprAlts(args[1], opts);
  const fuse = (side) => meqFuse(side);
  const gen = (L, R) => {
    const out = [];
    const pairs = [];
    for (let i = 0; i < L.length; i++) for (let j = 0; j < R.length; j++) pairs.push([i + j, i, j]);
    pairs.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const [, i, j] of pairs) {
      const l = L[i], r = R[j];
      if (!l || !r) continue;
      if (l === r) {
        out.push(fuse(l), l);
        if (!l.includes("/")) {
          const pl = pluralSnakeS(l) || pluralLetterS(l) || pluralMidS(l);
          if (pl) out.push(fuse(pl));
        }
      } else {
        out.push("MEq_" + l + "_" + r);
        if (l.startsWith(r)) out.push(fuse(l));
      }
      out.push(l + "/ae/" + r);
    }
    if (!L.length) for (const r of R) out.push(fuse(r));
    if (!R.length) for (const l of L) out.push(fuse(l));
    if (!L.length && !R.length) out.push("MEq");
    return out;
  };
  const f0 = isFunNode(args[0]), f1 = isFunNode(args[1]);
  const dropped = f0 && f1 ? gen([], []) : f1 ? gen(L, []) : f0 ? gen([], R) : [];
  const raw = uniq([...gen(L, R), ...dropped].filter(Boolean));
  return raw.filter((s) => !hasIllegalMeqImply(s));
}
function meqCanon(node, opts) {
  const args = node.args || [];
  const f0 = isFunNode(args[0]), f1 = isFunNode(args[1]);
  if (f0 && f1) return "MEq";
  const left = f0 ? "" : nameExpr(args[0], opts);
  const right = nameExpr(args[1], opts);
  if (left && right) {
    if (left === right) {
      const plural = pluralSnakeS(left) || pluralLetterS(left) || pluralMidS(left);
      if (plural) return meqFuse(plural);
      return meqFuse(left);
    }
    return "MEq_" + left + "_" + right;
  }
  if (right) return meqFuse(right);
  if (left) return meqFuse(left);
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
  if (tag === "Eq" && eqJointSides(node)) return "Eq_Joint";
  if (opts.asGiven && tag === "Eq") {
    const eqRange = eqSumRangeNumName(node, opts);
    if (eqRange) return eqRange;
  }
  if (left && right) {
    if (left === right && (tag === "Eq" || tag === "Iff")) return left;
    if (opts.asGiven) {
      const iv = tag === "Subset" ? intervalCtorName(args[1]) : "";
      if (iv) return "Subset_" + iv;
      if (/^\d+$/.test(right) && leftEndsInBinSnake(args[0])) return T + right + binSnakeLeftName(args[0], left);
      if (isNamespacedConst(args[1]) || isTypeAscriptionExpr(args[0]) || isTypeAscriptionExpr(args[1])) return T + left + right;
      if (/^Deriv\d+$/.test(left || "") && right === "0" && (tag === "Lt" || tag === "Gt")) {
        return (tag === "Lt" ? "Gt0" : "Lt0") + left;
      }
      if (right === "0" && (tag === "Lt" || tag === "Gt")) {
        const rel0 = rel0VsZeroHoleLeft(tag, left);
        if (rel0) return rel0;
      }
      if (left === right && !String(left).includes("/")) {
        const pl = pluralSnakeS(left);
        if (pl) return T + pl;
      }
      if (/__$/.test(left) && /^(?:Mul|Dot|SMul|MatMul|MulVec)/.test(left))
        return T + "_" + left + glueRelTail(left, right);
      return T + left + glueRelTail(left, right);
    }
    if (right === "0" && (soft === "gt" || soft === "lt")) return left + "/" + (soft === "gt" ? "Gt_0" : "Lt_0");
    if (left === "0" && (soft === "gt" || soft === "lt")) return right + "/" + (soft === "lt" ? "Gt_0" : "Lt_0");
    return left + "/" + soft + "/" + right;
  }
  if (!left && right) return snakeFocus(T, right);
  if (left && !right) {
    const m = mirroredFocus(tag, left);
    return m ? (ae ? "Ae" : "") + m : T + (left === "One" ? "1" : left);
  }
  if (cls(node) === "Lean_cdotp") return "Dot__";
  return T;
}

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
function isInftyToken(n) {
  const u = unwrapParen(n);
  return cls(u) === "LeanToken" && (u.text === "∞" || u.text === "oo");
}
function isSupLtInfty(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "Lean_lt" || (u.args || []).length !== 2) return false;
  if (!isInftyToken(u.args[1])) return false;
  let lhs = unwrapParen(u.args[0]);
  if (limitsBigOpBoundScope(lhs)?.kind === "Lean_sup") return true;
  const head = cls(lhs) === "LeanArgsSpaceSeparated" ? lhs.args?.[0] : lhs;
  return cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "sup";
}
function isBddAboveSup(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return false;
  if (cls(u.args[0]) !== "LeanToken" || u.args[0].text !== "BddAbove") return false;
  let a = unwrapParen(u.args[1]);
  if (cls(a) === "LeanProperty" && cls(a.args?.[0]) === "LeanToken" && a.args[0].text === "Set") a = a.args[1];
  if (cls(a) === "LeanArgsIndented") a = a.args?.[0];
  if (cls(a) !== "LeanArgsSpaceSeparated") return false;
  const xs = a.args || [];
  if (xs.length === 2 && cls(xs[0]) === "LeanToken" && /^(Set\.)?range$/.test(xs[0].text || "") && cls(unwrapParen(xs[1])) === "Lean_fun") return true;
  return xs.length >= 2 && cls(unwrapParen(xs[0])) === "Lean_fun" && cls(xs[1]) === "LeanToken" && xs[1].text === "''";
}
function supBoundKind(node) {
  const u = unwrapParen(node);
  let body = null;
  if (isSupLtInfty(u)) {
    const lhs = unwrapParen(u.args[0]);
    const lim = limitsBigOpBoundScope(lhs);
    if (lim?.kind === "Lean_sup") body = lim.scope;
    else body = cls(lhs) === "LeanArgsSpaceSeparated" ? lhs.args?.[lhs.args.length - 1] : null;
  } else {
    let a = unwrapParen(u.args?.[1]);
    if (cls(a) === "LeanProperty") a = a.args?.[1];
    if (cls(a) === "LeanArgsIndented") a = a.args?.[0];
    const f = (a?.args || []).map(unwrapParen).find((x) => cls(x) === "Lean_fun");
    const r = f?.args?.[0];
    body = cls(r) === "LeanRightarrow" ? r.args?.[r.args.length - 1] : null;
  }
  const b = unwrapParen(body);
  const k = cls(b);
  if (k === "Lean_sum" || k === "Lean_int" || k === "LeanNorm" || k === "LeanAbs") return b?.pathToken || "";
  return "";
}
function supBoundCanon(node) {
  return supBoundKind(node) === "Sum" ? "GtInftySup_Sum" : "GtInftySup";
}
function supBoundAlts(node) {
  const k = supBoundKind(node);
  const canon = k === "Sum" ? "GtInftySup_Sum" : "GtInftySup";
  const out = [canon];
  if (k && ("GtInftySup_" + k) !== canon) out.push("GtInftySup_" + k);
  if (canon !== "GtInftySup") out.push("GtInftySup");
  out.push("LtSup__Infty");
  return out;
}
function peelHoleExpr(node) {
  let n = node;
  for (let i = 0; i < 12 && n; i++) {
    const c = cls(n);
    if (c === "LeanParenthesis") { n = n.args?.[0]; continue; }
    if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") { n = firstConclusion(n); continue; }
    if (c === "LeanColon") { n = n.args?.[0]; continue; }
    break;
  }
  return n;
}

function partialBoundScope(node) {
  if (!node) return null;
  const c = cls(node);
  if (c !== "Lean_partial" && c !== "LeanPartial") return null;
  if (node.bound != null || node.scope != null) {
    return { bound: node.bound ?? null, scope: node.scope ?? null };
  }
  const arg = node.arg ?? node.args?.[0];
  return { bound: null, scope: arg ?? null };
}

function partialPathAtom(node) {
  return partialBoundScope(node) ? node.pathToken : null;
}

function partialNameFromScope(node, opts = {}) {
  const ps = partialBoundScope(node);
  if (!ps) return "";
  const scopeName = nameExpr(ps.scope, opts) || "";
  if (!scopeName) return node.pathToken;
  return node.pathToken + "_" + scopeName;
}

function partialNameAltsFromScope(node, opts = {}, A) {
  const ps = partialBoundScope(node);
  if (!ps) return [];
  const bodies = typeof A === "function" ? A(ps.scope) : nameExprAlts(ps.scope, opts);
  const nonempty = (bodies || []).filter(Boolean);
  if (!nonempty.length) return [node.pathToken];
  return [...new Set([...nonempty.map((y) => node.pathToken + "_" + y), node.pathToken])];
}

function nablaBoundScope(node) {
  if (!node) return null;
  const c = cls(node);
  if (c !== "Lean_nabla" && c !== "LeanNabla") return null;
  if (node.bound != null || node.scope != null) {
    return { bound: node.bound ?? null, scope: node.scope ?? null };
  }
  return { bound: node.args?.[0] ?? null, scope: node.args?.[1] ?? null };
}

function nablaPathChoicesToGrad(choices) {
  const out = [];
  for (const raw of choices || []) {
    const s = String(raw ?? "");
    if (s === "Nabla" || s.startsWith("Nabla_") || /^Nabla[A-Z0-9]/.test(s)) {
      out.push("Grad" + s.slice("Nabla".length));
    } else {
      out.push(s);

    }
  }
  return out;
}

function nablaGradAlts(node, opts = {}) {
  if (!nablaBoundScope(node)) return [];
  let ch = [];
  if (typeof node.pathChoices === "function") {
    ch = nablaPathChoicesToGrad(node.pathChoices(opts) || []);
  }
  ch = [...new Set(ch.filter((x) => x != null))];
  if (!ch.includes("Grad") && !ch.includes("")) ch.push("Grad");
  const nonempty = ch.filter(Boolean);
  if (!nonempty.includes("Grad")) nonempty.unshift("Grad");
  return nonempty;
}

const HOLE_RE_ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanInv", "LeanMatMul"]);
const HOLE_RE_TRIG_FN = /^(sin|cos|tan|cot|arctan|log|exp)$/i;

export function implyHoleRegexFromAst(implyStmts, opts = {}) {
  const root = peelHoleExpr(implyStmts);
  if (!root) return "";
  const frag = holeRegexExpr(root, opts);
  if (frag == null || frag === "" || frag === "_") return "";
  return storeHoleGroups(frag);
}

function storeHoleGroups(raw) {
  const s = String(raw ?? "");
  if (!s.includes("(_|")) return s;
  return s.replace(/\(_\|/g, "(");
}

function requiredScopeParen(s, i) {
  if (/(?:Expect|Deriv|Integral)_$/.test(s.slice(Math.max(0, i - 16), i))) return true;
  if (s[i] === "(") {
    const close = holeRegexMatchingParen(s, i);
    if (close > i && splitTopHouse(s.slice(i + 1, close))) return true;
  }
  return false;
}

function expandOptionalParens(s) {
  let out = "";
  for (let i = 0; i < s.length; i++) {
    if (s.startsWith("(_)", i)) {
      out += "(_)";
      i += 2;
      continue;
    }
    if (s[i] === "(" && !requiredScopeParen(s, i)) out += "(_|";
    else out += s[i];
  }
  return out;
}

function expandHouseStoredGroups(s) {
  let out = "";
  let i = 0;
  while (i < s.length) {
    const delimLen = houseDelimLenAt(s, i);
    if (delimLen) {
      out += s.slice(i, i + delimLen);
      i += delimLen;
      continue;
    }
    if (s[i] === "(") {
      let depth = 1;
      let j = i + 1;
      while (j < s.length && depth > 0) {
        if (s[j] === "(") depth++;
        else if (s[j] === ")") depth--;
        if (depth > 0) j++;
      }
      out += "(" + expandOptionalParens(s.slice(i + 1, j)) + ")";
      i = j + 1;
      continue;
    }
    out += s[i];
    i++;
  }
  return out;
}

export function expandSimplifiedHoleOpts(reSource) {
  const s = String(reSource || "");
  if (!s || s.includes("(_|")) return s;
  if (sourceHasHouseDelim(s)) return expandHouseStoredGroups(s);
  if (!s.includes("(")) return s;
  return expandOptionalParens(s);
}

export function appendHoleRegexTrailingStar(reSource) {
  const s = String(reSource || "");
  if (!s) return s;
  const side = (part) => (part.endsWith("_*") ? part : part + "_*");
  const h = splitTopHouse(s);
  if (h) return side(h.left) + houseDelimSlash(h.soft) + side(h.right);
  return side(s);
}

export function parseHoleRegexTree(reSource) {
  const s = expandSimplifiedHoleOpts(reSource);
  let i = 0;
  function parseSeq() {
    const parts = [];
    while (i < s.length) {
      if (s[i] === ")") break;
      if (s.startsWith("(_|", i)) {
        i += 3;
        const inner = parseSeq();
        if (s[i] === ")") i++;
        parts.push({ kind: "opt", alts: inner });
      } else if (s.startsWith("(_)", i)) {
        i += 3;
        parts.push({ kind: "hole" });
      } else if (s[i] === "\\") {
        if (i + 1 < s.length) {
          parts.push({ kind: "lit", v: s[i + 1] });
          i += 2;
        } else {
          i++;
        }
      } else if (s[i] === "(") {
        i++;
        const inner = parseSeq();
        if (s[i] === ")") i++;
        parts.push({ kind: "group", kids: inner });
      } else if (s.startsWith("_*", i)) {
        i += 2;
        parts.push({ kind: "star" });
      } else {
        let start = i;
        while (
          i < s.length &&
          s[i] !== "(" &&
          s[i] !== ")" &&
          s[i] !== "\\" &&
          !s.startsWith("_*", i)
        ) i++;
        if (i > start) parts.push({ kind: "lit", v: s.slice(start, i) });
      }
    }
    return parts;
  }
  try {
    const tree = parseSeq();
    markNestedHouseGroups(tree);
    return tree;
  } catch {
    return [];
  }
}

export function holeRegexNodeDepth(node) {
  if (!node) return 0;
  if (node.kind === "lit") return 0;
  if (node.kind === "hole") return 1;
  if (node.kind === "opt") {
    const child = Math.max(0, ...(node.alts || []).map(holeRegexNodeDepth));
    return 1 + child;
  }
  if (node.kind === "group") {
    return Math.max(0, ...(node.kids || []).map(holeRegexNodeDepth));
  }
  if (node.kind === "star") return 0;
  return 0;
}

function holeRegexNodeTrailing(node) {
  if (!node) return { T: 0, U: null };
  if (node.kind === "lit") {
    const v = String(node.v || "");
    const trail = v.match(/_*$/)[0].length;
    return { T: trail, U: /^_*$/.test(v) ? v.length : null };
  }
  if (node.kind === "hole") return { T: 1, U: 1 };
  if (node.kind === "opt") {
    const fill = holeRegexSeqTrailing(node.alts || []);
    return { T: Math.max(1, fill.T), U: Math.max(1, fill.U == null ? 0 : fill.U) };
  }
  if (node.kind === "group") return holeRegexSeqTrailing(node.kids || []);
  if (node.kind === "star") return { T: 0, U: 0 };
  return { T: 0, U: null };
}

function holeRegexSeqTrailing(nodes) {
  let acc = { T: 0, U: 0 };
  for (const n of nodes || []) {
    const b = holeRegexNodeTrailing(n);
    let T = b.T;
    if (b.U != null) T = Math.max(T, acc.T + b.U);
    const U = acc.U != null && b.U != null ? acc.U + b.U : null;
    acc = { T, U };
  }
  return acc;
}

const trailingPadCache = new Map();

export function holeRegexTrailingPad(reSource) {
  if (reSource && typeof reSource === "object") {
    if (Number.isFinite(Number(reSource.pad))) return Number(reSource.pad);
    reSource = reSource.regex || reSource.expr || "";
  }
  const key = String(reSource || "");
  if (trailingPadCache.has(key)) return trailingPadCache.get(key);
  const pad = holeRegexSeqTrailing(parseHoleRegexTree(key)).T;
  trailingPadCache.set(key, pad);
  return pad;
}

export function holeRegexLastNodeDepth(reSource) {
  const tree = parseHoleRegexTree(reSource);
  if (!tree.length) return 0;
  const last = tree[tree.length - 1];
  let d = holeRegexNodeDepth(last);
  const src = String(reSource || "");
  if (sourceHasHouseDelim(src) && last && last.kind === "group") {
    d = Math.max(d, 1 + holeRegexNodeDepth(last));
  }
  return d;
}

export function normalizeHouseEqTokenToRegex(token, reSource) {
  let s = String(token || "");
  const re = String(reSource || "");
  if (splitTopHouse(re) || sourceHasHouseDelim(re)) {
    const h = splitTopHouse(s);
    if (h) s = h.left + houseDelimSlash(h.soft) + h.right;
  }
  return s;
}

export function houseEqStemToPath(stem) {
  const s = String(stem || "");
  const h = splitTopHouse(s);
  if (!h) return s;
  return h.left + houseDelimSlash(h.soft) + nestHouseDots(h.right);
}

function matchHoleRegexTreeToken(nodes, token) {
  const s = String(token || "");
  function matchSeq(seq, pos, edgeFilledOpt, edgeDigit) {
    if (!seq.length) return [{ pos, edgeFilledOpt, edgeDigit }];
    const [head, ...rest] = seq;
    const heads = matchNode(head, pos, edgeFilledOpt, edgeDigit);
    const out = [];
    for (const h of heads) {
      for (const r of matchSeq(rest, h.pos, h.edgeFilledOpt, h.edgeDigit)) out.push(r);
    }
    return out;
  }
  function matchNode(node, pos, edgeFilledOpt, edgeDigit) {
    if (!node) return [];
    if (node.kind === "lit") {
      const v = node.v || "";
      if (v && s.startsWith(v, pos)) return [{ pos: pos + v.length, edgeFilledOpt: false, edgeDigit: false }];
      if (!v) return [{ pos, edgeFilledOpt, edgeDigit }];
      return [];
    }
    if (node.kind === "hole") {
      if (s[pos] === "_") return [{ pos: pos + 1, edgeFilledOpt: false, edgeDigit: false }];
      return [];
    }
    if (node.kind === "opt") {
      const out = [];
      if (s[pos] === "_") out.push({ pos: pos + 1, edgeFilledOpt: false, edgeDigit: false });
      const tryAt = (start) => {
        for (const m of matchSeq(node.alts || [], start, false, false)) {
          const endsWithHole = m.pos > 0 && s[m.pos - 1] === "_";
          const endsDigit = m.pos > 0 && /\d/.test(s[m.pos - 1]);
          out.push({ pos: m.pos, edgeFilledOpt: !endsWithHole, edgeDigit: !endsWithHole && endsDigit });
        }
      };
      if (edgeFilledOpt) {
        if (s[pos] === "_") tryAt(pos + 1);
        else if (edgeDigit && /\d/.test(s[pos] || "")) tryAt(pos);
      } else {
        tryAt(pos);
      }
      return out;
    }
    if (node.kind === "group") {
      if (node.nestedHouse) {
        const fused = fuseHouseIdent(houseKidsSource(node.kids));
        if (fused && s.startsWith(fused, pos))
          return [{ pos: pos + fused.length, edgeFilledOpt: false, edgeDigit: false }];
        return [];
      }
      return matchSeq(node.kids || [], pos, edgeFilledOpt, edgeDigit);
    }
    if (node.kind === "star") {
      let j = pos;
      while (s[j] === "_") j++;
      return [{ pos: j, edgeFilledOpt: false, edgeDigit: false }];
    }
    return [];
  }
  const ends = matchSeq(nodes || [], 0, false, false);
  return ends.some((e) => e.pos === s.length);
}

function houseRegexSidePads(reSource) {
  const src = expandSimplifiedHoleOpts(String(reSource || ""));
  const h = splitTopHouse(src);
  if (!h) return null;
  return [h.left, h.right].map((side) => holeRegexSeqTrailing(parseHoleRegexTree(side)).T);
}

export function consistent(token, regex, pad) {
  const boxed = regex && typeof regex === "object";
  const src0 = boxed ? String(regex.regex || regex.expr || "") : String(regex || "");
  if (!src0) return false;
  const src = expandSimplifiedHoleOpts(src0);
  const matchSrc = appendHoleRegexTrailingStar(src);
  const stored = boxed && Number.isFinite(Number(regex.pad)) ? Number(regex.pad) : null;
  const d = pad == null ? (stored != null ? stored : holeRegexTrailingPad(src0)) : Math.max(0, Number(pad) || 0);
  const norm = normalizeHouseEqTokenToRegex(String(token || "").replace(/'/g, "").replace(/\./g, "/"), src);
  const house = splitTopHouse(norm);
  const sidePads = house ? houseRegexSidePads(src0) : null;
  const sides = house ? [house.left, house.right] : null;
  const joinSoft = house ? houseDelimSlash(house.soft) : "/eq/";
  const t = sides && sidePads && sidePads.length === sides.length
    ? sides.map((side, i) => side + "_".repeat(Math.max(d, sidePads[i] || 0))).join(joinSoft)
    : sides
      ? sides.map((side) => side + "_".repeat(d)).join(joinSoft)
      : norm + "_".repeat(d);
  const tree = parseHoleRegexTree(matchSrc);
  if (tree.length) {
    try {
      return matchHoleRegexTreeToken(tree, t);
    } catch {
    }
  }
  try {
    return new RegExp("^" + matchSrc + "$").test(t);
  } catch {
    return false;
  }
}

export function maxTrailingUnderscoreFills(reSource) {
  return holeRegexTrailingPad(reSource);
}

export function normalizeHoleMatchStem(stem) {
  return String(stem || "").replace(/(\d)'(?=\d)/g, "$1");
}

export function matchImplyHoleRegex(reSource, stem) {
  const boxed = reSource && typeof reSource === "object";
  const src = boxed ? String(reSource.regex || reSource.expr || "") : String(reSource || "");
  if (!src) return false;
  const pad = boxed && Number.isFinite(Number(reSource.pad)) ? Number(reSource.pad) : holeRegexTrailingPad(src);
  return consistent(String(stem || ""), src, pad);
}

export function enumerateHoleRegexLanguage(reSource) {
  const parts = parseHoleRegexTree(reSource);
  function adjacentFillSep(leftS, rightS, leftEdgeFilled) {
    if (!leftEdgeFilled || !leftS || !rightS) return "";
    if (leftS.endsWith("_") || rightS.startsWith("_")) return "";
    const l = leftS[leftS.length - 1];
    const r = rightS[0];
    if (/\d/.test(l) && /\d/.test(r)) return "";
    return "_";
  }
  function cart(nodes) {
    let acc = [{ s: "", edgeFilledOpt: false }];
    for (const p of nodes || []) {
      const next = [];
      if (p.kind === "lit") {
        for (const a of acc) next.push({ s: a.s + p.v, edgeFilledOpt: false });
      } else if (p.kind === "hole") {
        for (const a of acc) next.push({ s: a.s + "_", edgeFilledOpt: false });
      } else if (p.kind === "opt") {
        const filled = cart(p.alts);
        for (const a of acc) {
          next.push({ s: a.s + "_", edgeFilledOpt: false });
          for (const f of filled) {
            if (!f.s) continue;
            const sep = adjacentFillSep(a.s, f.s, a.edgeFilledOpt);
            next.push({ s: a.s + sep + f.s, edgeFilledOpt: true });
          }
        }
      } else if (p.kind === "group") {
        const inner = cart(p.kids);
        for (const a of acc) {
          for (const f of inner) {
            const sep =
              a.edgeFilledOpt && f.edgeFilledOpt
                ? adjacentFillSep(a.s, f.s, true)
                : "";
            const body = p.nestedHouse ? fuseHouseIdent(f.s) : f.s;
            next.push({
              s: a.s + sep + body,
              edgeFilledOpt: f.edgeFilledOpt,
            });
          }
        }
      }
      acc = next.length ? next : acc;
      if (acc.length > 20000) break;
    }
    return acc;
  }
  try {
    return cart(parts).map((a) => a.s);
  } catch {
    return [];
  }
}

export function holeRegexLanguageTokens(reSource, opts = {}) {
  const cap = opts.cap ?? 4096;
  const raw = enumerateHoleRegexLanguage(reSource);
  const out = [];
  const seen = new Set();
  const publishStem = (stem) => {
    const rawStem = String(stem || "");
    const h = splitTopHouse(rawStem);
    if (!h) return sanitizePathSeg(rawStem);
    return sanitizePathSeg(h.left) + h.delim + nestHouseDots(sanitizePathSeg(h.right));
  };
  const dottedHouse = (stem) => {
    const h = splitTopHouse(stem);
    if (!h) return "";
    return sanitizePathSeg(h.left) + houseDelimDot(h.soft) + nestHouseDots(sanitizePathSeg(h.right));
  };
  const push = (stem) => {
    const s = publishStem(stem);
    const admit = (t) => t && !seen.has(t) && !unfilledHolePiece(t) && matchImplyHoleRegex(reSource, t);
    if (admit(s)) {
      seen.add(s);
      out.push(s);
      const dotted = dottedHouse(s);
      if (dotted && admit(dotted)) {
        seen.add(dotted);
        out.push(dotted);
      }
    }
  };
  const addApostropheVariants = (stem) => {
    push(stem);
    const positions = [];
    for (let j = 0; j < stem.length - 1; j++) {
      if (/\d/.test(stem[j]) && /\d/.test(stem[j + 1])) positions.push(j);
    }
    const n = positions.length;
    if (!n || n > 8) return;
    for (let mask = 1; mask < (1 << n); mask++) {
      const chars = stem.split("");
      let offset = 0;
      for (let b = 0; b < n; b++) {
        if (mask & (1 << b)) {
          chars.splice(positions[b] + 1 + offset, 0, "'");
          offset++;
        }
      }
      push(chars.join(""));
    }
  };
  for (const r of raw) {
    addApostropheVariants(r);
    if (out.length >= cap) break;
  }
  return out.slice(0, cap);
}

function isGetElemColonSlice(node) {
  if (cls(node) !== "LeanGetElem") return false;
  const headTok = cls(node.args?.[0]) === "LeanToken" ? (node.args[0].text || "") : "";
  const BIG = new Set(["𝔼", "ℙ", "𝕍𝕒𝕣", "∇", "max", "min", "sup", "inf", "max⁻¹", "min⁻¹"]);
  if (BIG.has(headTok)) return false;
  let idx = node.rhs ?? node.args?.[1];
  for (let i = 0; i < 8 && idx; i++) {
    const ic = cls(idx);
    if (ic === "LeanColon") return true;
    if (ic === "LeanParenthesis") { idx = idx.arg ?? idx.args?.[0]; continue; }
    if (ic === "LeanStatements" || ic === "LeanArgsNewLineSeparated") {
      idx = (idx.args || []).find((a) => cls(a) !== "LeanLineComment") || idx.args?.[0];
      continue;
    }
    idx = peelHoleExpr(idx);
    if (idx && cls(idx) === "LeanColon") return true;
    break;
  }
  return false;
}

function getElemHoleRegexFrag(node, opts) {
  if (cls(node) !== "LeanGetElem") return null;
  const headTok = cls(node.args?.[0]) === "LeanToken" ? (node.args[0].text || "") : "";
  if (headTok === "ℙ" || headTok === "∇" || headTok === "Var" || headTok === "variance") return undefined;
  if (isGetElemColonSlice(node)) return "GetSlice__";
  const idxLit = unwrapParen(node.args?.[1]);
  if (cls(idxLit) === "LeanToken" && /^-?\d+$/.test(idxLit.text || "")) return "Get_(" + idxLit.text + ")";
  if (isBinderGetAtLiteral(node, opts)) return null;
  if (isGetIndexNoise(node.args?.[1], opts)) {
    const headFrag = holeRegexExpr(node.args?.[0], opts);
    return (headFrag == null || headFrag === "" || headFrag === "_") ? null : headFrag;
  }
  const idxFrag = holeRegexExpr(node.args?.[1], opts);
  if (idxFrag == null || idxFrag === "" || idxFrag === "_") {
    const headFrag = holeRegexExpr(node.args?.[0], opts);
    return (headFrag == null || headFrag === "" || headFrag === "_") ? null : headFrag;
  }
  return "Get_" + wrapHoleOpt(idxFrag);
}

function isGluedQuantEqRegex(re) {
  const s = String(re || "");
  return /^(?:Any|All)_\((?:_\|)?(?:Any|All)_[A-Za-z0-9_]*Eq[A-Za-z0-9_]*\)$/.test(s)
    || /^(?:Any|All)_[A-Za-z0-9_]*Eq[A-Za-z0-9_]*$/.test(s);
}

function peelQuantBody(node) {
  let n = node;
  for (let i = 0; i < 12 && n; i++) {
    const c = cls(n);
    if (c === "LeanParenthesis" || c === "LeanColon") { n = n.args?.[0]; continue; }
    if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") { n = firstConclusion(n); continue; }
    break;
  }
  return n;
}

function isQuantEqHoleNode(node, opts) {
  const u = peelHoleExpr(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") return isLeafName(u.text, opts?.leaves);
  if (c === "LeanArgsSpaceSeparated") return (u.args || []).every((a) => isQuantEqHoleNode(a, opts));
  if (c === "LeanInv" || c === "LeanNeg") return isQuantEqHoleNode(u.args?.[0], opts);
  return false;
}

function binaryHoleDeriv(re) {
  return String(re || "").replace(/Deriv_(?![\(_])/g, "Deriv__");
}

function quantEqPartialToken(node) {
  const ps = partialBoundScope(node);
  const b = ps ? peelHoleExpr(ps.bound) : null;
  const n = b && cls(b) === "LeanArgsCommaSeparated" ? Math.max(1, (b.args || []).length) : 1;
  return n >= 2 ? node.pathToken + "__" : node.pathToken;
}

function decompQuantEqExpr(node, opts) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  const c = cls(u);
  const opt = (frag) => wrapHoleOpt(frag);
  if (c === "Lean_partial" || c === "LeanPartial") {
    const ps = partialBoundScope(u);
    if (!ps || isQuantEqHoleNode(ps.scope, opts)) return quantEqPartialToken(u);
    const inner = decompQuantEqExpr(ps.scope, opts);
    return inner ? u.pathToken + "_" + opt(inner) : null;
  }
  if (c === "Lean_sqrt") {
    const arg = u.arg ?? u.args?.[0];
    if (isQuantEqHoleNode(arg, opts)) return u.pathToken;
    const inner = decompQuantEqExpr(arg, opts);
    return inner ? u.pathToken + opt(inner) : null;
  }
  if (c === "LeanInv" || c === "LeanNeg") {
    const tag = u.pathToken;
    const arg = u.arg ?? u.args?.[0];
    if (isQuantEqHoleNode(arg, opts)) return tag;
    const inner = decompQuantEqExpr(arg, opts);
    return inner ? tag + opt(inner) : null;
  }
  if (c === "LeanAdd" || c === "LeanSub" || c === "LeanMul" || c === "LeanDiv") {
    const tag = CLASS_TOKEN[c];
    let s = tag;
    for (const a of u.args || []) {
      if (isQuantEqHoleNode(a, opts)) { s += "_"; continue; }
      const p = decompQuantEqExpr(a, opts);
      if (!p) return null;
      s += opt(p);
    }
    return s;
  }
  if (c === "LeanToken") {
    const raw = u.text || "";
    if (isLeafName(raw, opts?.leaves)) return null;
    if (/^-?\d+$/.test(raw)) return raw;
    return nameToken(raw) || null;
  }
  if (c === "LeanEq") {
    const L = decompQuantEqExpr(u.lhs ?? u.args?.[0], opts);
    const R = decompQuantEqExpr(u.rhs ?? u.args?.[1], opts);
    if (!L || !R) return null;
    return "Eq" + opt(L) + opt(R);
  }
  if (c === "Lean_otimes" || c === "Lean_otimesSub") {
    const args = u.args || [];
    if (!args.length) return "Otimes__";
    let s = "Otimes";
    let holes = 0;
    for (const a of args) {
      if (isQuantEqHoleNode(a, opts)) { holes++; s += "_"; continue; }
      const p = decompQuantEqExpr(a, opts);
      if (!p) return null;
      s += opt(p);
    }
    return holes === args.length ? "Otimes" + "_".repeat(args.length) : s;
  }
  if (c === "LeanArgsSpaceSeparated") {
    const args = u.args || [];
    const head = peelHoleExpr(args[0]);
    const headHole = cls(head) === "LeanToken" && (
      isQuantEqHoleNode(head, opts) || isLeafName(head.text, opts?.quantLeaves)
    );
    if (!headHole || args.length < 2) return null;
    const frags = [];
    for (const a of args.slice(1)) {
      if (isQuantEqHoleNode(a, opts)) continue;
      const p = decompQuantEqExpr(a, opts);
      if (!p) return null;
      frags.push(p);
    }
    if (!frags.length) return null;
    return frags.map((p) => opt(p)).join("");
  }
  return null;
}

function decompQuantHoleRegex(node, opts) {
  const u = peelHoleExpr(node);
  const c = cls(u);
  if (c !== "Lean_forall" && c !== "Lean_exists") return null;
  const tag = u.pathToken;
  let body = u.scope ?? u.args?.[u.args.length - 1];
  if (c === "Lean_forall") body = peelGuardForalls(body);
  body = peelQuantBody(body);
  const bc = cls(body);
  if (bc === "Lean_forall" || bc === "Lean_exists") {
    const inner = decompQuantHoleRegex(body, opts);
    if (!inner) return null;
    return tag + "_" + wrapHoleOpt(inner);
  }
  if (bc === "LeanEq") {
    const eq = decompQuantEqExpr(body, opts);
    if (!eq || !eq.startsWith("Eq")) return null;
    return tag + "_" + wrapHoleOpt(eq);
  }
  return null;
}

function updateColParts(node) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return null;
  const head = u.args?.[0];
  if (cls(head) !== "LeanProperty") return null;
  const prop = head.args?.[1];
  if (cls(prop) !== "LeanToken" || prop.text !== "updateCol") return null;
  return { matrix: head.args?.[0], index: u.args?.[1], col: u.args?.[2] };
}

function implyBinderSet(opts) {
  return new Set(opts?.leaves || []);
}

function noteQuantBinders(node, binders) {
  const head = node?.args?.[0];
  const c = cls(head);
  if (c === "LeanToken" && head.text) binders.add(head.text);
  if (c === "LeanColon" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text)
    binders.add(head.args[0].text);
  if ((c === "Lean_gt" || c === "Lean_lt" || c === "Lean_ge" || c === "Lean_le")
      && cls(head.args?.[0]) === "LeanToken" && head.args[0].text)
    binders.add(head.args[0].text);
}

function isImplyHole(node, opts, binders) {
  const u = peelHoleExpr(node);
  if (!u) return true;
  const c = cls(u);
  if (c === "LeanToken") {
    const t = u.text || "";
    if (!t || t === "_") return true;
    if (/^-?\d+$/.test(t)) return !opts?.digitLiteral;
    return binders.has(t) || isLeafName(t, binders) || isLeafName(t, opts?.leaves);
  }
  if (c === "LeanArgsSpaceSeparated") {
    if (updateColParts(u)) return false;
    return (u.args || []).every((a) => isImplyHole(a, opts, binders));
  }
  if (c === "LeanMul" && (u.subscript === "ᵥ" || String(u.operator || "").startsWith("ᵥ"))) return false;
  if ((c === "LeanConj" || c === "LeanAdjoint" || c === "LeanTranspose" || c === "LeanInv")
      && opts?.quantNames) {
    const inner = peelHoleExpr(u.arg ?? u.args?.[0]);
    if (cls(inner) === "LeanToken" && opts.quantNames.has(inner.text || "")) return true;
  }
  if (c === "LeanMatMul" || c === "Lean_bullet") return false;
  if (c === "LeanAdd" || c === "LeanSub" || c === "LeanMul" || c === "LeanDiv"
      || c === "Lean_lt" || c === "Lean_gt" || c === "Lean_le" || c === "Lean_ge") {
    const args = u.args || [];
    return args.length > 0 && args.every((a) => isImplyHole(a, opts, binders));
  }
  return false;
}

function peelQuantRelGuard(node, quantNames) {
  let n = peelHoleExpr(node);
  const names = quantNames || new Set();
  while (n && (cls(n) === "Lean_rightarrow" || cls(n) === "LeanRightarrow")) {
    const ant = peelHoleExpr(n.args?.[0]);
    const rel = cls(ant);
    if (!["Lean_ne", "LeanNe", "Lean_lt", "Lean_gt", "Lean_le", "Lean_ge", "LeanEq"].includes(rel)) break;
    const sides = ant.args || [];
    const quantSide = (s) => {
      const u = peelHoleExpr(s);
      if (cls(u) === "LeanConj" || cls(u) === "LeanAdjoint" || cls(u) === "LeanInv" || cls(u) === "LeanTranspose") {
        const inner = peelHoleExpr(u.arg ?? u.args?.[0]);
        return cls(inner) === "LeanToken" && names.has(inner.text || "");
      }
      return cls(u) === "LeanToken" && names.has(u.text || "");
    };
    const digitSide = (s) => {
      const u = peelHoleExpr(s);
      return cls(u) === "LeanToken" && /^-?\d+$/.test(u.text || "");
    };
    if (!((quantSide(sides[0]) && digitSide(sides[1])) || (quantSide(sides[1]) && digitSide(sides[0])))) break;
    n = peelHoleExpr(n.args?.[1]);
  }
  return n;
}

function isFreeMatrixAtom(node, opts) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "LeanToken") return false;
  const t = u.text || "";
  if (!t || t === "_" || /^-?\d+$/.test(t)) return false;
  return !(opts?.quantNames?.has(t));
}

function decompImplyStruct(node, opts, binders) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  if (!binders) binders = implyBinderSet(opts);
  if (!opts.quantNames) opts.quantNames = new Set();
  opts.isHole = opts.isHole || isImplyHole;
  opts.noteQuantBinders = opts.noteQuantBinders || noteQuantBinders;
  opts.peelGuardForalls = opts.peelGuardForalls || peelGuardForalls;
  opts.peelQuantRelGuard = opts.peelQuantRelGuard || peelQuantRelGuard;
  opts.isFreeMatrixAtom = opts.isFreeMatrixAtom || isFreeMatrixAtom;
  opts.updateColParts = opts.updateColParts || updateColParts;
  opts.peel = opts.peel || peelHoleExpr;
  opts.decomp = (n, b = binders) => decompImplyStruct(n, opts, b);

  const c = cls(u);

  if (c === "LeanVecNotation") return null;

  if (c === "Lean_approx") {
    const L = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
    const R = decompImplyStruct(u.rhs ?? u.args?.[1], opts, binders);
    if (!L && !R) return "XEq";
    if (!L) return R ? "XEq_" + storedHoleOpt(R) : "XEq_";
    if (!R) return "XEq" + storedHoleOpt(L) + "_";
    return "XEq" + storedHoleOpt(L) + storedHoleOpt(R);
  }

  if (c === "LeanAppend") {
    const L = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
    const R = decompImplyStruct(u.rhs ?? u.args?.[1], opts, binders);
    if (!L && !R) return "Append__";
    if (!L) return R ? "Append_" + storedHoleOpt(R) : "Append_";
    if (!R) return "Append" + storedHoleOpt(L) + "_";
    return "Append" + storedHoleOpt(L) + storedHoleOpt(R);
  }

  if (c === "LeanGetElem") {
    let idx = u.rhs ?? u.args?.[1];
    for (let i = 0; i < 8 && idx; i++) {
      const ic = cls(idx);
      if (ic === "LeanColon") return "GetSlice__";
      if (ic === "LeanParenthesis") { idx = idx.arg ?? idx.args?.[0]; continue; }
      if (ic === "LeanStatements" || ic === "LeanArgsNewLineSeparated") {
        idx = (idx.args || []).find((a) => cls(a) !== "LeanLineComment") || idx.args?.[0];
        continue;
      }
      idx = peelHoleExpr(idx);
      if (idx && cls(idx) === "LeanColon") return "GetSlice__";
      break;
    }
    return "Get__";
  }

  if (c === "LeanTranspose") {
    const inner = decompImplyStruct(u.arg ?? u.args?.[0], opts, binders);
    return inner ? "T" + storedHoleOpt(inner) : "T_";
  }

  if (c === "LeanMatMul") {
    const L = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
    const R = decompImplyStruct(u.rhs ?? u.args?.[1], opts, binders);
    if (!L && !R) return "Dot__";
    if (!L) return R ? "Dot_" + storedHoleOpt(R) : "Dot_";
    if (!R) return "Dot" + storedHoleOpt(L) + "_";
    return "Dot" + storedHoleOpt(L) + storedHoleOpt(R);
  }

  if (typeof u.storedHoleRegex === "function") {
    const native = u.storedHoleRegex(opts, binders);
    if (native) return native;
  }

  if (c === "LeanProperty") {
    const prop = u.rhs ?? u.args?.[1];
    const raw = cls(prop) === "LeanToken" ? (prop.text || "") : "";
    const propTok = raw ? nameToken(raw) : "";
    if (/^softmax$/i.test(raw) || propTok === "Softmax") {
      const inner = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
      return inner ? "Softmax" + storedHoleOpt(inner) : "Softmax_";
    }
    if (raw === "sqrt" || propTok === "Sqrt") {
      const arg = u.lhs ?? u.args?.[0];
      if (opts.isHole(arg, opts, binders)) return "Sqrt_";
      const inner = decompImplyStruct(arg, opts, binders);
      return inner ? "Sqrt" + storedHoleOpt(inner) : "Sqrt_";
    }
    if (/^card$/i.test(raw) || propTok === "Card") {
      const inner = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
      return inner ? "Card" + storedHoleOpt(inner) : "Card_";
    }
  }

  if (c === "Lean_sqrt") {
    const arg = u.arg ?? u.args?.[0];
    if (opts.isHole(arg, opts, binders)) return "Sqrt_";
    const inner = decompImplyStruct(arg, opts, binders);
    return inner ? "Sqrt" + storedHoleOpt(inner) : "Sqrt_";
  }

  if (c === "LeanAbs") {
    const inner = decompImplyStruct(u.arg ?? u.args?.[0], opts, binders);
    return inner ? u.pathToken + storedHoleOpt(inner) : u.pathToken + "_";
  }

  if (c === "Lean_sum" || c === "Lean_prod") {
    const tag = u.pathToken;
    const parts = u.args || [];
    const body = decompImplyStruct(parts[parts.length - 1], opts, binders);
    const domain = parts.length > 1 ? decompImplyStruct(parts[0], opts, binders) : null;
    if (!body) return domain ? tag + storedHoleOpt(domain) + "_" : tag + "__";
    return tag + (domain ? storedHoleOpt(domain) : "_") + storedHoleOpt(body);
  }

  if (typeof u.holeRegexAltTag === "string") {
    const fill = holeRegexAltFill(u, {
      ...opts,
      nameToken,
      isLeaf: (t) => isLeafName(t, opts.leaves),
    });
    if (fill) return fill;
  }

  if (c === "LeanMul" || c === "LeanDiv" || c === "LeanAdd" || c === "LeanSub" || c === "Lean_lt" || c === "Lean_gt" || c === "Lean_le" || c === "Lean_ge") {
    const tag = u.pathToken;
    const L = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
    const R = decompImplyStruct(u.rhs ?? u.args?.[1], opts, binders);
    const lHole = !L;
    const rHole = !R;
    if (lHole && rHole) return tag === "Mul" ? "Mul__" : tag;
    if (lHole) return tag + "_" + storedHoleOpt(R);
    if (rHole) return tag + storedHoleOpt(L) + "_";
    return tag + storedHoleOpt(L) + storedHoleOpt(R);
  }

  {
    const sps = singlePSpaceHoleRegex(u, opts);
    if (sps) return sps;
  }

  if (c === "LeanPreimage") {
    const L = decompImplyStruct(u.lhs ?? u.args?.[0], opts, binders);
    const R = decompImplyStruct(u.rhs ?? u.args?.[1], opts, binders);
    if (!L && !R) return "Preimage__";
    if (!L) return R ? "Preimage_" + storedHoleOpt(R) : "Preimage_";
    if (!R) return "Preimage" + storedHoleOpt(L) + "_";
    return "Preimage" + storedHoleOpt(L) + storedHoleOpt(R);
  }

  if (opts.isHole(u, opts, binders)) return null;
  return null;
}

const ITE_BINARY = {
  Lean_lt: "Lt", Lean_gt: "Gt", Lean_le: "Le", Lean_ge: "Ge",
  LeanEq: "Eq", Lean_ne: "Ne", LeanNe: "Ne",
  LeanDiv: "Div", LeanMul: "Mul", LeanAdd: "Add", LeanSub: "Sub", LeanPow: "Pow",
  Lean_land: "And", Lean_lor: "Or", Lean_leftrightarrow: "Iff",
  Lean_cdotp: "Dot", LeanMatMul: "Dot",
};
const ITE_UNARY = {
  LeanNeg: "Neg", LeanInv: "Inv", Lean_lnot: "Not", Lean_sqrt: "Sqrt",
  LeanNorm: "Norm", LeanAbs: "Abs", LeanConj: "Conj",
};

function containsIte(node) {
  const u = peelHoleExpr(node);
  if (!u) return false;
  if (cls(u) === "LeanIte") return true;
  return (u.args || []).some((a) => containsIte(a));
}

function isIteOperandHole(node) {
  const u = peelHoleExpr(node);
  if (!u) return true;
  if (cls(u) === "LeanIte") return false;
  return !containsIte(u);
}

function isSqrtProp(node) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "LeanProperty") return false;
  const rhs = u.rhs ?? u.args?.[1];
  return cls(rhs) === "LeanToken" && (rhs.text || "") === "sqrt";
}

function iteBranchToken(node, opts) {
  const u = peelHoleExpr(node);
  if (!u) return "_";
  if (cls(u) === "LeanIte") return iteHoleRegex(u, opts);
  if (cls(u) === "LeanToken" && /^-?\d+$/.test(u.text || "")) return u.text;
  if (isSqrtProp(u)) {
    const arg = u.lhs ?? u.args?.[0];
    return "Sqrt" + (isIteOperandHole(arg, opts) ? "_" : "(" + iteBranchToken(arg, opts) + ")");
  }
  const bin = ITE_BINARY[cls(u)];
  if (bin) {
    const a = u.args || [];
    const L = isIteOperandHole(a[0], opts) ? "_" : "(" + iteBranchToken(a[0], opts) + ")";
    const R = isIteOperandHole(a[1], opts) ? "_" : "(" + iteBranchToken(a[1], opts) + ")";
    return bin + L + R;
  }
  const un = ITE_UNARY[cls(u)];
  if (un) {
    const arg = u.arg ?? u.args?.[0];
    return un + (isIteOperandHole(arg, opts) ? "_" : "(" + iteBranchToken(arg, opts) + ")");
  }
  return "_";
}

function simplifyIteHoleRegex(raw) {
  const s = String(raw || "");
  if (!s.includes("Ite(") || !s.includes("(_|")) return raw;
  const simplified = s.replace(/\(_\|/g, "(");
  if (simplified.includes("(_|")) return raw;
  if (!/^(?:(?:Any|All)_|IsIrreducible|Lt|Eq)\(/.test(simplified)) return raw;
  return simplified;
}

function simplifyQuantRelDigit(raw) {
  let s = String(raw || "").replace(/\(_\|/g, "(");
  if (/^(?:Any|All)_\((?:Lt|Gt|Le|Ge)\(-?\d+\)$/.test(s)) s = s.slice(0, -1) + "_)";
  if (!/^(?:Any|All)_\((?:Lt|Gt|Le|Ge)\(-?\d+\)_\)$/.test(s)) return raw;
  return s;
}

function quantRelDigitMirror(stored) {
  const m = /^(Any|All)_\((Lt|Gt|Le|Ge)\((-?\d+)\)_\)$/.exec(String(stored || ""));
  if (!m) return "";
  const mirror = { Lt: "Gt", Gt: "Lt", Le: "Ge", Ge: "Le" }[m[2]];
  return mirror ? m[1] + "_(" + mirror + "_(" + m[3] + "))" : "";
}

function iteHoleRegex(node, opts) {
  const args = node.args || [];
  let cond, th, el;
  if (cls(args[0]) === "LeanColon") {
    cond = args[0].args?.[1];
    th = args[1];
    el = args[2];
  } else {
    cond = args[0];
    th = args[1];
    el = args[2];
  }
  const grp = (arm, role) => {
    const frag = iteBranchToken(arm, opts);
    if (role === "else" && /^-?\d+$/.test(frag)) return frag;
    return "(" + frag + ")";
  };
  return "Ite" + grp(cond, "cond") + grp(th, "then") + grp(el, "else");
}

function flattenStackedExpect(re) {
  if (re == null || re === "") return re;
  let s = String(re);
  for (let guard = 0; guard < 8; guard++) {
    const next = flattenStackedExpectOnce(s);
    if (next === s) return s;
    s = next;
  }
  return s;
}

function flattenStackedExpectOnce(s) {
  const open = "Expect_(";
  let i = 0;
  while (i < s.length) {
    const at = s.indexOf(open, i);
    if (at < 0) return s;
    const inner = at + open.length;
    if (!s.startsWith("Expect", inner)) { i = at + 1; continue; }
    let end = -1;
    if (s.startsWith("Expect__", inner) && s[inner + "Expect__".length] !== "(")
      end = inner + "Expect__".length;
    else if (s.startsWith("Expect_(", inner)) {
      const close = holeRegexMatchingParen(s, inner + "Expect_".length);
      if (close >= 0) end = close + 1;
    }
    if (end < 0 || s[end] !== ")") { i = at + 1; continue; }
    return s.slice(0, at) + s.slice(inner, end) + s.slice(end + 1);
  }
  return s;
}

function flattenStackedAll(re) {
  if (re == null || re === "") return re;
  let s = String(re);
  for (let guard = 0; guard < 8; guard++) {
    const next = flattenStackedAllOnce(s);
    if (next === s) return s;
    s = next;
  }
  return s;
}

function flattenStackedAllOnce(s) {
  let i = 0;
  while (i < s.length) {
    const a = s.indexOf("All_(", i);
    const b = s.indexOf("All_(_|", i);
    let at = -1;
    let innerOff = 0;
    if (a >= 0 && (b < 0 || a <= b)) { at = a; innerOff = "All_(".length; }
    else if (b >= 0) { at = b; innerOff = "All_(_|".length; }
    if (at < 0) return s;
    const inner = at + innerOff;
    if (!s.startsWith("All", inner)) { i = at + 1; continue; }
    const openParen = s.indexOf("(", at);
    const close = holeRegexMatchingParen(s, openParen);
    if (close < 0) { i = at + 1; continue; }
    const innerFrag = s.slice(inner, close);
    if (!innerFrag.startsWith("All")) { i = at + 1; continue; }
    return s.slice(0, at) + innerFrag + s.slice(close + 1);
  }
  return s;
}

function isProbHoleFrag(s) {
  const t = String(s || "");
  return t === "Prob__" || t === "Prob_(Cond__)" || t === "Prob" || t.startsWith("Prob_");
}

function isEqOfProbQuantTree(n) {
  let cur = peelHoleExpr(n);
  for (let i = 0; i < 8; i++) {
    if (cls(cur) !== "Lean_forall" && cls(cur) !== "Lean_exists") break;
    let body = cur.scope ?? cur.args?.[cur.args.length - 1];
    if (cls(cur) === "Lean_forall") body = peelGuardForalls(body);
    cur = peelHoleExpr(peelQuantBody(body));
  }
  if (cls(cur) !== "LeanEq") return false;
  const L = peelHoleExpr(cur.lhs ?? cur.args?.[0]);
  const R = peelHoleExpr(cur.rhs ?? cur.args?.[1]);
  return cls(L) === "Lean_Prob" && cls(R) === "Lean_Prob";
}

function isSimpleGetObservation(node) {
  const u = peelHoleExpr(node);
  if (!u) return false;
  const c = cls(u);
  if (c === "LeanGetElem") {
    let idx = u.rhs ?? u.args?.[1];
    for (let i = 0; i < 8 && idx; i++) {
      const ic = cls(idx);
      if (ic === "LeanColon") return false;
      if (ic === "LeanParenthesis") { idx = idx.arg ?? idx.args?.[0]; continue; }
      if (ic === "LeanStatements" || ic === "LeanArgsNewLineSeparated") {
        idx = (idx.args || []).find((a) => cls(a) !== "LeanLineComment") || idx.args?.[0];
        continue;
      }
      idx = peelHoleExpr(idx);
      if (idx && cls(idx) === "LeanColon") return false;
      break;
    }
    return true;
  }
  if (c === "LeanEq") {
    const a = peelHoleExpr(u.lhs ?? u.args?.[0]);
    const b = peelHoleExpr(u.rhs ?? u.args?.[1]);
    return isSimpleGetObservation(a) || isSimpleGetObservation(b);
  }
  return false;
}

function isJointOfTwoGetObservations(node) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "Lean_land") return false;
  const L = unwrapParen(u.lhs ?? u.args?.[0]);
  const R = unwrapParen(u.rhs ?? u.args?.[1]);
  return isSimpleGetObservation(L) && isSimpleGetObservation(R);
}

function matchProbCommaCondScope(sc0) {
  const sc = peelHoleExpr(sc0);
  if (cls(sc) === "LeanArgsCommaSeparated") {
    const args = (sc.args || []).map((a) => unwrapParen(a));
    if (args.length >= 2 && cls(args[0]) === "LeanBitOr") {
      const bit = args[0];
      return {
        event: unwrapParen(bit.lhs ?? bit.args?.[0]),
        conds: [unwrapParen(bit.rhs ?? bit.args?.[1]), ...args.slice(1)],
      };
    }
  }
  if (cls(sc) === "LeanBitOr") {
    const R = unwrapParen(sc.rhs ?? sc.args?.[1]);
    if (cls(R) === "LeanArgsCommaSeparated" && (R.args || []).length >= 1) {
      return {
        event: unwrapParen(sc.lhs ?? sc.args?.[0]),
        conds: (R.args || []).map((a) => unwrapParen(a)),
      };
    }
  }
  return null;
}

function isCommaCondProbFrag(s) {
  const t = String(s || "");
  if (t.startsWith("Prob_(Cond(") && t.includes("Joint(")) return true;
  return t === "(Cond/eq/Prod)_Prob" || t === "(Cond.eq.Prod)_Prob";
}

function isCondProbProductBody(s) {
  const t = String(s || "");
  if (t.startsWith("Prob_(Cond")) return true;
  return isCommaCondProbFrag(t);
}

function isProbFamilyFrag(s) {
  const t = String(s || "");
  return isProbHoleFrag(t) || isProbProductFrag(t) || t.startsWith("Prod_") || isCommaCondProbFrag(t);
}

function getRvCondHoleFrag(node) {
  const u = peelHoleExpr(node);
  if (!u) return "";
  if (isGetElemColonSlice(u)) return "GetSlice__";
  if (isSimpleGetObservation(u) || cls(u) === "LeanGetElem") return "Get__";
  return "";
}

function rvCondHoleFrag(node) {
  const u = peelHoleExpr(node);
  const base = getRvCondHoleFrag(u);
  if (base) return base;
  if (isJointOfTwoGetObservations(u)) {
    return jointHoleFrag([
      getRvCondHoleFrag(u.lhs ?? u.args?.[0]),
      getRvCondHoleFrag(u.rhs ?? u.args?.[1]),
    ]);
  }
  return "";
}

function jointHoleFrag(frags) {
  const xs = (frags || []).map((f) => (f && f !== "_") ? f : "");
  if (!xs.length) return "";
  let acc = xs[0];
  for (let i = 1; i < xs.length; i++) {
    const L = acc || "";
    const R = xs[i] || "";
    if (!L && !R) acc = "Joint__";
    else if (!L) acc = "Joint_" + storedHoleOpt(R);
    else if (!R) acc = "Joint" + storedHoleOpt(L) + "_";
    else acc = "Joint" + storedHoleOpt(L) + storedHoleOpt(R);
  }
  return acc;
}

function commaCondProbHoleRegex(node) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "Lean_Prob") return null;
  const hit = matchProbCommaCondScope(u.scope);
  if (!hit) return null;
  return condProbHoleRegexFromFrags(
    getRvCondHoleFrag(hit.event),
    jointHoleFrag((hit.conds || []).map(getRvCondHoleFrag)),
  );
}

function condProbHoleRegexFromFrags(ev, cd) {
  const evS = (ev && ev !== "_") ? ev : "";
  const cdS = (cd && cd !== "_") ? cd : "";
  let cond;
  if (!evS && !cdS) cond = "Cond__";
  else if (!evS) cond = "Cond_" + storedHoleOpt(cdS);
  else if (!cdS) cond = "Cond" + storedHoleOpt(evS) + "_";
  else cond = "Cond" + storedHoleOpt(evS) + storedHoleOpt(cdS);
  return "Prob_(" + cond + ")";
}

function probSideHoleFrag(node, opts) {
  const u = peelHoleExpr(node);
  if (cls(u) === "LeanGetElem") {
    const frag = getElemHoleRegexFrag(u, opts);
    return frag || "Get__";
  }
  return rvCondHoleFrag(u);
}

function probCondGetHoleRegex(node, opts) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "Lean_Prob") return null;
  const comma = commaCondProbHoleRegex(u);
  if (comma) return comma;
  const sc = peelHoleExpr(u.scope);
  if (cls(sc) !== "LeanBitOr" || cls(unwrapParen(sc.args?.[0])) === "Lean_perp") return null;
  const L = unwrapParen(sc.lhs ?? sc.args?.[0]);
  const R = unwrapParen(sc.rhs ?? sc.args?.[1]);
  if (isSimpleGetObservation(L) && isSimpleGetObservation(R))
    return condProbHoleRegexFromFrags(probSideHoleFrag(L, opts), probSideHoleFrag(R, opts));
  return condProbHoleRegexFromFrags(rvCondHoleFrag(L), rvCondHoleFrag(R));
}

function isProbProductFrag(s) {
  const t = String(s || "");
  return t.startsWith("Mul(") && t.includes("Prob");
}

function parenGroupEnd(s, i) {
  const close = s[i] === "(" ? holeRegexMatchingParen(s, i) : -1;
  return close < 0 ? -1 : close + 1;
}

function pluralSHead(atom) {
  const m = /^([A-Z][A-Za-z0-9]*)([\s\S]*)$/.exec(atom);
  return m ? m[1] + "S" + m[2] : null;
}

const NON_PLURAL_REPEAT_HEADS = new Set(["Joint"]);

function rewriteRepeatedApp(s) {
  for (let i = 0; i < s.length; i++) {
    if (!/[A-Z]/.test(s[i]) || (i > 0 && /[A-Za-z0-9_]/.test(s[i - 1]))) continue;
    let j = i;
    while (j < s.length && /[A-Za-z0-9]/.test(s[j])) j++;
    const op = s.slice(i, j);
    if (NON_PLURAL_REPEAT_HEADS.has(op)) continue;
    const end1 = parenGroupEnd(s, j);
    if (end1 < 0) continue;
    const end2 = parenGroupEnd(s, end1);
    if (end2 < 0) continue;
    const x = s.slice(j + 1, end1 - 1);
    if (x !== s.slice(end1 + 1, end2 - 1)) continue;
    const plural = pluralSHead(x);
    if (plural) return { repl: s.slice(0, i) + s.slice(i, j) + plural + s.slice(end2), op, x, xPluralized: plural, end: end2, start: i };
  }
  return null;
}

function pluralizeRepeatedApps(s) {
  let cur = String(s || "");
  for (;;) {
    const hit = rewriteRepeatedApp(cur);
    if (!hit) return cur;
    cur = hit.repl;
  }
}

function pluralRepeatedHoleAlts(reSource) {
  const s = String(reSource || "");
  const out = [];
  const seen = new Set();
  const push = (v) => {
    if (!v || v === s || seen.has(v)) return;
    seen.add(v);
    out.push(v);
  };
  for (let from = 0; from < s.length;) {
    const hit = rewriteRepeatedApp(s.slice(from));
    if (!hit) break;
    const at = from + hit.start;
    const xPluralized = pluralizeRepeatedApps(hit.x);
    const headInner = pluralSHead(xPluralized);
    const headOuter = pluralSHead(hit.x);
    const suffix = s.slice(at + (hit.end - hit.start));
    if (headInner) push(s.slice(0, at) + hit.op + headInner + suffix);
    if (headOuter) push(s.slice(0, at) + hit.op + headOuter + suffix);
    if (xPluralized !== hit.x) push(s.slice(0, at) + hit.op + "(" + xPluralized + ")(" + xPluralized + ")" + suffix);
    from = at + (hit.end - hit.start);
  }
  return out;
}

function integralMeasurePartial(node) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "Lean_int") return null;
  if (typeof u.measurePartial === "function") return u.measurePartial() || null;
  return null;
}

function isIntegralArgList(n) {
  const c = cls(n);
  return c === "LeanArgsSpaceSeparated" || c === "LeanArgsNewLineSeparated"
    || c === "LeanArgsCommaNewLineSeparated" || c === "LeanArgsIndented";
}

function integrandContainsNode(n, meas, d = 0) {
  if (!n || !meas || d > 24) return false;
  if (n === meas) return true;
  if ((n.args || []).some((a) => integrandContainsNode(a, meas, d + 1))) return true;
  if (n.lhs && integrandContainsNode(n.lhs, meas, d + 1)) return true;
  if (n.rhs && integrandContainsNode(n.rhs, meas, d + 1)) return true;
  if (n.scope && integrandContainsNode(n.scope, meas, d + 1)) return true;
  if (n.arg && integrandContainsNode(n.arg, meas, d + 1)) return true;
  if (n.bound && integrandContainsNode(n.bound, meas, d + 1)) return true;
  return false;
}

function integrandHoleRegex(node, opts, measure) {
  if (!node || node === measure) return null;
  const u = peelHoleExpr(node);
  if (!u || u === measure) return null;
  if (isIntegralArgList(u)) {
    if (cls(u) === "LeanArgsIndented") {
      const L = integrandHoleRegex(u.lhs, opts, measure);
      const R = integrandHoleRegex(u.rhs, opts, measure);
      return (L && L !== "_") ? L : ((R && R !== "_") ? R : null);
    }
    const args = (u.args || []).filter((a) => a !== measure && cls(a) !== "LeanCaret");
    const named = [];
    for (const a of args) {
      const f = integrandHoleRegex(a, opts, measure);
      if (f && f !== "_") named.push(f);
    }
    if (!named.length) return null;
    return named.length === 1 ? named[0] : named[0];
  }
  if (cls(u) === "Lean_bullet") {
    const L = integrandHoleRegex(u.lhs ?? u.args?.[0], opts, measure);
    const R = integrandHoleRegex(u.rhs ?? u.args?.[1], opts, measure);
    const lFrag = (L && L !== "_") ? L : "";
    const rFrag = (R && R !== "_") ? R : "";
    if (!lFrag && !rFrag) return "SMul__";
    if (!lFrag) return "SMul_" + storedHoleOpt(rFrag);
    if (!rFrag) return "SMul" + storedHoleOpt(lFrag) + "_";
    return "SMul" + storedHoleOpt(lFrag) + storedHoleOpt(rFrag);
  }
  if (measure && integrandContainsNode(u, measure)) {
    const tag = u.pathToken || CLASS_TOKEN[cls(u)];
    if (tag && tag !== "Integral") {
      const L = integrandHoleRegex(u.lhs ?? u.args?.[0], opts, measure);
      const R = integrandHoleRegex(u.rhs ?? u.args?.[1] ?? u.scope, opts, measure);
      const lFrag = (L && L !== "_") ? L : "";
      const rFrag = (R && R !== "_") ? R : "";
      if (!lFrag && !rFrag) return tag + "__";
      if (!lFrag) return tag + "_" + storedHoleOpt(rFrag);
      if (!rFrag) return tag + storedHoleOpt(lFrag) + "_";
      return tag + storedHoleOpt(lFrag) + storedHoleOpt(rFrag);
    }
  }
  return holeRegexExpr(u, opts);
}

function integralHoleRegex(node, opts) {
  let u = peelHoleExpr(node);
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "Lean_int")
    u = u.args[0];
  if (cls(u) !== "Lean_int") return null;
  const measure = integralMeasurePartial(u);
  const body = u.scope ?? u.args?.[u.args.length - 1];
  const inner = integrandHoleRegex(body, opts, measure);
  if (!inner || inner === "_") return "Integral__";
  if (inner === "Integral" || inner.startsWith("Integral_")) return inner;
  return "Integral_" + storedHoleOpt(inner);
}

const MEASURABLE_RV_HEADS = new Set([
  "Measurable",
  "AEMeasurable",
  "StronglyMeasurable",
  "AEStronglyMeasurable",
]);

function measurableGetHoleRegex(node, opts) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return null;
  const args = u.args || [];
  if (args.length < 2) return null;
  const head = unwrapParen(args[0]);
  if (cls(head) !== "LeanToken") return null;
  const headName = nameToken(head.text || "");
  if (!MEASURABLE_RV_HEADS.has(headName)) return null;
  const rv = unwrapParen(args[1]);
  if (cls(rv) !== "LeanGetElem") return null;
  if (isGetElemColonSlice(rv)) return null;
  let out = headName + "(Get__)";
  for (let i = 2; i < args.length; i++) {
    const a = args[i];
    if (isImplyHole(a, opts, implyBinderSet(opts))) {
      out += "_";
      continue;
    }
    const f = holeRegexExpr(a, opts);
    out += (f && f !== "_") ? "_(" + f + ")" : "_";
  }
  return out;
}

function singlePSpaceHoleRegex(node, opts) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return null;
  const args = u.args || [];
  if (args.length < 2) return null;
  const head = unwrapParen(args[0]);
  if (cls(head) !== "LeanToken" || head.text !== "SinglePSpace") return null;
  const argFrag = rvOperandHoleFrag(args[args.length - 1], opts);
  if (!argFrag || argFrag === "_") return "SinglePSpace_";
  return "SinglePSpace_" + storedHoleOpt(argFrag);
}

function preimageHoleRegex(node, opts) {
  const u = peelHoleExpr(node);
  if (cls(u) !== "LeanPreimage") return null;
  const L = holeRegexExpr(u.lhs ?? u.args?.[0], opts);
  const R = holeRegexExpr(u.rhs ?? u.args?.[1], opts);
  const lFrag = (L && L !== "_") ? L : "";
  const rFrag = (R && R !== "_") ? R : "";
  if (!lFrag && !rFrag) return "Preimage__";
  if (!lFrag) return "Preimage_" + storedHoleOpt(rFrag);
  if (!rFrag) return "Preimage" + storedHoleOpt(lFrag) + "_";
  return "Preimage" + storedHoleOpt(lFrag) + storedHoleOpt(rFrag);
}

const PREDICATE_APP_HEADS = new Set([
  "Measurable",
  "MeasurableSet",
  "AEMeasurable",
  "StronglyMeasurable",
  "AEStronglyMeasurable",
]);

function predicateAppHoleRegex(node, opts) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return null;
  const args = u.args || [];
  if (args.length < 2) return null;
  const head = unwrapParen(args[0]);
  if (cls(head) !== "LeanToken") return null;
  const headName = nameToken(head.text || "");
  if (!PREDICATE_APP_HEADS.has(headName)) return null;
  const last = unwrapParen(args[args.length - 1]);
  if (cls(last) === "LeanGetElem") return null;
  if (typeof isMeasurableJointArg === "function" && isMeasurableJointArg(last)) return null;
  const frags = [];
  for (let i = 1; i < args.length; i++) {
    const a = args[i];
    if (isImplyHole(a, opts, implyBinderSet(opts))) {
      frags.push("");
      continue;
    }
    const f = holeRegexExpr(a, opts);
    frags.push((f && f !== "_") ? f : "");
  }
  if (!frags.length) return null;
  if (frags.every((f) => !f)) return headName + "_".repeat(frags.length);
  let s = headName;
  for (const f of frags) {
    if (!f) s += "_";
    else s += "_" + storedHoleOpt(f);
  }
  return s;
}

function propertyAppHoleRegex(node, opts) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated") return null;
  const args = u.args || [];
  if (args.length < 2) return null;
  const head = unwrapParen(args[0]);
  if (cls(head) !== "LeanProperty") return null;
  const headName = nameExpr(head, opts);
  if (!headName) return null;
  if (headName !== "WithDensity" && headName !== "Pdf" && headName !== "Dens")
    return null;
  const frags = args.slice(1).map((a) => holeRegexExpr(a, opts));
  if (frags.every((f) => f == null || f === "" || f === "_"))
    return headName + "_".repeat(frags.length);
  let s = headName;
  for (const f of frags) {
    if (f == null || f === "" || f === "_") s += "_";
    else s += "_(" + f + ")";
  }
  return s;
}

function independencePerp(node) {
  if (node && typeof node.constructor?.independenceOf === "function") {
    const hit = node.constructor.independenceOf(node);
    if (hit) return hit;
  }
  const u = stripIndepWrap(node);
  if (cls(u) === "Lean_perp" && u.isIndependence !== false) return u;
  return null;
}

function condIndepBits(node) {
  const u = stripIndepWrap(node);
  if (cls(u) !== "LeanBitOr") return null;
  const perp = independencePerp(u.lhs ?? u.args?.[0]);
  if (!perp) return null;
  return { perp, cond: u.rhs ?? u.args?.[1] };
}

function storedNary(tag, frags) {
  const xs = (frags || []).map((f) => (f && f !== "_") ? f : "");
  if (!xs.length || xs.every((x) => !x)) return tag;
  let last = -1;
  for (let i = 0; i < xs.length; i++) if (xs[i]) last = i;
  let s = tag;
  for (let i = 0; i <= last; i++) s += xs[i] ? storedHoleOpt(xs[i]) : "_";
  if (last < xs.length - 1) s += "_".repeat(xs.length - 1 - last);
  return s;
}

function peelEtaFun(node) {
  const n = unwrapParen(node);
  if (cls(n) !== "Lean_fun") return node;
  const arrow = n.args?.[n.args.length - 1];
  const ac = cls(arrow);
  if (ac !== "LeanRightarrow" && ac !== "Lean_mapsto") return node;
  const binders = new Set();
  quantBinderNames(n, binders);
  quantBinderNames(arrow.args?.[0], binders);
  let body = peelHoleExpr(arrow.args?.[arrow.args.length - 1]);
  if (!body) return node;
  if (cls(body) === "LeanArgsSpaceSeparated" && (body.args || []).length >= 2) {
    const args = body.args;
    const last = unwrapParen(args[args.length - 1]);
    if (cls(last) === "LeanToken" && binders.has(last.text)) {
      if (args.length === 2) body = args[0];
      else return node;
    }
  }
  return body;
}

function rvOperandHoleFrag(node, opts) {
  const u = peelHoleExpr(peelEtaFun(node));
  if (!u) return "";
  const parts = commaParts(u) || jrsParts(u);
  if (parts && parts.length >= 2) {
    const frags = parts.map((p) => rvOperandHoleFrag(p, opts));
    return jointHoleFrag(frags) || "Joint__";
  }
  if (isGetElemColonSlice(u)) return "GetSlice__";
  if (cls(u) === "LeanGetElem") {
    const ge = getElemHoleRegexFrag(u, opts);
    if (ge && ge !== "_" && ge !== "") return ge;
    return "Get__";
  }
  const f = holeRegexExpr(u, opts);
  return (f && f !== "_") ? f : "";
}

function condIndepHoleRegex(node, opts) {
  const bits = condIndepBits(node);
  if (!bits) return null;
  const L = rvOperandHoleFrag(bits.perp.lhs ?? bits.perp.args?.[0], opts);
  const R = rvOperandHoleFrag(bits.perp.rhs ?? bits.perp.args?.[1], opts);
  const C = rvOperandHoleFrag(bits.cond, opts);
  const indep = storedNary("Indep", [L, R]);
  return storedNary("Cond", [indep, C]);
}

function eqJointHoleRegex(node, opts) {
  const u = unwrapParen(node);
  if (!eqJointSides(u)) return null;
  const sideFrag = (n) => {
    if (isCdotSection(n) || isSingleVarSide(n)) return "";
    if (isJointRvTuple(n)) {
      const parts = commaParts(peelHoleExpr(n)) || jrsParts(peelHoleExpr(n)) || [];
      const frags = parts.map((p) => rvOperandHoleFrag(p, opts));
      return storedNary("Joint", frags) || "Joint__";
    }
    const f = holeRegexExpr(n, opts);
    return (f && f !== "_") ? f : "";
  };
  return storedNary("Eq", [sideFrag(u.lhs ?? u.args?.[0]), sideFrag(u.rhs ?? u.args?.[1])]);
}

function holeRegexExpr(node, opts) {
  const frag = holeRegexExprWalk(node, opts);
  return typeof frag === "string" ? flattenStackedAll(flattenStackedExpect(frag)) : frag;
}

function holeRegexExprWalk(node, opts) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  if (cls(u) === "LeanVecNotation") return null;
  {
    const meas = measurableGetHoleRegex(u, opts);
    if (meas) return meas;
  }
  {
    const sps = singlePSpaceHoleRegex(u, opts);
    if (sps) return sps;
  }
  {
    const pre = preimageHoleRegex(u, opts);
    if (pre) return pre;
  }
  {
    const pred = predicateAppHoleRegex(u, opts);
    if (pred) return pred;
  }

  if (cls(u) === "Lean_Prob") {
    const cond = probCondGetHoleRegex(u, opts);
    if (cond) return cond;
    const ev = peelHoleExpr(u.scope);
    const frag = cls(ev) === "LeanGetElem" ? getElemHoleRegexFrag(ev, opts) : null;
    if (frag) return u.pathToken + "_" + storedHoleOpt(frag);
  }

  if (cls(u) === "Lean_prod") {
    const body = holeRegexExpr(u.scope ?? u.args?.[u.args.length - 1], opts);
    if (isCondProbProductBody(body)) {
      const dom = sumDomainName(u);
      return dom ? u.pathToken + storedHoleOpt(dom + "_") + storedHoleOpt(body) : u.pathToken + "_" + storedHoleOpt(body);
    }
  }

  if (cls(u) === "Lean_perp") {
    const T = u.pathToken;
    const left = u.lhs ?? u.args?.[0];
    const right = u.rhs ?? u.args?.[1];
    if (isJointRvTuple(left) && !isJointRvTuple(right)) return T + "(Joint__)_";
    const L = holeRegexExpr(left, opts);
    const R = holeRegexExpr(right, opts);
    const lFrag = (L && L !== "_") ? L : "";
    const rFrag = (R && R !== "_") ? R : "";
    if (!lFrag && !rFrag) return T;
    if (!lFrag) return T + "_" + storedHoleOpt(rFrag);
    if (!rFrag) return T + storedHoleOpt(lFrag) + "_";
    return T + storedHoleOpt(lFrag) + storedHoleOpt(rFrag);
  }

  {
    const ci = condIndepHoleRegex(u, opts);
    if (ci) return ci;
  }

  {
    const ej = eqJointHoleRegex(u, opts);
    if (ej) return ej;
  }

  if (cls(u) === "Lean_int") {
    const ire = integralHoleRegex(u, opts);
    if (ire) return ire;
  }

  {
    const parts = splitTopConjunction(u, false);
    if (parts && parts.length >= 2 && !opts?.asGiven && !isHoleAndTree(u, opts)) {
      const frags = parts.map((p) => holeRegexExpr(p, opts));
      if (frags.every((f) => f && f !== "_" && !/^And(?:_And)*_?$/.test(String(f))))
        return frags.join("/");
    }
  }

  const peelGuardsDeep = (n) => {
    return peelHoleExpr(peelGuardForalls(n));
  };
  const holeOpts = {
    ...opts,
    nameToken,
    isLeaf: (t) => isLeafName(t, opts.leaves),
    peelGuards: peelGuardsDeep,
    frozen: (n) => {
      if (cls(n) === "Lean_int") {
        const ire = integralHoleRegex(n, opts);
        if (ire) return ire;
      }
      if (cls(n) === "LeanIte") return iteHoleRegex(n, opts);
      if (cls(n) === "LeanGetElem") {
        const ge = getElemHoleRegexFrag(n, opts);
        if (ge !== undefined) return ge;
      }
      if (cls(n) === "Lean_approx") {
        const dec = decompImplyStruct(n, opts);
        if (dec) return dec;
      }
      if (cls(n) === "LeanBitOr" && cls(unwrapParen(n.args?.[0])) !== "Lean_perp") {
        let p = n.parent;
        while (p && (cls(p) === "LeanParenthesis" || cls(p) === "LeanColon")) p = p.parent;
        if (cls(p) === "Lean_Expect") {
          const left = unwrapParen(n.args?.[0]);
          let leftFrag = holeRegexExpr(left, opts);
          const tag = left?.pathToken || CLASS_TOKEN[cls(left)];
          if (tag && leftFrag === tag && (left?.args || []).length === 2)
            leftFrag = tag + "__";
          if (!leftFrag || leftFrag === "_") return "Cond__";
          return "Cond" + storedHoleOpt(leftFrag) + "_";
        }
      }
      {
        const app = propertyAppHoleRegex(n, opts);
        if (app) return app;
      }
      {
        const meas = measurableGetHoleRegex(n, opts);
        if (meas) return meas;
      }
      {
        const sps = singlePSpaceHoleRegex(n, opts);
        if (sps) return sps;
      }
      {
        const pre = preimageHoleRegex(n, opts);
        if (pre) return pre;
      }
      {
        const pred = predicateAppHoleRegex(n, opts);
        if (pred) return pred;
      }
      const frozen = nameExpr(n, opts);
      return frozen ? escapeHoleReLit(sanitizePathSeg(frozen)) : null;
    },
  };
  {
    const pc = cls(u);
    if (pc === "Lean_partial" || pc === "LeanPartial") {
      const ps = partialBoundScope(u);
      if (!ps) return "Deriv__";
      const scopeFrag = holeRegexExpr(ps.scope, opts);
      if (scopeFrag == null || scopeFrag === "" || scopeFrag === "_") return "Deriv__";
      return "Deriv_(" + scopeFrag + ")";
    }
  }
  if (cls(u) === "Lean_approx") {
    const dec = decompImplyStruct(u, opts);
    if (dec) return dec;
  }
  if (cls(u) === "Lean_forall" && opts?.asGiven) {
    const givenOpts = { ...opts, digitLiteral: true };
    const dec = decompImplyStruct(u, givenOpts);
    if (dec && dec.includes("(") && !dec.includes("(_|"))
      return dec;
    let body = u.scope ?? u.args?.[u.args.length - 1];
    body = peelHoleExpr(peelGuardForalls(body));
    if (cls(stripIndepWrap(body)) === "Lean_perp" || condIndepBits(body) || eqJointSides(body)) {
      const inner = holeRegexExpr(body, givenOpts);
      if (inner && inner !== "_" && inner !== "All") {
        if (inner === "All" || inner.startsWith("All_")) return inner;
        return "All_" + storedHoleOpt(inner);
      }
    }
    if (allNeProb0GivenName(u) === "All_NeProb_0") return "All_(Ne(Prob__)(0))";
    const inner = holeRegexExpr(body, givenOpts);
    if (inner && (/Measurable\(Get__\)/.test(inner) || /SinglePSpace_?\(/.test(inner))) {
      if (inner === "All" || inner.startsWith("All_")) return inner;
      return "All_" + storedHoleOpt(inner);
    }
  }
  if (cls(u) === "LeanEq" && opts?.asGiven) {
    const dec = decompImplyStruct(u, { ...opts, digitLiteral: true });
    if (dec && dec.includes("(") && !dec.includes("(_|")) return dec;
  }

  if ((cls(u) === "Lean_forall" || cls(u) === "Lean_exists") && isEqOfProbQuantTree(u)) {
    const tag = u.pathToken;
    let body = u.scope ?? u.args?.[u.args.length - 1];
    if (cls(u) === "Lean_forall") body = peelGuardForalls(body);
    body = peelQuantBody(body);
    const inner = holeRegexExpr(body, opts);
    if (inner && inner !== "_") {
      if (inner === tag || inner.startsWith(tag + "_")) return inner;
      return tag + "_" + storedHoleOpt(inner);
    }
  }

  if (cls(u) === "LeanEq") {
    const L = holeRegexExpr(u.lhs ?? u.args?.[0], opts);
    const R = holeRegexExpr(u.rhs ?? u.args?.[1], opts);
    if (isProbFamilyFrag(L) && isProbFamilyFrag(R)) {
      if (u.superscript === "ᵐ") {
        const side = (frag) => {
          let f = frag;
          if (/^[A-Za-z][A-Za-z0-9]*__$/.test(f)) f = f.slice(0, -2);
          return "(" + f + ")";
        };
        return side(L) + "/ae/" + side(R);
      }
      return "Eq" + storedHoleOpt(L) + storedHoleOpt(R);
    }
  }
  if (cls(u) === "LeanMul") {
    const L = holeRegexExpr(u.lhs ?? u.args?.[0], opts);
    const R = holeRegexExpr(u.rhs ?? u.args?.[1], opts);
    const probish = (f) => isProbHoleFrag(f) || String(f).startsWith("Prod(");
    if (probish(L) && probish(R))
      return "Mul" + storedHoleOpt(L) + storedHoleOpt(R);
  }
  if (cls(u) === "Lean_lt" || cls(u) === "Lean_gt" || cls(u) === "Lean_le" || cls(u) === "Lean_ge") {
    const dec = decompImplyStruct(u, opts);
    if (dec && dec.includes("(")) return dec;
  }
  if (cls(u) === "LeanProperty") {
    const propNode = u.rhs ?? u.args?.[1];
    const rawProp = cls(propNode) === "LeanToken" ? (propNode.text || "") : "";
    const propTok = rawProp ? nameToken(rawProp) : "";
    if (propTok && !HOLE_RE_TRIG_FN.test(rawProp)) {
      const dec = decompImplyStruct(u.lhs ?? u.args?.[0], opts);
      if (dec && dec.startsWith("UpdateCol")) return propTok + "(" + dec + ")";
    }
  }
  if (typeof u.holeRegex === "function") {
    const raw = binaryHoleDeriv(u.holeRegex(holeOpts));
    if (isGluedQuantEqRegex(raw)) {
      const dec = decompQuantHoleRegex(u, opts);
      if (dec) return dec;
    }
    if (/^Any_\((?:_\|)?And_[A-Za-z0-9_]+\)$/.test(String(raw || ""))) {
      const dec = decompImplyStruct(u, opts);
      if (dec) return dec;
    }
    return simplifyQuantRelDigit(simplifyIteHoleRegex(raw));
  }
  return holeOpts.frozen(u);
}

function pluralMulSHoleRegex(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  const c = cls(u);

  if (c === "Lean_rightarrow" || c === "LeanRightarrow")
    return pluralMulSHoleRegex(u.args?.[u.args.length - 1], opts);

  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const body = pluralMulSHoleRegex(bodyNode, opts);
    if (body == null || body === "") return null;
    if (body === tag || body.startsWith(tag + "_")) return body;
    return tag + "_(" + body + ")";
  }

  const relTag = CLASS_TOKEN[c];
  if (relTag === "Eq") {
    const args = u.args || [];
    const L = peelHoleExpr(args[0]);
    const R = args[1];
    const lc = cls(L);
    if (lc !== "LeanSub" && lc !== "LeanAdd") return null;
    const a = holeRegexExpr(L.args?.[0], opts);
    const b = holeRegexExpr(L.args?.[1], opts);
    if (!a || !b || a !== b) return null;
    if (!/^Mul\b/.test(a) && !/^Mul_/.test(a) && a !== "Mul" && !a.startsWith("Mul(")) return null;
    const mulS = a.replace(/^Mul/, "MulS");
    const opTag = lc === "LeanSub" ? "Sub" : "Add";
    const leftFrag = opTag + "(" + mulS + ")";
    const rhsFrag = holeRegexExpr(R, { ...opts, mulBothHolesBare: true });
    return relTag + "(" + leftFrag + wrapHoleOpt(rhsFrag) + ")";
  }
  return null;
}

function eqEqualMulSHoleRegex(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  const c = cls(u);

  if (c === "Lean_rightarrow" || c === "LeanRightarrow")
    return eqEqualMulSHoleRegex(u.args?.[u.args.length - 1], opts);

  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const body = eqEqualMulSHoleRegex(bodyNode, opts);
    if (body == null || body === "") return null;
    if (body === tag || body.startsWith(tag + "_") || body.startsWith(tag + "Eq")) return body;
    if (body.startsWith("Eq(")) return tag + "_" + body;
    return tag + "_(" + body + ")";
  }

  const relTag = CLASS_TOKEN[c];
  if (relTag === "Eq") {
    const args = u.args || [];
    const a = holeRegexExpr(args[0], opts);
    const b = holeRegexExpr(args[1], opts);
    if (!a || !b || a !== b) return null;
    if (!/^Mul\b/.test(a) && !/^Mul_/.test(a) && a !== "Mul" && !a.startsWith("Mul(")) return null;
    if (!/Deriv/.test(a)) return null;
    return "Eq(MulS(_(Deriv)))";
  }
  return null;
}

function holeFillStemsEqMulS(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return [];
  const c = cls(u);
  if (c === "Lean_rightarrow" || c === "LeanRightarrow")
    return holeFillStemsEqMulS(u.args?.[u.args.length - 1], opts);
  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const bodies = holeFillStemsEqMulS(bodyNode, opts);
    const out = [];
    for (const b of bodies) {
      if (!b) continue;
      if (b === tag || b.startsWith(tag + "_")) out.push(b);
      else out.push(tag + "_" + b);
    }
    return [...new Set(out)];
  }
  const relTag = CLASS_TOKEN[c];
  if (relTag !== "Eq") return [];
  const args = u.args || [];
  const a = holeRegexExpr(args[0], opts);
  const b = holeRegexExpr(args[1], opts);
  if (!a || !b || a !== b) return [];
  if (!/^Mul\b/.test(a) && !/^Mul_/.test(a) && a !== "Mul" && !a.startsWith("Mul(")) return [];
  if (!/Deriv/.test(a)) return [];
  return ["EqMulS_Deriv", "EqMulS"];
}

function isEqProb0Hole(eqFrag) {
  const s = String(eqFrag || "").replace(/\(_\|/g, "(");
  return s === "Eq(Prob__)(0)" || s === "Eq(0)(Prob__)";
}

function impEqualEqSHoleRegex(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  const c = cls(u);

  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const body = impEqualEqSHoleRegex(bodyNode, opts);
    if (body == null || body === "") return null;
    if (body === tag || body.startsWith(tag + "_")) return body;
    if (body.startsWith("ImpEqS(")) return tag + "_(" + body + ")";
    return tag + "_" + storedHoleOpt(body);
  }

  if (c === "Lean_rightarrow") {
    const args = u.args || [];
    const a = holeRegexExpr(args[0], opts);
    const b = holeRegexExpr(args[1], opts);
    if (!a || !b || a !== b) return null;
    if (!/^Eq\b/.test(a) && !a.startsWith("Eq(")) return null;
    if (isEqProb0Hole(a)) return "ImpEqS((Prob__)(0))";
    const eqS = a.replace(/^Eq/, "EqS");
    return "Imp" + storedHoleOpt(eqS);
  }
  return null;
}

function holeFillStemsImpEqS(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return [];
  const c = cls(u);
  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const bodies = holeFillStemsImpEqS(bodyNode, opts);
    const out = [];
    for (const b of bodies) {
      if (!b) continue;
      if (b === tag || b.startsWith(tag + "_")) out.push(b);
      else out.push(tag + "_" + b);
    }
    return [...new Set(out)];
  }
  if (c !== "Lean_rightarrow") return [];
  const args = u.args || [];
  const a = holeRegexExpr(args[0], opts);
  const b = holeRegexExpr(args[1], opts);
  if (!a || !b || a !== b) return [];
  if (!/^Eq\b/.test(a) && !a.startsWith("Eq(")) return [];
  const sideFills = holeFillStems(args[0], opts).filter(Boolean);
  const out = [];
  for (const e of sideFills) {
    if (!(e === "Eq" || e.startsWith("Eq"))) continue;
    out.push("Imp" + ("EqS" + e.slice(2)));
  }
  if (!out.length) out.push("ImpEqS");
  return [...new Set(out)];
}

function houseCollapseDivToRealProb(frag, keepProb) {
  const div = /Div\((?:_\|)?ToReal\((?:_\|)?Prob_+\)\)\((?:_\|)?ToReal\((?:_\|)?Prob_+\)\)/g;
  const to = keepProb ? "Div(Prob__)(Prob__)" : "Div";
  return String(frag || "").replace(div, to);
}

function houseExpectLhsForms(frag) {
  const text = String(frag || "");
  if (!/Div\((?:_\|)?ToReal\((?:_\|)?Prob/.test(text)) return [houseCollapseDivToRealProb(text, false)];
  const full = houseCollapseDivToRealProb(text, true);
  const simple = full.replace(/Div\((?:_\|)?Prob__\)\((?:_\|)?Prob__\)/g, "DivProbS__");
  return simple === full ? [full] : [full, simple];
}

function eqHouseHoleRegexAlts(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return [];
  const c = cls(u);
  if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") {
    return eqHouseHoleRegexAlts(firstConclusion(u), opts);
  }
  if (c === "Lean_rightarrow" || c === "LeanRightarrow") {
    return eqHouseHoleRegexAlts(u.args?.[u.args.length - 1], opts);
  }
  const relTag = CLASS_TOKEN[c];
  if (relTag === "Iff") {
    const L = holeRegexExpr(u.args?.[0] ?? u.lhs, opts);
    const R = holeRegexExpr(u.args?.[1] ?? u.rhs, opts);
    if (!L || L === "_" || !R || R === "_") return [];
    const houseSide = (frag) => {
      let f = frag;
      if (/^[A-Za-z][A-Za-z0-9]*__$/.test(f)) f = f.slice(0, -2);
      return "(" + f + ")";
    };
    const house = storeHoleGroups(houseSide(L) + "/is/" + houseSide(R));
    return house ? [house] : [];
  }
  if (relTag !== "Eq") return [];
  const args = u.args || [];
  const lhsForms = houseExpectLhsForms(holeRegexExpr(args[0], opts));
  const R = houseCollapseDivToRealProb(holeRegexExpr(args[1], opts), true);
  if (!R || R === "_") return [];
  const houseSide = (frag) => {
    let f = frag;
    if (/^[A-Za-z][A-Za-z0-9]*__$/.test(f)) f = f.slice(0, -2);
    return "(" + f + ")";
  };
  const out = [];
  for (const L of lhsForms) {
    if (!L || L === "_") continue;
    const storedL = storeHoleGroups(L);
    const soft = u.superscript === "ᵐ" ? "/ae/" : "/eq/";
    const house = storeHoleGroups(houseSide(L) + soft + houseSide(R));
    if (house && !out.includes(house)) out.push(house);
    if (storedL && storedL.includes("DivProbS__") && !out.includes(storedL)) out.push(storedL);
    if (storedL && storedL.includes("DivProbS__")) {
      const plural = "(" + storedL + ")" + soft + "(SubVarS__)";
      if (!out.includes(plural)) out.push(plural);
    }
  }
  return out;
}

function holeRegexMatchingParen(s, openIdx) {
  let depth = 0;
  for (let i = openIdx; i < s.length; i++) {
    if (s[i] === "(") depth++;
    else if (s[i] === ")") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function pluralEqualAppendChild(arg) {
  const s = String(arg || "");
  const head = /^([A-Z][A-Za-z0-9]*)/.exec(s);
  if (head && s[head[0].length] === "(") {
    const open = head[0].length;
    const close = holeRegexMatchingParen(s, open);
    if (close === s.length - 1 && close > open) return head[1] + "S" + s.slice(open + 1, close);
  }
  const m = /^(.*?)(_*)$/.exec(s);
  if (!m || !m[1]) return "";
  return m[1] + "S" + m[2];
}

function appendEqualPluralHoleRegex(reSource) {
  return equalBinaryPluralHoleRegex(reSource, "Append");
}

function equalBinaryPluralHoleRegex(reSource, tag) {
  const s = String(reSource || "");
  const head = String(tag || "");
  if (!head || !s.includes(head + "(")) return "";
  let out = "";
  let i = 0;
  let changed = false;
  while (i < s.length) {
    const atTag = s.startsWith(head + "(", i) && (i === 0 || !/[A-Za-z0-9]/.test(s[i - 1]));
    if (!atTag) {
      out += s[i];
      i++;
      continue;
    }
    const aOpen = i + head.length;
    const aClose = holeRegexMatchingParen(s, aOpen);
    const bOpen = aClose >= 0 ? aClose + 1 : -1;
    const bClose = bOpen >= 0 && s[bOpen] === "(" ? holeRegexMatchingParen(s, bOpen) : -1;
    if (aClose < 0 || bClose < 0) {
      out += s[i];
      i++;
      continue;
    }
    const left = s.slice(aOpen + 1, aClose);
    const right = s.slice(bOpen + 1, bClose);
    const plural = left && left === right ? pluralEqualAppendChild(left) : "";
    if (!plural) {
      out += s[i];
      i++;
      continue;
    }
    out += head + plural;
    i = bClose + 1;
    changed = true;
  }
  return changed ? out : "";
}

function isJointHoleFrag(frag) {
  const s = String(frag || "");
  return s === "Joint" || /^Joint_+$/.test(s) || s.startsWith("Joint(");
}

function stubIndepJointOperands(reSource) {
  const s = String(reSource || "");
  if (!s.includes("Indep(")) return "";
  let out = "";
  let i = 0;
  let changed = false;
  while (i < s.length) {
    const atIndep = s.startsWith("Indep(", i) && (i === 0 || !/[A-Za-z0-9]/.test(s[i - 1]));
    if (!atIndep) {
      out += s[i];
      i++;
      continue;
    }
    const aOpen = i + "Indep".length;
    const aClose = holeRegexMatchingParen(s, aOpen);
    const bOpen = aClose >= 0 ? aClose + 1 : -1;
    const bClose = bOpen >= 0 && s[bOpen] === "(" ? holeRegexMatchingParen(s, bOpen) : -1;
    if (aClose < 0 || bClose < 0) {
      out += s[i];
      i++;
      continue;
    }
    const left = s.slice(aOpen + 1, aClose);
    const right = s.slice(bOpen + 1, bClose);
    if (!isJointHoleFrag(left) || !isJointHoleFrag(right)) {
      out += s[i];
      i++;
      continue;
    }
    if (left === "Joint__" && right === "Joint__") {
      out += s.slice(i, bClose + 1);
      i = bClose + 1;
      continue;
    }
    out += "Indep(Joint__)(Joint__)";
    i = bClose + 1;
    changed = true;
  }
  return changed ? out : (out === s ? s : "");
}

function indepEqualJointSHoleRegex(reSource) {
  const stubbed = stubIndepJointOperands(reSource);
  if (!stubbed) return "";
  const compact = equalBinaryPluralHoleRegex(stubbed, "Indep");
  return compact && compact !== String(reSource || "") ? compact : "";
}

function readBalanced(s, open) {
  if (s[open] !== "(") return null;
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    if (s[i] === "(") depth++;
    else if (s[i] === ")") {
      depth--;
      if (depth === 0) return { text: s.slice(open + 1, i), end: i + 1 };
    }
  }
  return null;
}

function condSameHeadPluralAlts(re) {
  const s = String(re || "");
  const out = [];
  for (let i = 0; i + 5 <= s.length; i++) {
    if (!s.startsWith("Cond(", i)) continue;
    const l = readBalanced(s, i + 4);
    if (!l || s[l.end] !== "(") continue;
    const r = readBalanced(s, l.end);
    if (!r) continue;
    const hl = /^([A-Z][A-Za-z0-9]*)/.exec(l.text);
    const hr = /^([A-Z][A-Za-z0-9]*)/.exec(r.text);
    if (!hl || !hr || hl[1] !== hr[1]) continue;
    out.push(s.slice(0, i) + "Cond" + hl[1] + "S__" + s.slice(r.end));
  }
  return out;
}

function prodCondPluralAlts(re) {
  const s = String(re || "");
  const out = [];
  for (let i = 0; i + 4 <= s.length; i++) {
    if (!s.startsWith("Prod(", i)) continue;
    const dom = readBalanced(s, i + 4);
    if (!dom || s[dom.end] !== "(") continue;
    const body = readBalanced(s, dom.end);
    if (!body) continue;
    for (const alt of condSameHeadPluralAlts(body.text))
      out.push(s.slice(0, dom.end) + "(" + alt + ")" + s.slice(body.end));
  }
  return out;
}

export function pluralRepeatedAppAlts(alts) {
  const out = [];
  const push = (v) => {
    const stored = storeHoleGroups(v);
    if (stored && !out.includes(stored)) out.push(stored);
  };
  for (const alt of alts || []) push(alt);
  for (const alt of alts || []) {
    for (const plural of pluralRepeatedHoleAlts(alt)) push(plural);
  }
  return out;
}

export function unaryHeadHoles(alt, node, opts = {}) {
  if (!alt || !node) return String(alt || "");
  const heads = new Set();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty") {
      const obj = n.args?.[0];
      const prop = n.args?.[1];
      if (cls(obj) === "LeanToken" && cls(prop) === "LeanToken" && isLeafName(obj.text || "", opts.leaves)) {
        const head = nameToken(prop.text || "");
        if (head) heads.add(head);
      }
    }
    for (const a of n.args || []) walk(a);
  })(node);
  let out = String(alt);
  for (const head of heads) {
    const lit = escapeHoleReLit(head);
    out = out.replace(new RegExp(`(?<![A-Za-z0-9_])${lit}(?![A-Za-z0-9_(])`, "g"), head + "_");
  }
  return out;
}

export function holeRegexAlternatives(typeNode, opts = {}) {
  const primary = implyHoleRegexFromAst(typeNode, opts);
  const out = [];
  if (primary) out.push(storeHoleGroups(primary));
  if (!opts.asGiven && primary) {
    const compact = appendEqualPluralHoleRegex(primary);
    if (compact && compact !== primary && !out.includes(storeHoleGroups(compact))) out.push(storeHoleGroups(compact));
    const indepJointS = indepEqualJointSHoleRegex(primary);
    if (indepJointS && indepJointS !== primary && !out.includes(storeHoleGroups(indepJointS))) out.push(storeHoleGroups(indepJointS));
    for (const alt of pluralRepeatedHoleAlts(primary)) {
      const stored = storeHoleGroups(alt);
      if (stored && !out.includes(stored)) out.push(stored);
    }
    for (const alt of prodCondPluralAlts(primary)) {
      const stored = storeHoleGroups(alt);
      if (stored && !out.includes(stored)) out.push(stored);
    }
  }
  const relMirror = quantRelDigitMirror(primary);
  if (relMirror && !out.includes(storeHoleGroups(relMirror))) out.push(storeHoleGroups(relMirror));
  const plural = pluralMulSHoleRegex(typeNode, opts);
  if (plural && plural !== primary) out.push(storeHoleGroups(plural));
  const eqMulS = eqEqualMulSHoleRegex(typeNode, opts);
  if (eqMulS && eqMulS !== primary && !out.includes(storeHoleGroups(eqMulS))) out.push(storeHoleGroups(eqMulS));
  const impEqS = impEqualEqSHoleRegex(typeNode, opts);
  if (impEqS && impEqS !== primary && !out.includes(storeHoleGroups(impEqS))) out.push(storeHoleGroups(impEqS));
  for (const house of eqHouseHoleRegexAlts(typeNode, opts)) {
    if (house && house !== primary && !out.includes(storeHoleGroups(house))) out.push(storeHoleGroups(house));
    for (const alt of pluralRepeatedHoleAlts(house)) {
      const stored = storeHoleGroups(alt);
      if (stored && stored !== primary && !out.includes(stored)) out.push(stored);
    }
  }
  if (!opts.asGiven) {
    for (const re of out.slice()) {
      const m = /^\(([\s\S]*)\)\/eq\/\(([\s\S]*)\)$/.exec(String(re));
      if (!m) continue;
      for (const side of [m[1], m[2]]) {
        if (side.includes("(_|") || !/^[A-Z][A-Za-z0-9]*(?:_?\(|__|_)/.test(side)) continue;
        const stored = storeHoleGroups(side);
        if (stored && !out.includes(stored)) out.push(stored);
      }
    }
  }
  const named = nameExpr(typeNode, opts);
  const primaryDecomp = out.some((r) => /(?:Any|All)_\(_\|Eq/.test(String(r)) || String(r).includes("All_(Eq(") || String(r).includes("All_(Eq_(") || String(r).includes("Any_(Eq(") || String(r).includes("Any_(Eq_(") || String(r).includes("All_(Ne(") || String(r).includes("And(") || /(?:Any|All)_\(And\(/.test(String(r)) || String(r).includes("Ite(") || /(?:Any|All)_\([A-Za-z][A-Za-z0-9]*_?\(/.test(String(r)));
  const guardGlued = /Imp/.test(String(named || "")) && out.some((r) => /(?:Any|All)_\(/.test(String(r)));
  const admitted = out.some((re) => String(re).includes("(") && matchImplyHoleRegex(re, named));
  if (named && !named.includes("/") && !hasQuantEqSlash(named) && /^(?:Any|All)_/.test(named) && !out.includes(named)
      && !(primaryDecomp && !named.includes("("))
      && !guardGlued
      && !admitted)
    out.push(storeHoleGroups(named));
  if (!opts.asGiven && !opts.skipCollectHoleAlternatives) {
    const altOpts = {
      ...opts,
      nameToken,
      isLeaf: (t) => isLeafName(t, opts.leaves),
    };
    for (const alt of collectHoleRegexAlternatives(typeNode, altOpts)) {
      const stored = storeHoleGroups(alt);
      if (stored && !out.includes(stored)) out.push(stored);
    }
  }
  const alts = out.length ? pluralRepeatedAppAlts(out) : ["_"];
  const informative = alts.filter((alt) => {
    const m = /^([A-Za-z][A-Za-z0-9]*)__$/.exec(String(alt));
    if (!m) return true;
    return !alts.some((other) => other !== alt && String(other).startsWith(m[1] + "("));
  });
  const relaxPads = (s) => s.replace(/([A-Za-z][A-Za-z0-9]*)__/g, "$1");
  const padded = informative.filter((alt) => {
    const s = String(alt);
    if (s.includes("__")) return true;
    return !informative.some((other) => {
      const o = String(other);
      return o !== s && o.includes("__") && relaxPads(o) === relaxPads(s);
    });
  });
  return padded.map((alt) => unaryHeadHoles(alt, typeNode, opts));
}

function holeFillStems(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return [""];
  const c = cls(u);
  if (c === "LeanVecNotation") return [""];

  const uniq = (xs) => {
    const out = [];
    const seen = new Set();
    for (const x of xs || []) {
      const k = x === "" ? "\0" : x;
      if (seen.has(k)) continue;
      seen.add(k);
      out.push(x);
    }
    return out;
  };
  const cartJoin = (lefts, rights, join) => {
    const out = [];
    for (const l of lefts) for (const r of rights) out.push(join(l, r));
    return uniq(out);
  };

  if (c === "LeanToken") {
    const raw = u.text || "";
    if (!raw || raw === "_" || isLeafName(raw, opts.leaves)) return [""];
    if (/^-?\d+$/.test(raw)) return [raw, ""];
    const tok = nameToken(raw);
    return tok ? [tok] : [""];
  }
  if (c === "LeanRightarrow")
    return holeFillStems(u.args?.[u.args.length - 1], opts);
  if (c === "Lean_rightarrow") {
    const args = u.args || [];
    const Ls = holeFillStems(args[0], opts);
    const Rs = holeFillStems(args[1], opts);
    const aRe = holeRegexExpr(args[0], opts);
    const bRe = holeRegexExpr(args[1], opts);
    const joined = cartJoin(Ls, Rs, (l, r) => {
      if (!l && !r) return "Imp__";
      if (!l && r) return "Imp_" + r;
      if (l && !r) return "Imp" + l;
      return "Imp" + l + r;
    });
    const plural = [];
    if (aRe && bRe && aRe === bRe && (/^Eq\b/.test(aRe) || aRe.startsWith("Eq("))) {
      for (const e of Ls.filter(Boolean)) {
        if (!(e === "Eq" || e.startsWith("Eq"))) continue;
        plural.push("Imp" + ("EqS" + e.slice(2)));
      }
    }
    return uniq([...plural, ...joined, ""]);
  }
  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const bodies = holeFillStems(bodyNode, opts);
    return uniq(bodies.flatMap((b) => {
      if (!b) return [tag, ""];
      if (b === tag || b.startsWith(tag + "_")) return [b, ""];
      const eqAtom = quantWrapEqBody(tag, b);
      if (eqAtom) return [eqAtom, ""];
      if (hasQuantEqSlash(b) || String(b).includes("/eq/") || String(b).includes(".eq.")) return [""];
      return [tag + "_" + b, ""];
    }));
  }
  if (c === "Lean_partial" || c === "LeanPartial") {
    const ps = partialBoundScope(u);
    if (!ps) return [""];
    const scopes = holeFillStems(ps.scope, opts);
    const filled = scopes.filter(Boolean);
    if (!filled.length) return ["Deriv_", ""];
    return uniq([
      ...filled.map((s) => "Deriv_" + s),
      "Deriv_",
      "",
    ]);
  }
  if (c === "Lean_nabla" || c === "LeanNabla") {
    return nablaBoundScope(u) ? ["Grad_", ""] : [""];
  }
  if (c === "LeanProperty") {
    const obj = u.args?.[0];
    const prop = u.args?.[1];
    const rawProp = cls(prop) === "LeanToken" ? (prop.text || "") : "";
    const propTok = rawProp ? nameToken(rawProp) : "";
    if (propTok && HOLE_RE_TRIG_FN.test(rawProp)) {
      const inners = holeFillStems(obj, { ...opts, inTrigProp: true });
      return uniq(inners.flatMap((inner) => inner ? [propTok + inner, ""] : [propTok + "_", ""]));
    }
    return holeFillStems(obj, opts);
  }
  if (c === "Lean_sqrt") {
    const inners = holeFillStems(u.args?.[0], opts);
    return uniq(inners.flatMap((inner) => inner ? ["Sqrt" + inner, ""] : ["Sqrt", ""]));
  }
  if (c === "LeanNeg" || c === "LeanInv") {
    const tag = u.pathToken;
    const inners = holeFillStems(u.args?.[0], opts);
    return uniq(inners.flatMap((inner) => inner ? [tag + inner, ""] : [tag, ""]));
  }
  if (HOLE_RE_ARITH.has(c)) {
    const tag = u.pathToken;
    const args = u.args || [];
    const Ls = holeFillStems(args[0], opts);
    const Rs = args.length > 1 ? holeFillStems(args[1], opts) : [""];
    const joined = [];
    for (const l of Ls) for (const r of Rs) {
      if (!l && !r) {
        if (c === "LeanMul") joined.push(opts.mulBothHolesBare ? tag : tag + "__");
        else joined.push(tag);
        continue;
      }
      if (l && r) {
        const glued = tag + l + r;
        const apo = tag + joinDigits(l, r);
        joined.push(glued);
        if (apo !== glued) joined.push(apo);
        continue;
      }
      if (l && !r) {
        if (c === "LeanMul" && /^(?:T|Adjoint|Conj)$/.test(l)) joined.push(tag + l + "__");
        else joined.push(tag + l + "_");
        continue;
      }
      joined.push(tag + "_" + r);
    }
    return uniq([...joined, ""]);
  }
  const relTag = CLASS_TOKEN[c];
  if (relTag && ["Eq", "Ne", "Lt", "Gt", "Le", "Ge", "Iff", "Subset", "Dvd"].includes(relTag)) {
    const args = u.args || [];
    const Ls = holeFillStems(args[0], opts);
    const Rs = holeFillStems(args[1], opts);
    const joined = cartJoin(Ls, Rs, (l, r) => {
      if (!l && !r) return relTag;
      if (!l && r) return relTag + "_" + r;
      if (l && !r) return relTag + l;
      return relTag + l + r;
    });
    return uniq([...joined, ""]);
  }
  if (c === "LeanArgsSpaceSeparated") {
    const head = u.args?.[0];
    const rawHead = cls(head) === "LeanToken" ? (head.text || "") : "";
    const headTok = rawHead ? nameToken(rawHead) : "";
    if (headTok && HOLE_RE_TRIG_FN.test(rawHead)) {
      let inners = [""];
      for (let i = 1; i < (u.args || []).length; i++) {
        const got = holeFillStems(u.args[i], opts);
        if (got.some((x) => x)) { inners = got; break; }
      }
      return uniq(inners.flatMap((inner) => inner ? [headTok + inner, ""] : [headTok + "_", ""]));
    }
  }

  if (c === "Lean_Expect" || c === "Lean_Prob" || c === "Lean_Var") {
    const tok = u.pathToken;
    const scopes = holeFillStems(u.scope ?? u.args?.[1], opts);
    const filled = scopes.filter(Boolean);
    if (!filled.length) return uniq([`${tok}__`, ""]);
    return uniq([
      ...filled.map((s) => (tok === "Expect" && s === "Mul" ? "Expect_Mul" : `${tok}_` + s)),
      `${tok}__`,
      "",
    ]);
  }

  if (c === "LeanGetElem") {
    const headTok = cls(u.args?.[0]) === "LeanToken" ? (u.args[0].text || "") : "";
    if (headTok === "ℙ" || headTok === "∇" || headTok === "Var" || headTok === "variance") {
      const frozen = nameExpr(u, opts);
      return frozen ? [sanitizePathSeg(frozen)] : [""];
    }
    if (isGetElemColonSlice(u)) return uniq(["GetSlice", ""]);
    if (isBinderGetAtLiteral(u, opts)) return [""];
    if (isGetIndexNoise(u.args?.[1], opts)) return holeFillStems(u.args?.[0], opts);
    const idxs = holeFillStems(u.args?.[1], opts);
    return uniq(idxs.flatMap((idx) => (idx ? ["Get_" + idx, ""] : ["Get_", ""])));
  }

  if (c === "Lean_perp") {
    const T = u.pathToken;
    const Ls = holeFillStems(u.lhs ?? u.args?.[0], opts);
    const Rs = holeFillStems(u.rhs ?? u.args?.[1], opts);
    const joined = [];
    for (const l of Ls.length ? Ls : [""]) for (const r of Rs.length ? Rs : [""]) {
      if (l && r) joined.push(T + l + "_" + r);
      else if (!l && r) joined.push(T + "_" + r);
      else if (l && !r) joined.push(T + l);
      else joined.push(T);
    }
    return uniq([...joined, ""]);
  }

  if (c === "LeanBitOr" && condIndepBits(u)) {
    const T = u.pathToken;
    const bits = condIndepBits(u);
    const indeps = holeFillStems(bits.perp, opts);
    const Cs = holeFillStems(bits.cond, opts);
    const joined = [];
    for (const ind of indeps.length ? indeps : [""])
      for (const cnd of Cs.length ? Cs : [""]) {
        let stem = T;
        if (ind) stem += ind;
        else if (cnd) stem += "_";
        if (cnd) stem += (ind ? "_" : "") + cnd;
        if (!ind && !cnd) stem = T;
        joined.push(stem);
      }
    return uniq([...joined, ""]);
  }

  const frozen = nameExpr(u, opts);
  return frozen ? [sanitizePathSeg(frozen)] : [""];
}

function holeFillStemsPlural(node, opts = {}) {
  const u = peelHoleExpr(node);
  if (!u) return [];
  const c = cls(u);
  if (c === "Lean_rightarrow" || c === "LeanRightarrow")
    return holeFillStemsPlural(u.args?.[u.args.length - 1], opts);
  if (c === "Lean_forall" || c === "Lean_exists") {
    const tag = u.pathToken;
    const rawBody = u.args?.[u.args.length - 1];
    const bodyNode = c === "Lean_forall" ? peelGuardForalls(rawBody) : rawBody;
    const bodies = holeFillStemsPlural(bodyNode, opts);
    const out = [];
    for (const b of bodies) {
      if (!b) continue;
      if (b === tag || b.startsWith(tag + "_")) out.push(b);
      else out.push(tag + "_" + b);
    }
    return [...new Set(out)];
  }
  const relTag = CLASS_TOKEN[c];
  if (relTag === "Eq") {
    const args = u.args || [];
    const L = peelHoleExpr(args[0]);
    const lc = cls(L);
    if (lc !== "LeanSub" && lc !== "LeanAdd") return [];
    const aName = nameExpr(L.args?.[0], opts) || "";
    const bName = nameExpr(L.args?.[1], opts) || "";
    if (!aName || aName !== bName || !/^Mul/.test(aName)) return [];
    const opTag = lc === "LeanSub" ? "Sub" : "Add";
    const sideStems = holeFillStems(L.args[0], opts).filter(Boolean);
    const out = [];
    const rhsPreferred = ["Mul_Deriv", "MulMul__Deriv"];
    for (const s of sideStems) {
      const mulS = String(s).replace(/^Mul/, "MulS").replace(/_+$/, "");
      if (!mulS) continue;
      const left = opTag + mulS;
      out.push(relTag + left);
      for (const r of rhsPreferred) {
        out.push(relTag + left + "_" + r);
      }
    }
    const full = nameExpr(u, opts);
    if (full) out.push(sanitizePathSeg(full));
    return [...new Set(out.filter(Boolean))];
  }
  return [];
}

export function implyStemFromRelPath(relPath) {
  let s = String(relPath || "").replace(/\\/g, "/").replace(/\.lean$/, "");
  if (s.startsWith("Lemma/")) s = s.slice("Lemma/".length);
  const parts = s.split("/").filter(Boolean);
  if (parts.length < 2) return "";
  let rest = parts.slice(1).join("/");
  const ofi = rest.indexOf("/of/");
  if (ofi >= 0) rest = rest.slice(0, ofi);
  return rest;
}

export function stemMatchesAnyHoleRegex(stem, regexAlts) {
  const alts = Array.isArray(regexAlts) ? regexAlts : (regexAlts ? [regexAlts] : []);
  return alts.some((re) => matchImplyHoleRegex(re, stem));
}

export function ofStemsFromRelPath(relPath) {
  let s = String(relPath || "").replace(/\\/g, "/").replace(/\.lean$/, "");
  if (s.startsWith("Lemma/")) s = s.slice("Lemma/".length);
  const ofi = s.indexOf("/of/");
  if (ofi < 0) return [];
  return s.slice(ofi + 4).split("/").filter(Boolean);
}

export function suggestionPathMatchesHoles(relPath, implyRegexAlts, givenRegexLists, opts = {}) {
  if (unfilledHolePiece(relPath)) return false;
  const stem = implyStemFromRelPath(relPath);
  if (!stemMatchesAnyHoleRegex(stem, implyRegexAlts)) return false;
  const ofSegs = ofStemsFromRelPath(relPath);
  const lists = Array.isArray(givenRegexLists) ? givenRegexLists : [];
  const optional = opts.optionalFlags || [];
  let si = 0;
  for (let i = 0; i < lists.length; i++) {
    const regexes = lists[i] || [];
    if (!regexes.length) continue;
    if (si >= ofSegs.length) {
      if (optional[i]) continue;
      return false;
    }
    if (!stemMatchesAnyHoleRegex(ofSegs[si], regexes)) {
      if (optional[i]) continue;
      return false;
    }
    si++;
  }
  return true;
}

export function consistentSuggestionPaths(section, implyStems, givenStemLists, implyRegexAlts, givenRegexLists, opts = {}) {
  const sec = String(section || "").replace(/\\/g, "/");
  if (!sec) return [];
  const optional = opts.optionalFlags || [];
  const cap = opts.cap ?? 20000;
  const uniqStem = (xs) => [...new Set((xs || []).filter(Boolean).map((x) => sanitizeRelPath(String(x))).filter(Boolean))];
  const implyOk = uniqStem(implyStems).filter((s) => !unfilledHolePiece(s) && stemMatchesAnyHoleRegex(s, implyRegexAlts));
  const givenLists = (givenStemLists || []).map((stems, i) => {
    const regs = (givenRegexLists && givenRegexLists[i]) || [];
    const kept = uniqStem(stems).filter((s) => !unfilledHolePiece(s) && stemMatchesAnyHoleRegex(s, regs));
    if (kept.length) return kept;
    return optional[i] ? [""] : [];
  });
  if (givenLists.some((g, i) => !optional[i] && !g.length)) return [];
  let givenPaths = [""];
  for (let i = 0; i < givenLists.length; i++) {
    const next = [];
    const alts = givenLists[i].length ? givenLists[i] : [""];
    outer: for (const prefix of givenPaths) {
      for (const a of alts) {
        next.push(prefix && a ? prefix + "/" + a : prefix || a);
        if (next.length >= cap) break outer;
      }
    }
    givenPaths = next;
    if (givenPaths.length >= cap) break;
  }
  const out = [];
  const seen = new Set();
  outer2: for (const imply of implyOk) {
    for (const gp of givenPaths) {
      const body = (gp
        ? sec + "/" + imply + "/of/" + gp + ".lean"
        : sec + "/" + imply + ".lean").replace(/\\/g, "/");
      if (seen.has(body)) continue;
      if (!suggestionPathMatchesHoles(body, implyRegexAlts, givenRegexLists, { optionalFlags: optional })) continue;
      seen.add(body);
      out.push(body);
      if (out.length >= cap) break outer2;
    }
  }
  return out;
}

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
  if (!isExpectAppNode(right)) {
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

function eqSymmToDualTSumBodyName(implyStmts, houseFromDisk = "") {
  return isEqSymmToDualTSumGradLogShape(implyStmts) ? houseFromDisk : "";
}

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

function treeHasTokenText(node, texts) {
  const want = new Set(texts);
  let found = false;
  (function walk(n) {
    if (!n || typeof n !== "object" || found) return;
    if (cls(n) === "LeanToken" && want.has(n.text || "")) found = true;
    for (const a of n.args || []) walk(a);
  })(node);
  return found;
}

function isChiSquareApp(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanArgsSpaceSeparated" && (u.args || []).length >= 1) {
    const h = u.args[0];
    if (cls(h) === "LeanProperty" && cls(h.args?.[1]) === "LeanToken" && h.args[1].text === "chiSquare")
      return true;
    if (cls(h) === "LeanToken" && h.text === "chiSquare") return true;
  }
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && u.args[1].text === "chiSquare")
    return true;
  return false;
}

function isProdOfTwoChiSquare(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length !== 2) return false;
  const left = u.args[0];
  const right = u.args[1];
  if (cls(left) !== "LeanProperty" || cls(left.args?.[1]) !== "LeanToken" || left.args[1].text !== "prod")
    return false;
  return isChiSquareApp(left.args?.[0]) && isChiSquareApp(right);
}

function isMapPiGaussianRealHead(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken" || u.args[1].text !== "map")
    return false;
  const obj = u.args?.[0];
  return treeHasTokenText(obj, ["pi"]) && treeHasTokenText(obj, ["gaussianReal"]);
}

function isMapPiGaussianRealEqProdChiSquareSShape(implyStmts) {
  let hasMapPiGauss = false;
  let hasProdChi = false;
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (isMapPiGaussianRealHead(n)) hasMapPiGauss = true;
    if (cls(n) === "LeanArgsIndented" && isMapPiGaussianRealHead(n.args?.[0])) hasMapPiGauss = true;
    if (isProdOfTwoChiSquare(n)) hasProdChi = true;
    for (const a of n.args || []) walk(a);
  })(implyStmts);
  return hasMapPiGauss && hasProdChi;
}

function mapPiGaussianRealEqProdChiSquareSBodyName(implyStmts, houseFromDisk = "") {
  if (!isMapPiGaussianRealEqProdChiSquareSShape(implyStmts)) return "";
  const house = String(houseFromDisk || "").replace(/\\/g, "/");
  if (/MapPi_?GaussianReal\/eq\/ProdChiSquareS/.test(house)) return house;
  return "MapPi_GaussianReal/eq/ProdChiSquareS";
}

export function mulInvSqrtNodeChoices(node, opts = {}) {
  if (node && typeof node.pathChoices === "function") {
    const ch = node.pathChoices(opts);
    if (cls(node) === "Lean_nabla" || cls(node) === "LeanNabla") return nablaPathChoicesToGrad(ch);
    return ch;
  }
  return [""];
}

export function mulInvSqrtCombineMulChoices(leftChoices, rightChoices) {
  return pathCombineMulChoices(leftChoices, rightChoices);
}

export function mulInvSqrtEqFlatStem(lhs, rhs) {
  return pathEqFlatStem(lhs, rhs);
}

export function mulInvSqrtEqCombineChoices(leftChoices, rightChoices, house = "") {
  return pathEqCombineChoices(leftChoices, rightChoices, house);
}

export function mulInvSqrtEqImplyStemsFromTree(implyStmts, opts = {}, house = "") {
  const eq = peelImplyEq(implyStmts);
  if (!eq || typeof eq.pathImplyStems !== "function") return null;
  return eq.pathImplyStems(opts, house);
}

export function mulInvSqrtEqAllowedImplyStems(house = "", implyStmts = null, opts = {}) {
  if (!implyStmts) return [];
  const got = mulInvSqrtEqImplyStemsFromTree(implyStmts, opts, house);
  return got ? got.stems : [];
}

export function mulInvSqrtEqFlatImplyStems(implyStmts = null, opts = {}, house = "") {
  const stems = mulInvSqrtEqAllowedImplyStems(house, implyStmts, opts);
  return stems.filter((s) => !String(s).includes("/eq/"));
}

export function isAllowedMulInvSqrtEqSlashImply(stem) {
  const s = String(stem || "").replace(/\\/g, "/").replace(/\.lean$/, "");
  return /^(MulInvSqrt|MulInv|Mul)\/eq\/(MulSqrt_Div|MulSqrt|Mul_Div|Mul)$/.test(s);
}

export function isAllowedMulInvSqrtEqFlatImply(stem) {
  const s = String(stem || "").replace(/\\/g, "/").replace(/\.lean$/, "");
  if (s === "EqMulS") return false;
  if (s === "EqMul__Mul" || s === "EqMul_Mul") return false;
  if (s === "EqMulInv_Mul") return false;
  if (s === "EqMulInv__Mul") return true;
  if (s === "EqMulInvSqrt_Mul") return false;
  if (s === "EqMulInvSqrt__Mul") return true;
  if (/^EqMul__(MulSqrt_Div|MulSqrt|Mul_Div)$/.test(s)) return true;
  if (/^EqMulInv__(MulSqrt_Div|MulSqrt|Mul_Div)$/.test(s)) return true;
  if (/^EqMulInvSqrt__(MulSqrt_Div|MulSqrt|Mul_Div)$/.test(s)) return true;
  return false;
}

export function isAllowedMulInvSqrtEqImply(stem) {
  return isAllowedMulInvSqrtEqSlashImply(stem) || isAllowedMulInvSqrtEqFlatImply(stem);
}

export function isMulInvSqrtEqFamily(altsOrPreferred) {
  const hit = (raw) => {
    const s = String(raw || "").replace(/\\/g, "/");
    if (isAllowedMulInvSqrtEqImply(s)) return true;
    return /(?:^|\/)(MulInvSqrt|MulInv|Mul)\/eq\/(MulSqrt_Div|MulSqrt|Mul_Div|Mul)(?:\/|$)/.test(s);
  };
  if (typeof altsOrPreferred === "string") return hit(altsOrPreferred);
  const list = altsOrPreferred || [];
  if (list.preferred && hit(list.preferred)) return true;
  return list.some((a) => hit(a));
}

function peelImplyEq(implyStmts) {
  const u = peelStmt(implyStmts);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return null;
  return u;
}

function isExpectAppNode(node) {
  if (expectProbVarBoundScope(node)?.kind === "Lean_Expect") return true;
  return !!legacyExpectProbVarApp(node, "𝔼");
}

function isArgMaxMinGetElem(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanGetElem" || cls(u.args?.[0]) !== "LeanToken") return false;
  const t = u.args[0].text || "";
  return t === "max⁻¹" || t === "min⁻¹";
}
function argMaxMinTokenName(node) {
  const u = unwrapParen(node);
  const lim = limitsBigOpBoundScope(u);
  if (lim && (lim.kind === "Lean_argmax" || lim.kind === "Lean_argmin")) return lim.pathToken;
  if (cls(u) === "LeanArgsSpaceSeparated" && isArgMaxMinGetElem(u.args?.[0])) {
    return argMaxMinTokenName(u.args[0]);
  }
  const t = cls(u) === "LeanGetElem" ? u.args?.[0]?.text : "";
  return t === "max⁻¹" ? "ArgMax" : t === "min⁻¹" ? "ArgMin" : "";
}
function isArgMaxMinApp(node) {
  const u = unwrapParen(node);
  const lim = limitsBigOpBoundScope(u);
  if (lim && (lim.kind === "Lean_argmax" || lim.kind === "Lean_argmin") && lim.scope != null) return true;
  return cls(u) === "LeanArgsSpaceSeparated" && isArgMaxMinGetElem(u.args?.[0]) && (u.args || []).length >= 2;
}
function argMaxMinBody(node) {
  const u = unwrapParen(node);
  if (!isArgMaxMinApp(u)) return null;
  const lim = limitsBigOpBoundScope(u);
  let b = lim ? unwrapParen(lim.scope) : unwrapParen(u.args[1]);
  while (cls(b) === "LeanColon") b = unwrapParen(b.args?.[0]);

  return b;
}
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

function matrixStackEntryBody(node) {
  let u = unwrapParen(node);
  if (cls(u) === "LeanProperty" && cls(u.args?.[1]) === "LeanToken" && u.args[1].text === "det") {
    u = unwrapParen(u.args[0]);
  }
  if (cls(u) !== "LeanStack" || !matrixFinBindersOf(u)) return null;
  return peelEntryStmt(u.scope ?? u.args?.[1]);
}

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

function gradientBody(node) {
  const u = unwrapParen(node);
  if (cls(u) === "Lean_nabla" || cls(u) === "LeanNabla") {
    const bs = nablaBoundScope(u);
    if (!bs) return null;
    if (bs.scope != null && cls(bs.scope) !== "LeanCaret") return bs.scope;
    return null;
  }
  if (cls(u) !== "LeanArgsSpaceSeparated" || (u.args || []).length < 2) return null;
  const head = u.args[0];
  const nabla = "∇";
  const isGradHead =
    (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === nabla) ||
    (cls(head) === "LeanToken" && head.text === nabla);
  if (!isGradHead) return null;
  const rest = u.args.slice(1);
  if (rest.length === 1) return rest[0];
  return appSlice(u, rest);
}

function preAlts(node, opts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  if (opts.asGiven && c === "LeanArgsSpaceSeparated" && cls(args[0]) === "LeanToken" && args[0].text === "IsPolicyTrajectory") {
    return canon ? ["IsPolicyTrajectory"] : uniq(["IsPolicyTrajectory", "All_Eq"]);
  }
  if (c === "Lean_nabla" || c === "LeanNabla") {
    const alts = nablaGradAlts(node, opts);
    if (alts.length) {
      const gb = gradientBody(node);
      if (gb) {
        const x = A(gb);
        const ranked = [];
        for (const y of x) {
          ranked.push("Grad" + y);
          if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
            ranked.push("GradExpect_" + y.slice("Expect".length));
          }
          ranked.push("Grad_" + y);
        }
        return ranked.length ? uniq([...ranked, ...alts]) : uniq(alts);
      }
      return canon ? [alts[0]] : uniq(alts);
    }
  }
  {
    const gb = gradientBody(node);
    if (gb) {
      const x = A(gb);
      const ranked = [];
      for (const y of x) {
        ranked.push("Grad" + y);
        if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
          ranked.push("GradExpect_" + y.slice("Expect".length));

        }
        ranked.push("Grad_" + y);
      }
      return ranked.length ? uniq(ranked) : ["Grad"];
    }
  }

  if (isSupLtInfty(node)) return canon ? [supBoundCanon(node)] : supBoundAlts(node);
  if (isBddAboveSup(node)) return canon ? [supBoundCanon(node)] : uniq([...supBoundAlts(node), ...nameExprAltsBase(node, opts)]);
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
    const T = node.pathToken;
    const b = A(args[args.length - 1]);
    const glueLim = (y) => (y.startsWith("Prob") ? [T + "_" + y, T + y, T + "/" + y] : [T + y, T + "_" + y, T + "/" + y]);
    const lim = b.length ? uniq(b.flatMap(glueLim)) : [T];
    if (canon) return lim;
    const base = nameExprAltsBase(node, opts);

    return uniq([...lim.slice(0, 30), ...base.slice(0, 200), ...lim, ...base]);
  }
  if ((c === "LeanNorm" || c === "LeanAbs") && cls(unwrapParen(args[0])) === "LeanSub") {
    const sub = unwrapParen(args[0]);
    const l = nameExpr(sub.args?.[0], opts);
    const r = nameExpr(sub.args?.[1], opts);
    const pre = c === "LeanNorm" ? "Norm" : "Abs";
    if (l && l === r && !l.includes("/")) return uniq([pre + "Sub" + l, pre + "Sub" + l.replace(/_/g, ""), pre + "Sub"]);
  }
  if (c === "LeanArgsSpaceSeparated" && args.length >= 2) {
    const head = args[0];
    const k = args.findIndex((a, i) => i > 0 && cls(a) === "LeanToken" && a.text === "''");
    if (k > 0 && k < args.length - 1) {
      const S = A(appSlice(node, args.slice(k + 1)));
      const F = A(appSlice(node, args.slice(0, k))).filter((f) => f !== "Fun");
      const out = S.map((s) => "Image" + s);
      if (!canon) for (const f of F) for (const s of S) out.push("Image" + f + s, "Image" + f + "_" + s);
      if (!canon) for (const s of S) out.push("Image_" + s);
      return out.length ? uniq(out) : ["Image"];
    }
    if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝔼" && args.length === 2) {
      const body = expectCondBody(args[1]);
      if (body) {
        const x = A(body);
        const cond = x.length ? x.map((y) => EXPECT_COND + y) : [EXPECT_COND];
        return canon ? cond.slice(0, 1) : uniq([...cond.slice(0, 2), EXPECT_COND, "Expect", ...cond]);
      }
      const b = A(args[1]);
      const fuseExpect = (y) => y === "Mul" ? ["Expect_Mul"] : ["Expect" + y];
      return b.length ? uniq(b.flatMap(fuseExpect)) : ["Expect"];
    }
    if (cls(head) === "LeanGetElem" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text === "𝕍𝕒𝕣" && args.length === 2) {
      const b = A(args[1]);
      return b.length ? uniq(b.map((y) => "Var" + y)) : ["Var"];
    }
    if (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" && /^(real|toReal)$/.test(head.args[1].text || "") && args.length === 2 && isSetBuilder(args[1])) {
      const p = setCondNames(args[1], opts, canon);
      const out = p.map((x) => "Real" + x);
      if (!canon) out.push(...p.map((x) => "RealSetOf" + x), "Real");
      return uniq(out.length ? out : ["Real"]);
    }
    if (KEEP_GREEK && EMBED_HEADS.has(qualHeadText(head)) && args.slice(1).every((a) => { const u = unwrapParen(a); return cls(u) === "LeanToken" && (isLeafName(u.text, opts.leaves) || /^\d+$/.test(u.text || "")); }) && args.slice(1).some((a) => isLeafName(unwrapParen(a).text, opts.leaves))) {
      return [];
    }
  }
  if (c === "Lean_Expect") {
    const T = node.pathToken;
    const body = expectCondBody(node.scope);
    if (body) {
      const x = A(body);
      const cond = x.length ? x.map((y) => EXPECT_COND + y) : [EXPECT_COND];
      return canon ? cond.slice(0, 1) : uniq([...cond.slice(0, 2), EXPECT_COND, T, ...cond]);
    }
    const b = A(node.scope);
    const fuseExpect = (y) => y === "Mul" ? [T + "_Mul"] : [T + "_" + y];
    return b.length ? uniq(b.flatMap(fuseExpect)) : [T + "__"];
  }
  if (c === "Lean_Var") {
    const T = node.pathToken;
    const b = A(node.scope);
    return b.length ? uniq(b.map((y) => T + "_" + y)) : [T + "__"];
  }
  if (c === "Lean_Prob") {
    const T = node.pathToken;
    const probName = nameProbApp(node);
    if (probName) {
      const ev = matchProbApp(node);
      return canon
        ? [probName === "ProbS" && ev && isProbJointEvent(ev) ? "ProbJoint" : probName]
        : uniq([probName === "ProbS" && ev && isProbJointEvent(ev) ? "ProbJoint" : probName, T]);
    }
    return [T];
  }

  {
    const lim = limitsBigOpBoundScope(node);
    if (lim) {
      const tok = lim.pathToken;
      if (tok === "ArgMax" || tok === "ArgMin") return [tok];
      const b = A(lim.scope);
      if (!b.length) return [tok];
      return uniq(b.map((y) => limitsBigOpFuseName(tok, y)));
    }
  }

  if (c === "Lean_partial" || c === "LeanPartial") {
    if (!partialPathAtom(node)) return [];
    return partialNameAltsFromScope(node, opts, A);
  }
  if (c === "LeanParenthesis" && cls(args[0]) === "LeanAssign") return [];
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
      const x = A(cx);
      return x.length ? uniq(x.flatMap((y) => ["CondExp" + y, "CondExp_" + y])) : ["CondExp"];
    }
    const t = normHead(node, opts);
    if (t !== node) return [nameToken(t.text)].filter(Boolean);
  }
  if (c === "Lean_int") {
    const T = node.pathToken;
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
    const asExpect = (xs) => {
      if (canon || opts.section !== "Random") return xs;
      const expectOf = (rest) => rest === "Mul" ? "Expect_Mul" : "Expect" + rest;
      const extra = [];
      for (const x of xs) {
        if (x.startsWith(T + "_")) extra.push(expectOf(x.slice((T + "_").length)));
        else if (x.startsWith(T)) extra.push(expectOf(x.slice(T.length)));
      }
      return uniq([...xs, ...extra]);
    };
    if (b.length) return asExpect(uniq(b.flatMap((y) => [T + "_" + y, T + y])));
    const part = cls(body) === "LeanArgsSpaceSeparated" ? (body.args || []).find((x) => cls(x) === "Lean_partial" || cls(x) === "LeanPartial") : null;
    const m = !canon && part ? A(part.args?.[0]) : [];
    return asExpect(uniq([T, ...m.map((y) => T + y)]));
  }
  if (c === "Lean_prod") {
    const T = node.pathToken;
    const b = A(args[args.length - 1]);
    return b.length ? uniq(b.flatMap((y) => [T + "_" + y, T + y])) : [T];
  }
  return null;
}

function postAlts(node, opts, alts, canon) {
  const c = cls(node);
  const args = node.args || [];
  const A = (n) => (canon ? [nameExpr(n, opts)].filter(Boolean) : nameExprAlts(n, opts));
  const domainAtom = bigOpDomainAtom(node);
  if (domainAtom) {
    const arityRange = sumRangeArityName(node, opts);
    if (arityRange) alts = uniq([arityRange, ...alts]);
    const sname = sumDomainName(node);
    if (sname) {
      const tag = domainAtom + sname;
      const b = A(args[args.length - 1]);
      const extra = b.length ? b.flatMap((y) => [tag + "_" + y, tag + y]) : [tag];
      const preferDom = isSumIntervalDom(sname);
      alts = preferDom
        ? uniq(extra.flatMap((e, i) => (i < alts.length ? [e, alts[i]] : [e])).concat(alts.slice(extra.length)))
        : uniq([...alts, ...(canon ? [] : extra)]);
    }
    if (!canon && alts.length) alts = uniq([alts[0], domainAtom, ...alts.slice(1)]);
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
    for (const l of L) if (l) extra.push("SMul" + l);
    for (const r of R) if (r) extra.push("SMul_" + r);
    return uniq([...alts, ...extra]);
  }
  return alts;
}

const NODE_ALT_CAP = 1000;
function stripIndepWrap(n) {
  let u = unwrapParen(n);
  while ((cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") && (u.args || []).filter((a) => cls(a) !== "LeanLineComment").length === 1) {
    u = unwrapParen((u.args || []).find((a) => cls(a) !== "LeanLineComment"));
  }
  return u;
}
function indepAtom(node) {
  const u = stripIndepWrap(node);
  if (cls(u) === "Lean_perp") return u.pathToken;
  if (cls(u) === "LeanBitOr" && cls(stripIndepWrap(u.args?.[0])) === "Lean_perp") return "CondIndep";
  return "";
}
function indepCanon(node, opts = {}) {
  const joint = indepJointAlt(node);
  if (joint) return joint;
  const u = stripIndepWrap(node);
  if (cls(u) === "Lean_perp") {
    const T = u.pathToken;
    const isSlice = (n) => {
      const x = unwrapParen(n);
      return cls(x) === "LeanGetElem" && cls(x.args?.[1]) === "LeanColon";
    };
    const L = isSlice(u.args?.[0]);
    const R = isSlice(u.args?.[1]);
    if (opts.multiGiven && R && !L) return T;
    if (typeof u.pathChoices === "function") {
      const ch = (u.pathChoices(opts) || []).filter(Boolean);
      if (ch.length) return ch[0];
    }
    if (L && R) return T + "GetSlice_GetSlice";
    if (R) return T + "_GetSlice";
    if (L) return T + "GetSlice";
    return T;
  }
  if (cls(u) === "LeanBitOr" && cls(stripIndepWrap(u.args?.[0])) === "Lean_perp") return "CondIndep";
  return "";
}
function indepAlts(node, opts = {}) {
  const joint = indepJointAlt(node);
  const u = stripIndepWrap(node);
  if (cls(u) === "Lean_perp") {
    let ch = typeof u.pathChoices === "function"
      ? [...new Set((u.pathChoices(opts) || []).filter(Boolean))]
      : [];
    if (!ch.length) {
      const c = indepCanon(node, opts);
      if (c) ch = [c];
    }
    if (joint && !ch.includes(joint)) ch = [joint, ...ch];
    if (!ch.includes(u.pathToken)) ch.push(u.pathToken);
    return ch;
  }
  if (cls(u) === "LeanBitOr" && cls(stripIndepWrap(u.args?.[0])) === "Lean_perp") {
    return joint && joint !== "CondIndep" ? [joint, "CondIndep"] : ["CondIndep"];
  }
  return [];
}

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

function distributedLawName(rhs, opts) {
  let u = unwrapParen(rhs);
  if (cls(u) === "LeanArgsSpaceSeparated") u = unwrapParen(u.args?.[0]);
  if (cls(u) === "LeanToken") {
    const raw = u.text || "";
    if (raw === "𝒩" || raw === "gaussian" || raw === "gaussianReal" || raw === "GaussianReal" || raw === "Gaussian")
      return "Gaussian";
    const n = nameToken(raw);
    if (n === "gaussian" || n === "Gaussian" || n === "GaussianReal") return "Gaussian";
    return n;
  }
  const n = nameExpr(rhs, opts);
  if (!n) return "";
  if (n === "gaussian" || n === "Gaussian" || n === "GaussianReal" || /^gaussian/i.test(n)) return "Gaussian";
  return n;
}
function distributedCanon(node, opts = {}) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanDistributed") return "";
  const args = u.args || [];
  const left = nameExpr(args[0], opts);
  const law = distributedLawName(args[1], opts);
  if (opts.asGiven) {
    if (law === "Gaussian") return "Distributed_Gaussian";
    if (law) return "Distributed_" + law;
    return "Distributed";
  }
  if (left === "Add") return "DistributedAdd";
  if (left) return "Distributed" + left;
  if (law === "Gaussian") return "Distributed";
  if (law) return "Distributed_" + law;
  return "Distributed";
}
function distributedAlts(node, opts = {}) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanDistributed") return [];
  const args = u.args || [];
  const left = nameExpr(args[0], opts);
  const law = distributedLawName(args[1], opts);
  const out = [];
  if (opts.asGiven) {
    if (law === "Gaussian") {
      out.push("Distributed_Gaussian", "Distributed");
    } else if (law) {
      out.push("Distributed_" + law, "Distributed");
    } else {
      out.push("Distributed");
    }
    return uniq(out.filter(Boolean));
  }
  if (left === "Add") {
    out.push("DistributedAdd", "Distributed");
    if (law === "Gaussian") out.push("DistributedAdd_Gaussian");
  } else if (left) {
    out.push("Distributed" + left, "Distributed");
  } else {
    out.push("Distributed");
  }
  if (law && law !== "Gaussian") out.push("Distributed_" + law);
  return uniq(out.filter(Boolean));
}

function demoteExpectSnake(name) {
  if (!name) return name;
  if (name.startsWith("Expect_") && !/^Expect_(Mul|Div|SMul)/.test(name))
    name = "Expect" + name.slice("Expect_".length);
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

function unwrapAngle(node) {
  let n = node;
  while (n) {
    if (cls(n) === "LeanParenthesis") { n = n.args?.[0]; continue; }
    if (cls(n) === "LeanAngleBracket" && (n.args || []).length === 1) { n = n.args[0]; continue; }
    break;
  }
  return n;
}

function isBareFunNode(node) {
  return cls(unwrapAngle(node)) === "Lean_fun";
}

function isSfBvarText(text) {
  return /^\\sf\{\w\}$/.test(text || "") || /^«\\sf\{\w\}»$/.test(text || "");
}
function isBvarQuotation(node) {
  if (!node || typeof node !== "object") return false;
  if (cls(node) === "LeanDoubleAngleQuotation") {
    const inner = node.args?.[0];
    if (cls(inner) === "LeanProperty" && cls(inner.args?.[1]) === "LeanToken" && inner.args[1].text === "bvar") {
      return true;
    }
    if (cls(inner) === "LeanToken" && isSfBvarText(inner.text)) return true;
    return isBvarQuotation(inner);
  }
  return false;
}

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
  if (n === "LeanBitOr") return false;

  if (Array.isArray(node.args)) return node.args.some(eventHasAnd);
  return false;
}

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

function commaParts(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanArgsCommaSeparated" && (u.args || []).length >= 2) return u.args;
  return null;
}

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

function isRvTerm(node) {
  const u = unwrapParen(node);
  if (!u) return false;
  if (commaParts(u) || jrsParts(u)) return isJointRvTuple(u);
  const c = cls(u);
  if (c === "LeanToken") return RV_NAMES.has(u.text);
  if (c === "LeanGetElem") return isRvTerm(u.args?.[0]);

  if (c === "LeanArgsSpaceSeparated") {
    const h = u.args?.[0];
    if (cls(h) === "LeanToken") return RV_NAMES.has(h.text);
    if (cls(h) === "LeanGetElem") return isRvTerm(h);
    return false;
  }
  return false;
}

function isJointRvTuple(node) {
  const parts = commaParts(node) || jrsParts(node);
  if (!parts || parts.length < 2) return false;
  if (parts.every((p) => isRvTerm(p))) return true;
  return parts.every((p) => isRvTerm(p) || isSingleVarSide(p));
}

function isMeasurableJointArg(node) {
  const parts = commaParts(node) || jrsParts(node);
  if (!parts || parts.length < 2) return false;
  if (parts.every((p) => isRvTerm(p))) return true;
  return parts.every((p) => isRvTerm(p) || isSingleVarSide(p));
}

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

function isCdotSection(node) {
  const u = unwrapParen(node);
  if (cls(u) === "LeanToken") return u.text === "·";
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken") return u.args[0].text === "·";
  return false;
}

function isSingleVarSide(node) {
  const u = unwrapParen(node);
  if (!u || isCdotSection(u) || commaParts(u) || jrsParts(u)) return false;
  const ident = (t) => typeof t === "string" && t !== "·" && !/^-?\d+$/.test(t) && (/^[A-Za-z_]/.test(t) || /^[^\x00-\x7F]/.test(t));
  if (cls(u) === "LeanToken") return ident(u.text);
  if (cls(u) === "LeanGetElem") return isSingleVarSide(u.args?.[0]);
  if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanToken") return ident(u.args[0].text);
  return false;
}

function eqJointSides(node) {
  const u = unwrapParen(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return false;
  const [a, b] = u.args;
  const other = (n) => isCdotSection(n) || isSingleVarSide(n);
  return (isJointRvTuple(a) && other(b)) || (isJointRvTuple(b) && other(a));
}

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
  if (cls(u) === "Lean_perp") { perp = u; base = u.pathToken; }
  else if (cls(u) === "LeanBitOr" && cls(strip(u.args?.[0])) === "Lean_perp") {
    perp = strip(u.args[0]); cond = u.args?.[1]; base = "CondIndep";
  } else return "";
  const left = isJointRvTuple(perp.args?.[0]);
  const right = isJointRvTuple(perp.args?.[1]);
  const cj = !!(cond && isJointRvTuple(cond));
  if (!left && !right && !cj) return "";
  let name = base;
  if (left) name += "Joint";
  if (right || cj) name += "_Joint";
  return name;
}

function probEventName(event, tuples) {
  const joint = (n) => eventHasAnd(n) || (tuples && isJointRvTuple(n));
  const e = unwrapParen(event);
  if (cls(e) === "LeanBitOr") {
    const left = unwrapParen(e.args?.[0]);
    const right = unwrapParen(e.args?.[1]);
    const leftAnd = joint(left);
    const rightAnd = joint(right);
    if (leftAnd && !rightAnd) return PROB_COND + "Joint";
    if (rightAnd && !leftAnd) return PROB_COND + "_Joint";
    if (leftAnd && rightAnd) return PROB_COND + "Joint_Joint";
    return PROB_COND;
  }
  if (joint(e)) return "ProbS";
  return "Prob";
}

function divProbEventName(ln, rn) {
  if (!ln.startsWith("Prob") || !rn.startsWith("Prob")) return "";
  const joint = (n) => n === "ProbS" || new RegExp("^" + PROB_COND + "_?Joint(_Joint)?$").test(n);
  const cond = (n) => n === PROB_COND || new RegExp("^" + PROB_COND + "_?Joint$").test(n);
  if ((joint(ln) && cond(rn)) || (joint(ln) && joint(rn))) return "DivProbSCond";
  if (joint(ln) && rn === "Prob") return "DivProbS";
  return "Div" + ln + rn;
}

function matchProbApp(node) {
  const bs = expectProbVarBoundScope(node);
  if (bs?.kind === "Lean_Prob") {
    const sc = bs.scope;
    if (!sc) return null;
    if (cls(sc) === "LeanParenthesis" || cls(sc) === "LeanBrace") return unwrapParen(sc);
    return unwrapParen(sc);
  }
  const n = unwrapParen(node);
  if (cls(n) !== "LeanArgsSpaceSeparated") return null;
  const head = n.args?.[0];
  if (cls(head) !== "LeanGetElem") return null;
  if (cls(head.args?.[0]) !== "LeanToken" || head.args[0].text !== "ℙ") return null;
  for (let i = 1; i < (n.args || []).length; i++) {
    const a = n.args[i];
    if (cls(a) === "LeanParenthesis" || cls(a) === "LeanBrace") return unwrapParen(a);
  }
  return null;
}

function nameProbEvent(event) {
  return probEventName(event, false);
}

function nameProbApp(node) {
  const event = matchProbApp(node);
  if (!event) return "";
  return nameProbEvent(event);
}

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
    return isSlice(l) && isSlice(r) && isBvarQuotation(bvarHead(r.args[0]));
  });
}
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
function isProbJointEvent(event) {
  return isBvarSliceJointEvent(event) || isBvarPointSliceJointEvent(event);
}
function neProbJoint0GivenName(typeNode) {
  let u = unwrapParen(typeNode);
  while (cls(u) === "LeanArgsNewLineSeparated" || cls(u) === "LeanStatements") {
    const kids = (u.args || []).filter((a) => cls(a) !== "LeanLineComment");
    u = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  if (cls(u) === "Lean_forall") return "";

  if (cls(u) !== "Lean_ne" && cls(u) !== "LeanNe") return "";
  const right = unwrapParen(u.args?.[1]);
  if (cls(right) !== "LeanToken" || right.text !== "0") return "";
  let left = unwrapParen(u.args?.[0]);
  if (cls(left) === "LeanColon") left = unwrapParen(left.args[0]);
  const ev = matchProbApp(left);
  return ev && nameProbEvent(ev) === "ProbS" && isBvarPointSliceJointEvent(ev) ? "NeProbJoint__0" : "";
}

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
  if (cls(steps) !== "Lean_forall" || hasBvarBinder(steps)) return false;
  const imp = strip(steps.args[steps.args.length - 1]);
  if (cls(imp) !== "Lean_rightarrow" || cls(strip(imp.args?.[0])) !== "Lean_lt") return false;
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
    if (ev) { cond = nameProbEvent(ev) === PROB_COND; return; }
    for (const a of n.args || []) walk(a);
  })(lg.args[0]);
  return cond;
}
function hmmBvarAllAlts(alts) {
  const out = [];
  for (const b of alts) {
    out.push("All_" + b);
    const bare = b.replace(/Prob(?:JointGetSliceS|Joint|S)(?![A-Za-z])/g, "Prob");

    if (bare !== b) out.push("All_" + bare);
  }
  const have = new Set(alts);
  return uniq(out.filter((x) => !have.has(x)));
}

function bvarAllLt0ProbJointName(typeNode) {
  const u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall" || u.superscript === "ᵐ" || !hasBvarBinder(u)) return "";
  let body = unwrapParen(u.args[u.args.length - 1]);
  while (cls(body) === "LeanArgsNewLineSeparated" || cls(body) === "LeanStatements") {
    const kids = (body.args || []).filter((a) => cls(a) !== "LeanLineComment");
    body = unwrapParen(kids[kids.length - 1] || kids[0]);
  }
  const kind = cls(body);
  if ((kind !== "Lean_lt" && kind !== "Lean_gt") || (body.args || []).length !== 2) return "";
  const left = unwrapParen(body.args[0]);
  const right = unwrapParen(body.args[1]);
  const isZero = (n) => cls(n) !== "LeanToken" ? false : n.text === "0";
  let probSide = null;
  if (kind === "Lean_lt" && isZero(left)) probSide = right;
  else if (kind === "Lean_gt" && isZero(right)) probSide = left;
  else return "";
  if (cls(probSide) === "LeanColon") probSide = unwrapParen(probSide.args[0]);

  const ev = matchProbApp(probSide);
  return ev && nameProbEvent(ev) === "ProbS" && isBvarSliceJointEvent(ev) ? "All_Lt0ProbJoint" : "";
}

function isIllegalGtProbJointAtom(name) {
  return /^(GtProbJoint0|GtProbJoint_0|GtProbJoint__0|All_GtProbJoint0|All_GtProbJoint_0)$/.test(name || "");
}
function isIllegalTripleUnderscoreAtom(name) {
  return /___/.test(name || "");
}
function isIllegalNeProbJointAtom(name) {
  return /^(NeProbJoint0|NeProbJoint_0)$/.test(name || "");
}

function allNeProb0GivenName(typeNode) {
  let u = unwrapParen(typeNode);
  if (cls(u) !== "Lean_forall") return "";
  let body = unwrapParen(u.args[u.args.length - 1]);
  while (cls(body) === "Lean_forall") body = unwrapParen(body.args[body.args.length - 1]);
  while (cls(body) === "Lean_rightarrow") body = unwrapParen(body.args[body.args.length - 1]);
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
function maxBvarOperands(node) {
  const n = unwrapParen(node);
  const lim = limitsBigOpBoundScope(n);
  if (lim?.kind === "Lean_max") {
    const bind = lim.bound;
    if (cls(bind) !== "LeanColon" || !isBvarQuotation(bind.args?.[0])) return null;
    const sc = unwrapParen(lim.scope);
    if (cls(sc) === "LeanArgsSpaceSeparated") return sc.args.slice();
    return lim.scope != null ? [lim.scope] : [];
  }
  if (cls(n) !== "LeanArgsSpaceSeparated") return null;
  const head = n.args?.[0];
  if (cls(head) !== "LeanGetElem" || cls(head.args?.[0]) !== "LeanToken" || head.args[0].text !== "max") return null;
  const bind = head.args?.[1];
  if (cls(bind) !== "LeanColon" || !isBvarQuotation(bind.args?.[0])) return null;
  return n.args.slice(1);
}
function isBvarProbJoint(node, log = false) {
  let u = unwrapParen(node);
  if (log) {
    if (cls(u) !== "LeanProperty" || cls(u.args?.[1]) !== "LeanToken" || u.args[1].text !== "log") return false;
    u = u.args[0];
  }
  const ev = matchProbApp(unwrapAscribed(u));
  return !!ev && nameProbEvent(ev) === "ProbS" && isBvarJointEvent(ev);
}
function isMaxProbJointEq(node) {
  const u = stripStmt(node);
  if (cls(u) !== "LeanEq" || (u.args || []).length !== 2) return false;
  const ops = maxBvarOperands(u.args[0]);
  return !!ops && ops.length === 1 && isBvarProbJoint(ops[0]);
}
function fixMaxProbJointName(a) {
  return String(a)
    .replace(/(^|\/)GetMax(?=\/|$)/g, "$1EqMax_ProbJoint")
    .replace(/EqGetMax/g, "EqMax_ProbJoint")
    .replace(/GetMax/g, "Max_ProbJoint");
}
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
    if (isBvarQuotation(n)) foundBvar = true;
    if (c === "LeanToken" && (n.text === "ReferenceMeasure" || n.text === "measure")) foundPartial = true;
    if (Array.isArray(n.args)) for (const a of n.args) walk(a);
  };
  walk(head);
  return foundPartial || foundBvar;
}

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

function quantBinderNames(head, out = new Set()) {
  const c = cls(head);
  if (c === "LeanToken") { if (head.text && head.text !== "_") out.add(head.text); }
  else if (c === "LeanColon" || c === "LeanBitOr" || GUARD_REL.has(c)) quantBinderNames(head.args?.[0], out);
  else if (c === "LeanParenthesis" || c === "LeanArgsSpaceSeparated") for (const a of head.args || []) quantBinderNames(a, out);
  return out;
}

function quantArity(node) {
  return quantBinderNames(node.args?.[0]).size;
}

function mentionsAny(node, names) {
  if (!node || typeof node !== "object") return false;
  if (cls(node) === "LeanToken") return names.has(node.text);
  return (node.args || []).some((a) => mentionsAny(a, names));
}

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
  if (!flattenRight) return [...(leftParts || [left]), right];
  const rightParts = splitTopConjunction(right, flattenRight);
  return [...(leftParts || [left]), ...(rightParts || [right])];
}

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

function isEqConjunct(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  return cls(n) === "LeanEq";
}

function isFinishedPathConjunct(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n) return false;
  if (cls(n) === "LeanEq") return true;
  if (cls(n) === "LeanProperty" && cls(n.args?.[1]) === "LeanToken") {
    const t = n.args[1].text || "";
    return /^Is[A-Z]/.test(t) || /^Has[A-Z]/.test(t);
  }
  if (cls(n) === "LeanArgsSpaceSeparated") {
    const head = n.args?.[0];
    const tok = cls(head) === "LeanToken" ? head
      : (cls(head) === "LeanProperty" && cls(head.args?.[1]) === "LeanToken" ? head.args[1] : null);
    const t = tok?.text || "";
    return /^Is[A-Z]/.test(t) || /^Has[A-Z]/.test(t);
  }
  return false;
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

function isCoeAscription(node) {
  return cls(node) === "LeanColon" && hasNode(node.args?.[1], (n) => cls(n) === "LeanToken" && n.text === "ℝ*");
}

function nameExprBase(node, opts = {}) {
  if (!node) return "";
  const name = cls(node);
  if (isSupLtInfty(node) || isBddAboveSup(node)) return supBoundCanon(node);
  if (isCoeAscription(node)) return "Coe" + nameExpr(node.args[0], opts);

  if (name === "Lean_have" || name === "Lean_let") return "";
  if (isBvarQuotation(node)) return "";
  if (name === "LeanVecNotation") return "";
  if (name === "Lean_nabla" || name === "LeanNabla") {
    const gb = gradientBody(node);
    if (gb) {
      const y = nameExpr(gb, opts);
      if (!y) return "Grad";
      if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
        return "Grad" + y;
      }
      return joinHeadChild("Grad", y);
    }
    const alts = nablaGradAlts(node, opts);
    return alts[0] || "Grad";
  }
  {
    const gb = gradientBody(node);
    if (gb) {
      const y = nameExpr(gb, opts);
      if (!y) return "Grad";
      if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
        return "Grad" + y;
      }
      return joinHeadChild("Grad", y);
    }
  }

  if (indepAtom(node)) return indepCanon(node, opts);

  {
    const d = distributedCanon(node, opts);
    if (d) return d;
  }

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

  if (name === "Lean_partial" || name === "LeanPartial") {
    return partialNameFromScope(node, opts);
  }

  if (CLASS_TOKEN[name]) {
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanInv", "LeanMatMul"]);
    if (!ARITH.has(name)) {
    const tag = CLASS_TOKEN[name];
    const args = node.args || [];
    if (name === "Lean_exists" && node.unique) {
      const core = nameExpr(existsRestConjunct(node) || args[args.length - 1], opts);
      return core ? core + "/Unique" : "Unique";
    }
    if (name === "Lean_exists" || name === "Lean_forall") {
      if (name === "Lean_exists" && isHoleAndTree(args[args.length - 1], opts)) {
        const andName = nameExpr(args[args.length - 1], opts);
        if (andName) return tag + "_" + andName;
      }
      const bodyNode = name === "Lean_forall" ? peelGuardForalls(args[args.length - 1]) : args[args.length - 1];
      const body = nameExpr(bodyNode, opts);
      if (!body) return tag;
      {
        const eqAtom = quantWrapEqBody(tag, body);
        if (eqAtom) return eqAtom;
      }
      if (isAeQuantifier(node) && !isMixedBvarForall(node) && node.superscript === "ᵐ") {
        const eqAtom = aeEqAtom(body);
        if (eqAtom) return eqAtom;
        return "Ae" + body;
      }
      if (isAeQuantifier(node) && !isMixedBvarForall(node)) return body;
      const rest = existsRestConjunct(node);
      const multi = "";

      if (guardRestConjunct(args[args.length - 1]) && name === "Lean_exists") { const g = nameExpr(args[args.length - 1], { ...opts, asGiven: true }); if (g && !g.includes("/")) return tag + "_" + g; }
      if (rest) {
        const restName = nameExpr(rest, opts);
        if (restName) return tag + "_And_" + restName;
      }
      if (!body.includes("/") && /^Eq/.test(body)) return multi + tag + "_" + body;

      if (name === "Lean_forall" && !body.includes("/")) {
        const imp = unwrapParen(args[args.length - 1]);
        const prem = cls(imp) === "Lean_rightarrow" ? unwrapParen(imp.args?.[0]) : null;
        const bound = new Set();
        quantBinderNames(args[0], bound);
        if (prem && ["Lean_le", "Lean_lt", "Lean_ge", "Lean_gt"].includes(cls(prem)) && (prem.args || []).length === 2) {
          const [a, b] = prem.args.map(unwrapParen);
          const isB = (x) => cls(x) === "LeanToken" && bound.has(x.text);
          const other = isB(a) && !isB(b) ? b : isB(b) && !isB(a) ? a : null;
          if (other && !isConstNode(other) && cls(other) !== "LeanToken" && nameExpr(other, opts)) {
            if (body.startsWith("Imp")) return tag + "_" + body;
            return tag + "_Imp_" + body;
          }
        }
      }
      if (hasQuantEqSlash(body)) return tag;
      if (body.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(body)) return body;
      if ((name === "Lean_exists" || name === "Lean_forall") && (body === tag || body.startsWith(tag + "_"))) return body;
      return multi + tag + "_" + body;
    }
    if (name === "Lean_lnot") {
      const body = nameExpr(args[args.length - 1], opts);
      return body ? "Not" + body : "Not";
    }
    if (name === "Lean_land" || name === "Lean_lor") {
      const join = name === "Lean_lor" ? "Or" : "And";
      const leftHole = isAtomicHoleAndConjunct(args[0], opts);
      const rightHole = isAtomicHoleAndConjunct(args[1], opts);
      const left = leftHole
        ? (fillHoleAndConjunct(args[0], opts) || "")
        : nameExpr(args[0], opts);
      const right = rightHole
        ? (fillHoleAndConjunct(args[1], opts) || "")
        : nameExpr(args[1], opts);
      if (!leftHole && !rightHole && left && right) return left + "/" + right;
      return nameAndOr(join, left, right);
    }
    return relationCanon(node, tag, opts);
    }

  }

  if (name === "Lean_sum") {
    const arityRange = sumRangeArityName(node, opts);
    if (arityRange) return arityRange;
    const dom = sumDomainName(node);
    const keepDom = dom && isSumIntervalDom(dom);
    const tag = (node.superscript === "'" ? "TSum" : "Sum") + (keepDom ? dom : "");
    const args = node.args || [];
    const body = nameExpr(args[args.length - 1], opts);
    if (body && /^Sum_Square/.test(body)) return tag + "_" + body.replace(/^Sum_/, "");
    return body ? tag + "_" + body : tag;
  }
  if (name === "LeanStack") {
    const scope = peelEntryStmt(node.scope ?? node.args?.[1]);
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
    if (cls(unwrapParen(arg)) === "LeanSub") return wrapPrefix + "Sub";
    const leafHead = cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken" && isLeafName(arg.args[0].text, opts.leaves) && cls(unwrapParen(arg.args?.[1])) !== "LeanSub";
    if (leafHead) return wrapPrefix;

    if (cls(arg) === "LeanArgsSpaceSeparated" && (cls(arg.args?.[0]) === "LeanToken" || cls(arg.args?.[0]) === "LeanProperty")) {
      const headNode = arg.args[0];
      const camelFn = cls(headNode) === "LeanToken" ? nameToken(headNode.text) : nameExpr(headNode, opts);
      const inner = unwrapParen(arg.args?.[1]);
      if (cls(inner) === "LeanSub") return wrapPrefix + camelFn + nameExpr(inner, opts);
      return wrapPrefix + camelFn;
    }
    const inner = nameExpr(arg, opts);
    if (!inner) return wrapPrefix;
    const u = unwrapParen(arg);
    if (CLASS_TOKEN[cls(u)] || isSimpleArg(arg, opts)) return wrapPrefix + inner;
    return wrapPrefix + "_" + inner;
  }

  {
    const decor = { LeanAdjoint: "Adjoint", LeanTranspose: "T", LeanConj: "Conj", LeanInv: "Inv" }[name];
    if (decor) {
      if (isQuantBinderHole(node.args?.[0], opts)) return opts?.keepDecorOnBinder ? decor : "";
      const inner = nameExpr(node.args?.[0], opts);
      return inner ? decor + inner : decor;
    }
  }

if (name === "LeanToken") {
    const raw = node.text || "";
    if (isLeafName(raw, opts.leaves)) return "";

    if (/^-?\d+$/.test(raw)) return raw;

    return nameToken(raw);
  }

  if (name === "LeanConstruct") {
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
    const obj = node.args?.[0];
    const prop = node.args?.[1];
    const propName = cls(prop) === "LeanToken" ? nameToken(prop.text || "") || nameExpr(prop, opts) : nameExpr(prop, opts);
    if (isBinderMeasureProj(node, opts)) return "";
    if (cls(obj) === "LeanToken" || isModulePathReceiver(obj)) return propName || "";
    const objName = nameExpr(obj, opts);
    if (objName && propName) return propName + objName;
    return propName || objName || "";
  }
  if (name === "LeanParenthesis" || name === "LeanAngleBracket") return nameExpr(node.args?.[0], opts);
  if (name === "Lean_fun" || name === "LeanRightarrow" || name === "Lean_rightarrow") {
    const body = node.args?.[node.args.length - 1];
    const bodyName = nameExpr(body, opts);
    if (name === "LeanRightarrow") return bodyName;
    if (name === "Lean_rightarrow") {
      const ante = node.args?.[0];
      if (isPropHyp(ante) || isPropHyp(body)) {
        const left = nameExpr(ante, opts) || "";
        const right = bodyName || "";
        if (!left && !right) return "Imp__";
        if (!left && right) return "Imp_" + right;
        if (left && !right) return "Imp" + left;
        if (left && right && left === right && (left === "Eq" || left.startsWith("Eq")))
          return "Imp" + ("EqS" + left.slice(2));
        return "Imp" + left + right;
      }
      return bodyName;
    }
    return bodyName || "Fun";
  }
  if (name === "LeanArgsSpaceSeparated") {
    const args = node.args || [];
    const mj = measurableJointName(node);
    if (mj) return mj;

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
      const hn = cls(head) === "LeanToken" && !isLeafName(head.text, opts.leaves) ? nameToken(head.text) : "";
      return hn ? hn + "_Sub" : "UFnSub";
    }
    {
      if (isArgMaxMinApp(node)) return argMaxMinTokenName(node);
      const am = argMaxMinTokenName(args[0]);
      if (am && isArgMaxMinGetElem(args[0])) return am;
    }
    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headName = nameExpr(head, opts);
      if (headName) {
        let pref = applyEvalPrefix(head);
        if (pref === "Get" && headName.startsWith("Get")) pref = "";
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
      if (method && argNames.length === 1) {
        const arg = argNames[0];
        const argNode = args.slice(1).find((a) => nameExpr(a, opts) === arg);
        const u = unwrapParen(argNode);
        if (arg === "Fun") return method + arg;
        if (arg.startsWith("Fun")) return method + "_" + arg;
        if (cls(u) === "LeanArgsSpaceSeparated" && cls(u.args?.[0]) === "LeanProperty") return method + "_" + arg;
        if (cls(u) === "Lean_fun") return funBodyUnary(u) ? method + arg : method + "_" + arg;
        return method + arg;
      }
      if (method && argNames.length === 0) return method;
      if (method && argNames.length > 1) return joinHeadArgs(method, argNames);
    }
    if (cls(head) === "LeanToken") {
      const headName = isLeafName(head.text, opts.leaves) ? "" : nameToken(head.text || "");
      let argPairs = args.slice(1).map((a) => [a, nameExpr(a, opts)]).filter(([_, n]) => n);
      if (argPairs.length > 1 || (argPairs.length === 1 && args.length > 2 && head === args[0])) argPairs = argPairs.filter(([a, n]) => !(n === "Fun" && cls(unwrapParen(a)) === "Lean_fun"));

      const argNames = argPairs.map(([_, n]) => n);
      const idxName = head !== args[0] ? nameExpr(args[0].args?.[1], opts) : "";
      if (idxName) {
        let inner = argNames.length ? joinHeadArgs(headName, argNames) : headName;
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
        if (arg === "GetSlice") return headName + arg;
        if (cls(unwrapParen(argNode)) === "Lean_fun") return funBodyUnary(argNode) ? headName + arg : headName + "_" + arg;
        if (arg.startsWith("Fun")) return headName + "_" + arg;
        if (!isSimpleArg(argNode, opts)) {
          if (ARITH_OP.has(cls(unwrapParen(argNode)))) return joinHeadChild(headName, arg);
          return headName + "_" + arg;
        }
        if (isSingleTokenName(headName) && isSingleTokenName(arg) && cls(unwrapParen(argNode)) === "LeanProperty")
          return headName + "_" + arg;
        return headName + arg;
      }
      if (headName && argNames.length === 0) {
        if (headName === "Measurable") {
          const last = unwrapParen(args[args.length - 1]);
          if (cls(last) === "LeanGetElem" && !isGetElemColonSlice(last))
            return "MeasurableGet";
        }
        return headName;
      }
      if (headName && argNames.length > 1) return joinHeadArgs(headName, argNames);
    }
    const named = args
      .map((a) => [a, nameExpr(a, opts)])
      .filter(([a, n]) => n && !(n === "Fun" && isBareFunNode(a)))
      .map(([, n]) => n);
    if (named.length === 0) return "";
    if (named.length === 1) return named[0];
    return named.join("");
  }
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ") || name === "LeanMatMul") {
    let tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
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
      const sub = subscriptedMulAtom(node);
      if (sub) {
        const right = nameExpr(args[1], opts);
        const left = nameExpr(args[0], opts);
        if (right && left) return sub + left + "_" + right;
        if (right) return sub + "_" + right;
        if (left) return sub + left;
        return sub + "__";
      }
    }
    if (name === "LeanDiv" || name === "LeanMul") {
      const lEv = matchProbApp(args[0]);
      const rEv = matchProbApp(args[1]);
      if (lEv && rEv) {
        const ln = nameProbEvent(lEv);
        const rn = nameProbEvent(rEv);
        if (name === "LeanDiv") {
          const divProb = divProbEventName(ln, rn);
          if (divProb) return divProb;
        }
        if (name === "LeanMul") {
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return "Mul" + ln + rn;
        }
      }
    }
    const left = nameExpr(args[0], opts);
    const right = nameExpr(args[1], opts);
    if (name === "LeanPow" && left && right
        && ARITH_OP.has(cls(unwrapParen(args[0]))) && ARITH_OP.has(cls(unwrapParen(args[1])))) {
      return tag + left + "__" + right;
    }
    if (left && right) {
      if (left === right) return tag + (pluralSnakeS(left) || pluralLetterS(left) || pluralMidS(left));
      return tag + joinDigits(left, right);
    }
    if (right) return ["LeanNorm", "LeanAbs"].includes(cls(unwrapParen(args[1]))) && /^(Norm|Abs)[A-Z]/.test(right) ? tag + right : snakeFocus(tag, right);
    if (left) {
      if (name === "LeanMul" && /^(?:T|Adjoint|Conj)$/.test(left)) return tag + left + "__";
      return tag + left;

    }
    if (name === "Lean_cdotp") return "Dot__";
    return tag;
  }
  if (name === "LeanDoubleAngleQuotation") {
    return "";
  }
  if (name === "LeanIte") {
    const args = node.args || [];
    const parts = cls(args[0]) === "LeanColon"
      ? [args[0].args?.[1], args[1], args[2]]
      : [args[0], args[1], args[2]];
    for (const p of parts) {
      const n = nameExpr(p, opts);
      if (n) return n;
    }
    return "";
  }
  if (name === "Lean_bullet") {
    const left = nameExpr(node.args?.[0], opts) || "";
    const right = nameExpr(node.args?.[1], opts) || "";
    if (!left && !right) return "SMul__";
    if (left && !right) return "SMul" + left;
    if (!left && right) return "SMul_" + right;
    return "SMul" + left + "_" + right;
  }
  if (name === "Lean_Expect") {
    const body = expectCondBody(node.scope);
    if (body) {
      const x = nameExpr(body, opts);
      return x ? EXPECT_COND + x : EXPECT_COND;
    }
    const b = nameExpr(node.scope, opts);
    if (!b) return "Expect__";
    return b === "Mul" ? "Expect_Mul" : "Expect_" + b;
  }
  if (name === "Lean_Var") {
    const b = nameExpr(node.scope, opts);
    return b ? "Var_" + b : "Var__";
  }
  if (name === "Lean_Prob") {
    const probName = nameProbApp(node);
    if (probName) {
      const ev = matchProbApp(node);
      return probName === "ProbS" && ev && isProbJointEvent(ev) ? "ProbJoint" : probName;
    }
    return "Prob";
  }
  {
    const lim = limitsBigOpBoundScope(node);
    if (lim) {
      const tok = lim.pathToken;
      if (tok === "ArgMax" || tok === "ArgMin") return tok;
      const b = nameExpr(lim.scope, opts);
      return limitsBigOpFuseName(tok, b);
    }
  }
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return "Prob";
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "∇") return "Grad";
    if (cls(node.args?.[0]) === "LeanToken" && (node.args[0].text === "Var" || node.args[0].text === "variance")) {
      const idx = nameExpr(node.args?.[1], opts);
      return idx ? "Var" + idx : "Var";
    }
    if (isGetElemColonSlice(node)) return "GetSlice";
    if (isBinderGetAtLiteral(node, opts)) return "";
    if (isGetIndexNoise(node.args?.[1], opts)) {
      return nameExpr(node.args?.[0], opts);
    }
    {
      const idx = nameExpr(node.args?.[1], opts);
      if (idx) return snakeFocus("Get", idx);
      const head = nameExpr(node.args?.[0], opts);
      return head || "Get";
    }
  }
  if (name === "LeanBitOr") {
    return "";
  }
  if (Array.isArray(node.args)) {
    for (const a of node.args) { const n = nameExpr(a, opts); if (n) return n; }
  }
  return "";
}

function joinHeadChild(head, child) {
  if (!child) return head;
  if (!head) return child;
  if (/\d$/.test(head) && /^\d/.test(child)) return head + "'" + child;
  if (endsInUnaryIntervalSum(head)) return head + "_" + child;
  if (child.startsWith("Fun") || child.includes("_")) {
    if (!child.startsWith("Fun") && child.includes("_")) return head + child;
    return head + "_" + child;
  }
  return head + child;
}

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

function withQuantTag(tag, body) {
  return [tag + "_" + body];
}

function legacyEqJointAlts(alts) {
  const out = [];
  for (const a of alts) {
    if (a === "Eq_Joint") out.push("EqJoint");
    if (a === "All_Eq_Joint") out.push("All_EqJoint");
  }
  return uniq(out);
}

function legacyQuantCamelAlts(alts) {
  const out = [];
  for (const a of alts) {
    const m = /^(All|Any)_(.+)$/.exec(a || "");
    if (m && m[2] && !m[2].includes("/") && !/^Eq/.test(m[2])) out.push(m[1] + m[2]);
  }
  return uniq(out);
}

function replaceCapToken(atom, from, to) {
  return String(atom || "").split("_").map((part) => {
    const toks = part.match(/[A-Z][a-z0-9]*|[0-9]+|[^A-Za-z0-9]+/g) || [part];
    return toks.map((t) => (t === from ? to : t)).join("");
  }).join("_");
}

function hasCapToken(atom, tok) {
  return String(atom || "").split("_").some((part) => {
    const toks = part.match(/[A-Z][a-z0-9]*|[0-9]+/g) || [];
    return toks.includes(tok);
  });
}

function legacyTransposeAlts(alts) {
  const out = [];
  for (const a of alts || []) {
    if (!a || !hasCapToken(a, "T")) continue;
    const leg = replaceCapToken(a, "T", "Transpose");
    if (leg && leg !== a) out.push(leg);
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
  if (name === "LeanVecNotation") return [];
    if (name === "Lean_Expect" || name === "Lean_Var" || name === "Lean_Prob") {
    const got = preAlts(node, opts, false);
    return got && got.length ? got : [];
  }
  if (LIMITS_BIGOP_KIND[name]) {
    const got = preAlts(node, opts, false);
    return got && got.length ? got : [];
  }
if (name === "Lean_partial" || name === "LeanPartial") {
    if (!partialPathAtom(node)) return [];
    return partialNameAltsFromScope(node, opts);
  }
  if (name === "Lean_nabla" || name === "LeanNabla") {
    const alts = nablaGradAlts(node, opts);
    const gb = gradientBody(node);
    if (gb) {
      const x = nameExprAlts(gb, opts);
      const ranked = [];
      for (const y of x) {
        ranked.push("Grad" + y);
        if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
          ranked.push("GradExpect_" + y.slice("Expect".length));
        }
        ranked.push("Grad_" + y);
      }
      return ranked.length ? uniq([...ranked, ...alts]) : uniq(alts.length ? alts : ["Grad"]);
    }
    return uniq(alts.length ? alts : ["Grad"]);
  }
  {
    const gb = gradientBody(node);
    if (gb) {
      const x = nameExprAlts(gb, opts);
      const ranked = [];
      for (const y of x) {
        ranked.push("Grad" + y);
        if (y.startsWith("Expect") && !y.startsWith("Expect_") && /[A-Z]/.test(y.slice(6, 7) || "")) {
          ranked.push("GradExpect_" + y.slice("Expect".length));

        }
        ranked.push("Grad_" + y);
      }
      return ranked.length ? uniq(ranked) : ["Grad"];
    }
  }

  if (indepAtom(node)) {
    return indepAlts(node, opts);
  }
  {
    const dAlts = distributedAlts(node, opts);
    if (dAlts.length) return dAlts;
  }
  {
    const mj = measurableJointName(node);
    if (mj) return uniq([mj, mj.replace(/Joint$/, "")]);

  }

  const probName = nameProbApp(node);
  if (probName) {
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
    const ARITH = new Set(["LeanSub", "LeanAdd", "LeanMul", "LeanDiv", "LeanPow", "LeanNeg", "LeanInv", "LeanMatMul"]);
    if (!ARITH.has(name)) {
      const tag = CLASS_TOKEN[name];
      const args = node.args || [];
      if (name === "Lean_exists" && node.unique) {
        const core = nameExprAlts(existsRestConjunct(node) || args[args.length - 1], opts);
        return core.length ? uniq(core.map((c) => c + "/Unique")) : ["Unique"];
      }
      if (name === "Lean_exists" || name === "Lean_forall") {
        if (name === "Lean_exists" && isHoleAndTree(args[args.length - 1], opts)) {
          const andAlts = nameExprAlts(args[args.length - 1], opts);
          if (andAlts.length) {
            const normed = andAlts.map((a) => String(a || "").replace(/_+$/, "")).filter(Boolean);
            const snakeFilled = normed.filter((a) => /^And(_[A-Z][a-z0-9]*)+$/.test(a) && !/^And(_And)*$/.test(a));
            const snakeBare = normed.filter((a) => /^And(_And)*$/.test(a));
            const snake = snakeFilled.length ? snakeFilled : snakeBare;
            const cores = snake.length ? snake : normed;
            return uniq(cores.map((a) => tag + "_" + a));
          }
        }
        const bodyNode = name === "Lean_forall" ? peelGuardForalls(args[args.length - 1]) : args[args.length - 1];
        const bodyAlts = nameExprAlts(bodyNode, opts);
        const rest = existsRestConjunct(node);
        const guardAlts = rest ? nameExprAlts(rest, opts).map((r) => tag + "_And_" + r) : [];
        const wrapQuant = (b) => ((name === "Lean_exists" || name === "Lean_forall") && (b === tag || b.startsWith(tag + "_"))) ? [b] : withQuantTag(tag, b);
        if (!bodyAlts.length) return uniq([...guardAlts, tag]);
        if (isAeQuantifier(node) && !isMixedBvarForall(node)) {
          const eqAtoms = node.superscript === "ᵐ"
            ? bodyAlts.map(aeEqAtom).filter(Boolean)
            : [];
          const aeAlts = node.superscript === "ᵐ"
            ? [...eqAtoms, ...bodyAlts.map((b) => "Ae" + b), ...bodyAlts.map((b) => quantWrapEqBody(tag, b) || (hasQuantEqSlash(b) || String(b).includes("/eq/") ? "" : tag + "_" + b)), ...bodyAlts.filter((b) => !String(b).includes("/eq/") && !hasQuantEqSlash(b)), ...guardAlts]
            : [...bodyAlts, ...guardAlts];
          return uniq(aeAlts);
        }
        if (quantArity(node) >= 2 && !node.__singleQuant) {
          node.__singleQuant = true;
          let single;
          try { single = nameExprAlts(node, opts); } finally { delete node.__singleQuant; }
          const inner = nameExprAlts(bodyNode, opts);
          const tagged = inner.filter((b) => !b.includes("/")).flatMap((b) =>
            (name === "Lean_exists" && (b === tag || b.startsWith(tag + "_"))) ? [b] : withQuantTag(tag + "_" + tag, b));
          const rel = inner.filter((b) => b.includes("/") || /^(Prob|DivProb|MulProb)/.test(b));
          return uniq([...single.slice(0, 300), ...tagged.slice(0, 300), ...single.slice(300), ...rel, ...guardAlts, ...tagged.slice(300)]);
        }
        if (bodyAlts.some(b => b.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(b))) {
          const eqT = bodyAlts.filter((b) => !b.includes("/") && /^Eq/.test(b)).flatMap((b) => withQuantTag(tag, b));
          const tagged = bodyAlts.filter((b) => !b.includes("/")).flatMap((b) => wrapQuant(b));
          const eqSlash = [];
          const relSplit = [];
          for (const b of bodyAlts) {
            if (!b.includes("/") && !String(b).includes(".eq.")) continue;
            const eqAtom = quantWrapEqBody(tag, b);
            if (eqAtom) eqSlash.push(eqAtom);
            else if (!hasQuantEqSlash(b) && !/\/eq\/|\.eq\./.test(b)) relSplit.push(b);
          }
          return uniq([...eqSlash, ...eqT, ...tagged.slice(0, 200), ...relSplit, ...guardAlts, ...tagged.slice(200)]);
        }
        const out = [];
        for (const b of bodyAlts) {
          const eqAtom = quantWrapEqBody(tag, b);
          if (eqAtom) { out.push(eqAtom); continue; }
          if (hasQuantEqSlash(b) || /\/eq\/|\.eq\./.test(b)) continue;
          out.push(...wrapQuant(b));
        }
        if (cls(unwrapParen(bodyNode)) === "Lean_rightarrow") {
          for (const b of bodyAlts) {
            if (!b || b.startsWith("Imp") || b.includes("/imp/")) continue;
            out.push(tag + "_Imp_" + b);
          }
        }
        if (name === "Lean_forall" && !rest && piPointwise(node)) out.push(...bodyAlts);
        return uniq([...guardAlts, ...out]);
      }
      if (name === "Lean_lnot") {
        const bodyAlts = nameExprAlts(args[args.length - 1], opts);
        if (!bodyAlts.length) return ["Not"];
        return bodyAlts.map(b => "Not" + b);
      }
      if (name === "Lean_land" || name === "Lean_lor") {
        const join = name === "Lean_lor" ? "Or" : "And";
        const leftHole = isAtomicHoleAndConjunct(args[0], opts);
        const rightHole = isAtomicHoleAndConjunct(args[1], opts);
        const leftAlts = leftHole
          ? (() => { const f = fillHoleAndConjunctAlts(args[0], opts); return f.length ? f : [""]; })()
          : nameExprAlts(args[0], opts);
        const rightAlts = rightHole
          ? (() => { const f = fillHoleAndConjunctAlts(args[1], opts); return f.length ? f : [""]; })()
          : nameExprAlts(args[1], opts);
        if (!leftHole && !rightHole && join === "And") {
          const namedL = leftAlts.filter(Boolean);
          const namedR = rightAlts.filter(Boolean);
          const binary = pathAndInfixChoices(
            namedL.length ? namedL : [""],
            namedR.length ? namedR : [""],
          ).stems;
          const glued = [];
          for (const l of namedL) {
            for (const r of namedR) glued.push(nameAndOr(join, l, r));
          }
          return uniq([...binary, ...glued].filter((x) => x != null && x !== ""));
        }
        const out = [];
        for (const l of leftAlts) {
          for (const r of rightAlts) {
            if (l && r && !leftHole && !rightHole) {
              out.push(l + "/" + r);
              out.push(l + "/" + (join === "And" ? "and" : "or") + "/" + r);
            }
            out.push(nameAndOr(join, l, r));
            if (l && r) out.push(l + join + "__" + r);
            if (!l && r) out.push(join + r);
            if (l && !r) out.push(l + join);
            if (!l && !r) out.push(join);
          }
        }
        return uniq(out.filter((x) => x != null && x !== ""));
      }
      return relationAlts(node, tag, opts);
    }
  }

  if (name === "Lean_sum") {
    const arityRange = sumRangeArityName(node, opts);
    const dom = sumDomainName(node);
    const keepDom = dom && isSumIntervalDom(dom);
    const tag = (node.superscript === "'" ? "TSum" : "Sum") + (keepDom ? dom : "");
    const args = node.args || [];
    const bodyAlts = nameExprAlts(args[args.length - 1], opts);
    const base = !bodyAlts.length ? [tag] : bodyAlts.flatMap((b) => [tag + "_" + b, tag + b]);
    return uniq(arityRange ? [arityRange, ...base] : base);
  }
  if (name === "LeanStack") {
    const scope = peelEntryStmt(node.scope ?? node.args?.[1]);
    const bodyAlts = nameExprAlts(scope, opts);
    if (!bodyAlts.length) return ["Stack"];
    return uniq(bodyAlts.flatMap((b) => ["Stack_" + b, "Stack" + b]).concat(["Stack"]));
  }

  const WRAP_OP_PREFIX = { LeanNorm: "Norm", LeanAbs: "Abs", LeanCeil: "Ceil", LeanFloor: "Floor" };
  const wrapPrefix = WRAP_OP_PREFIX[name];
  if (wrapPrefix !== undefined) {
    const arg = node.args?.[0];
    if (cls(unwrapParen(arg)) === "LeanSub") return [wrapPrefix + "Sub"];
    const leafHead = cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken" && isLeafName(arg.args[0].text, opts.leaves) && cls(unwrapParen(arg.args?.[1])) !== "LeanSub";
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
    if (isSimpleArg(arg, opts)) return uniq(innerAlts.map((i) => wrapPrefix + i));
    const out = [];
    for (const i of innerAlts) {
      out.push(wrapPrefix + i);
      out.push(wrapPrefix + "_" + i);
    }
    return uniq([...out, ...oldLeaf]);
  }

  {
    const decor = { LeanAdjoint: "Adjoint", LeanTranspose: "T", LeanConj: "Conj", LeanInv: "Inv" }[name];
    if (decor) {
      if (isQuantBinderHole(node.args?.[0], opts)) return opts?.keepDecorOnBinder ? [decor] : [];
      const inner = nameExprAlts(node.args?.[0], opts);
      if (!inner.length) return [decor];
      return uniq(inner.flatMap((i) => [decor + i, decor + "_" + i]).concat([decor]));
    }
  }

  if (name === "LeanToken") {
    const raw = node.text || "";
    if (isLeafName(raw, opts.leaves)) return [];
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
    if (isBinderMeasureProj(node, opts)) return [];
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
    if (name === "LeanRightarrow") return bodyAlts;
    if (name === "Lean_rightarrow") {
      const ante = node.args?.[0];
      if (isPropHyp(ante) || isPropHyp(body)) {
        const leftAlts = nameExprAlts(ante, opts);
        const namedL = (leftAlts.length ? leftAlts : [""]).map((x) => x || "");
        const namedR = (bodyAlts.length ? bodyAlts : [""]).map((x) => x || "");
        const binary = pathImpInfixChoices(
          namedL.some(Boolean) ? namedL.filter((x) => x !== undefined) : [""],
          namedR.some(Boolean) ? namedR.filter((x) => x !== undefined) : [""],
        ).stems;
        const flat = [];
        const pluralEqS = [];
        for (const l of namedL) {
          for (const r of namedR) {
            if (!l && !r) flat.push("Imp__");
            else if (!l && r) flat.push("Imp_" + r);
            else if (l && !r) flat.push("Imp" + l);
            else {
              flat.push("Imp" + l + r);
              if (l === r && (l === "Eq" || l.startsWith("Eq")))
                pluralEqS.push("Imp" + ("EqS" + l.slice(2)));
            }
          }
        }
        return uniq([...pluralEqS, ...binary, ...flat, ...bodyAlts.map((b) => b ? "Imp_" + b : "Imp"), ...bodyAlts].filter(Boolean));
      }
      return bodyAlts;
    }
    if (!bodyAlts.length) return ["Fun"];
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
    const last = args[args.length - 1];
    if (cls(last) === "LeanParenthesis" && cls(last.args?.[0]) === "LeanSub") {
      const hn = cls(head) === "LeanToken" && !isLeafName(head.text, opts.leaves) ? [nameToken(head.text)] : [];
      return uniq([...hn.filter(Boolean).map((h) => h + "_Sub"), "UFnSub"]);
    }
    {
      if (isArgMaxMinApp(node)) return [argMaxMinTokenName(node)];
      const am = argMaxMinTokenName(args[0]);
      if (am && isArgMaxMinGetElem(args[0])) return [am];
    }

    const headCls = cls(head);
    if ((headCls === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") ||
        (headCls !== "LeanToken" && headCls !== "LeanProperty" && headCls !== "LeanParenthesis")) {
      const headAlts = nameExprAlts(head, opts);
      if (headAlts.length) {
        const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
        let pref = applyEvalPrefix(head);
        if (pref === "Get" && headAlts.some((n) => n.startsWith("Get"))) pref = "";
        let acc = pref ? cartJoin([pref], headAlts, joinHeadChild) : headAlts.slice();
        if (cls(unwrapParen(head)) === "LeanPow") acc = uniq([...acc, ...headAlts]);
        const all = [...acc];
        for (const aa of argAltLists) {
          acc = cartJoin(acc, aa, joinHeadChild);
          all.push(...acc);
        }
        return uniq(all);
      }
    }

    if (cls(head) === "LeanProperty") {
      const methodAlts = nameExprAlts(head, opts);
      const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
      if (!methodAlts.length) return [];
      if (!argAltLists.length) return methodAlts;
      let acc = methodAlts;
      const all = [...methodAlts];
      const binIv = methodAlts.some(isBinaryIntervalCtor);
      for (const a of args.slice(1)) {
        const argAlts = nameExprAlts(a, opts);
        if (!argAlts.length) continue;
        acc = binIv
          ? cartJoin(acc, argAlts, joinHeadChild)
          : uniq([...cartJoin(acc, argAlts, joinHeadChild), ...argJoinAlts(acc, a, argAlts, opts)]);
        all.push(...acc);
      }
      return uniq(all);
    }

    if (cls(head) === "LeanToken") {
      const headLeaf = isLeafName(head.text, opts.leaves);
      const headName = headLeaf ? "" : nameToken(head.text || "");
      if (!headName) {
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
      const binIv = isBinaryIntervalCtor(headName);
      for (const a of args.slice(1)) {
        const alts = nameExprAlts(a, opts);
        if (!alts.length) continue;
        acc = binIv ? cartJoin(acc, alts, joinHeadChild) : argJoinAlts(acc, a, alts, embedOpts);
        if (acc.length > NODE_ALT_CAP) acc = acc.slice(0, NODE_ALT_CAP);
        all.push(...acc);
      }
      const idx = head !== args[0] ? nameExprAlts(args[0].args?.[1], opts) : [];
      if (idx.length) return uniq([...cartJoin(acc, idx, (h, i) => h + "_" + i), ...all]);
      return uniq(all);
    }

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

  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg" || (name === "Lean_cdotp" && node.subscript === "ᵥ") || name === "LeanMatMul") {
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
        return leftAlts.length ? cartJoin([sub], leftAlts, joinHeadChild) : [sub + "__"];
      }
    }
    if (name === "LeanDiv" || name === "LeanMul") {
      const lEv = matchProbApp(args[0]);
      const rEv = matchProbApp(args[1]);
      if (lEv && rEv) {
        const ln = nameProbEvent(lEv);
        const rn = nameProbEvent(rEv);
        if (name === "LeanDiv") {
          const divProb = divProbEventName(ln, rn);
          if (divProb) return [divProb];
        }
        if (name === "LeanMul") {
          if (ln.startsWith("Prob") && rn.startsWith("Prob")) return ["Mul" + ln + rn];
        }
      }
    }
    const leftAlts = nameExprAlts(args[0], opts);
    const rightAlts = nameExprAlts(args[1], opts);
    const out = [];
    const rightSet = new Set(rightAlts);
    for (const l of leftAlts) {
      if (!l || !rightSet.has(l)) continue;
      const snakePlural = pluralSnakeS(l);
      if (snakePlural) out.push(tag + snakePlural);
      out.push(tag + pluralMidS(l));
      if (pluralLetterS(l)) out.push(tag + pluralLetterS(l));
      out.push(tag + sameChildS(l));
    }
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
          if (powBinArith) {
            out.push(tag + l + "__" + r);
            continue;
          }
          if (joinDigits(l, r) !== l + r) out.push(tag + joinDigits(l, r));
          if (name === "LeanMul" && l === "Expect" && r === "Expect") {
            out.push(tag + "ExpectS");
            continue;
          }
          out.push(tag + l + r);
          out.push(tag + l + "_" + r);

        }
      }
    }
    for (const [, di, dj] of diag) {
      const l = leftAlts[di], r = rightAlts[dj];
      if (!l || !r) continue;
      if (name === "LeanMul" && l === "Expect" && r === "Expect") continue;
      out.push(l + tag + r);
      out.push(l + r + tag);
      out.push(l + "_" + tag + "_" + r);
    }
    if (!leftAlts.length && rightAlts.length) {
      for (const r of rightAlts) {
        out.push(tag + "_" + r);
        if (name !== "Lean_cdotp") out.push(tag + r);
      }
    }
    if (leftAlts.length && !rightAlts.length) {
      for (const l of leftAlts) {
        if (name === "LeanMul" && /^(?:T|Adjoint|Conj)$/.test(l)) {
          out.push(tag + l + "__");
          out.push(tag + l);
          out.push(l + tag);
        } else {
          out.push(tag + l);
          out.push(l + tag);
        }
      }
    }
    if (!leftAlts.length && !rightAlts.length) out.push(name === "Lean_cdotp" ? "Dot__" : tag);
    const bareFun = (n, alts) => cls(unwrapParen(n)) === "Lean_fun" && alts.length === 1 && alts[0] === "Fun";
    if (bareFun(args[0], leftAlts) || bareFun(args[1], rightAlts)) {
      const L = bareFun(args[0], leftAlts) ? [] : leftAlts;
      const R = bareFun(args[1], rightAlts) ? [] : rightAlts;
      if (!L.length && !R.length) out.push(tag);
      for (const r of L.length ? [] : R) {
        out.push(tag + "_" + r);
        if (name !== "Lean_cdotp") out.push(tag + r);
      }
      for (const l of R.length ? [] : L) out.push(tag + l);
    }
    if (name === "LeanPow" && (leftAlts.length || rightAlts.length)) out.push(tag);
    if (name === "LeanMatMul") {
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
    if (!nameExpr(node.args?.[0], opts) && !nameExpr(node.args?.[1], opts)) return ["SMul__"];
    return ["SMul"];
  }

  if (name === "LeanDoubleAngleQuotation") return [];
  if (name === "LeanIte") {
    const args = node.args || [];
    const parts = cls(args[0]) === "LeanColon"
      ? [args[0].args?.[1], args[1], args[2]]
      : [args[0], args[1], args[2]];
    for (const p of parts) {
      const alts = nameExprAlts(p, opts);
      if (alts.length) return alts;
    }
    return [];
  }
  if (name === "LeanGetElem") {
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "ℙ") return ["Prob"];
    if (cls(node.args?.[0]) === "LeanToken" && node.args[0].text === "∇") return ["Grad"];
    if (isGetElemColonSlice(node)) return ["GetSlice"];
    if (isBinderGetAtLiteral(node, opts)) return [];
    if (isGetIndexNoise(node.args?.[1], opts)) {
      return nameExprAlts(node.args?.[0], opts);
    }
    {
      const idxAlts = nameExprAlts(node.args?.[1], opts).filter(Boolean);
      if (idxAlts.length) return uniq(idxAlts.map((idx) => snakeFocus("Get", idx)));
      const headAlts = nameExprAlts(node.args?.[0], opts).filter(Boolean);
      return headAlts.length ? headAlts : ["Get"];
    }
  }
  if (name === "LeanBitOr") return [];

  if (Array.isArray(node.args)) {
    const childAlts = node.args.map(a => nameExprAlts(a, opts)).filter(a => a.length);
    if (!childAlts.length) return [];
    return childAlts[0];
  }
  return [];
}

function classChain(node, out = []) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  if (CLASS_TOKEN[name] || name === "LeanEq" || name === "Lean_bullet" || name === "LeanConstruct" || name === "LeanProperty" || name === "LeanDistributed") out.push(name);
  else if (name === "LeanToken" && node.text && /^[A-Z]/.test(node.text)) out.push("Token:" + node.text);
  if (name === "Lean_perp") {
    out.push("Lean_perp");
    for (const a of node.args || []) classChain(a, out);
    return out;
  }
  if (name === "LeanBitOr" && condIndepBits(node)) {
    out.push("LeanBitOr");
    for (const a of node.args || []) classChain(a, out);
    return out;
  }
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
  if (name === "Lean_otimes" || name === "Lean_otimesSub") {
    out.push(name);
    for (const a of node.args || []) classChain(a, out);
    return out;
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

function extractInstanceHyps(indented) {
  const termBinders = new Set();

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

function truncateMainProof(source) {
  const at = source.indexOf("@[path]");
  const imply = source.indexOf("-- imply", at < 0 ? 0 : at);
  if (imply < 0) return source;
  const m = /:=(\s|$)/.exec(source.slice(imply));
  if (!m) return source;
  return source.slice(0, imply + m.index) + ":= by\n  sorry\n";
}
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
  const quantLeaves = new Set();
  collectLeafBinders(sig.nls, quantLeaves, true);
  collectLeafBinders(sig.implyStmts, quantLeaves, true);
  collectImplyIntroducedIdents(sig.implyStmts, quantLeaves);
  {
    const bundles = bundleVars(sig.indented);
    for (const r of new Set([sig.nls, sig.implyStmts])) holeBundleProjections(r, bundles, leaves);
  }
  const nameOpts = { leaves, quantLeaves, typeLeaves: collectTypeBinders(sig.indented) };
  const imply = sanitizePathSeg(nameExpr(sig.implyStmts, nameOpts) || "");
  const givens = extractGivens(sig.nls).filter((h) => h.prop).map((h) => ({
    binder: h.name,
    name: sanitizePathSeg(nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || ""),
  }));
  return { imply, givens };
}

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
  const abs = options.file ? path.resolve(options.file) : path.resolve(filePath);
  const source = options.source != null
    ? String(options.source).replace(/\r\n/g, "\n")
    : fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
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
  const curTop = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/").split("/")[0];
  const dataSections = sections.filter((s) => {
    if (nonDataFolder(s)) return false;
    if (refusedSectionFolder(s)) return sectionKindMap().get(s) === "type class" && s === curTop;
    return true;
  });
  const givenTypeNodes = extractGivens(sig.nls).filter((h) => h.prop).map((h) => h.typeNode);
  const legacyCustom = nonDataFolder(curTop) ? customSection(sections, sig.implyStmts, givenTypeNodes, importSections(source, sections), sig.indented) : null;
  const legacy = !!legacyCustom && nonDataFolder(legacyCustom) && curTop === legacyCustom;
  const custom = legacy ? legacyCustom : customSection(dataSections, sig.implyStmts, givenTypeNodes, importSections(source, dataSections), sig.indented);
  const picked = pickSection(sig.colon, legacy ? sections : dataSections, {
    custom,
    file: abs,
    imports: [
      ...[...importSections(source, sections).keys()].filter((s) => DATA_TYPE_SECTIONS.has(s) || TYPE_TO_SECTION[s]),
      ...openDataSections(source),
    ],
  });
  const section = options.section || picked.section;
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
  const quantLeaves = new Set();
  collectLeafBinders(sig.nls, quantLeaves, true);
  collectLeafBinders(sig.implyStmts, quantLeaves, true);
  collectImplyIntroducedIdents(sig.implyStmts, quantLeaves);
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
  const nameOpts = { leaves, quantLeaves, typeLeaves: collectTypeBinders(sig.indented), section };
  const implyAltsOf = (sg, no) => {
    const joined = nameExprAlts(sg.implyStmts, no).filter(Boolean);
    const partsLeft = splitTopConjunction(sg.implyStmts, false);
    const partsFull = splitTopConjunction(sg.implyStmts, true);
    const eqConj = partsFull && partsFull.length >= 2 && partsFull.length <= 6 && partsFull.every(isEqConjunct);
    const finishedPeer = partsFull && partsFull.length >= 2 && partsFull.length <= 6 && partsFull.every(isFinishedPathConjunct);
    const parts = (eqConj || finishedPeer) ? partsFull : partsLeft;
    if (!parts || parts.length < 2) return joined;
    const fixJ = parts.length === 2 && isMaxProbJointEq(parts[1]) ? fixMaxProbJointName : (x) => x;
    const peerOpts = finishedPeer ? { ...no, asGiven: true, keepDecorOnBinder: true } : null;
    const perConjunct = parts.map((p) => {
      const base = nameExprAlts(p, no).filter(Boolean);
      if (!peerOpts) return base;
      const flat = nameExpr(p, peerOpts);
      const peerAlts = nameExprAlts(p, peerOpts).filter(Boolean);
      return uniq([...(flat ? [flat] : []), ...peerAlts, ...base]);
    });
    if (!perConjunct.every((a) => a.length)) return joined.map(fixJ);
    const splitAlts = perConjunct.reduce(
      (acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))),
      [""],
    );
    let topAnd = sg.implyStmts;
    while (topAnd && (cls(topAnd) === "LeanParenthesis" || cls(topAnd) === "LeanStatements" || cls(topAnd) === "LeanArgsNewLineSeparated")) {
      topAnd = cls(topAnd) === "LeanParenthesis" ? topAnd.args?.[0] : firstConclusion(topAnd);
    }
    const andBinary = !eqConj && !finishedPeer
      && cls(topAnd) === "Lean_land"
      && !isAtomicHoleAndConjunct(topAnd.args?.[0], no)
      && !isAtomicHoleAndConjunct(topAnd.args?.[1], no);
    const sideChoices = (node) => {
      const named = nameExprAlts(node, no).filter((s) => {
        const t = String(s || "");
        return t && !t.includes("/") && !t.includes("And") && !t.includes("Or");
      });
      let walked = typeof node?.pathChoices === "function" ? node.pathChoices(no) : [];
      if (cls(node) === "Lean_nabla" || cls(node) === "LeanNabla"
          || (walked || []).some((s) => String(s).startsWith("Nabla"))) {
        walked = nablaPathChoicesToGrad(walked);
      }
      return pathUniqKeepEmpty([...named, ...(walked || []), ""]);
    };
    const andStems = andBinary
      ? pathAndInfixChoices(sideChoices(topAnd.args[0]), sideChoices(topAnd.args[1])).stems
      : null;
    const joinedKept = andStems ? joined.filter((s) => !String(s).includes("And")) : joined;
    const res = uniq([...splitAlts, ...joinedKept, ...(andStems || [])].map(fixJ));
    if (eqConj && splitAlts.length) {
      const canonParts = parts.map((p, i) => {
        const c = sanitizeRelPath(nameExpr(p, no) || "");
        return perConjunct[i].find((x) => sanitizeRelPath(x) === c) || perConjunct[i][0];
      });
      res.preferred = fixJ(canonParts.join("/"));
      if (partsLeft && partsLeft.length >= 2 && partsLeft.length < partsFull.length) {
        const perL = partsLeft.map((p) => nameExprAlts(p, no).filter(Boolean));
        if (perL.every((a) => a.length)) {
          const leftSplits = perL.reduce((acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))), [""]);
          res.extra = uniq([...(res.extra || []), ...leftSplits.map(fixJ)]);
        }
      }
    } else if (finishedPeer && splitAlts.length) {
      const canonParts = parts.map((p, i) => {
        const alts = perConjunct[i];
        const flatNamed = alts.find((x) => {
          const s = sanitizeRelPath(x || "");
          return s && !s.includes("/") && /^(Eq|Ne|Lt|Gt|Le|Ge|Is|Has)[A-Z0-9_]/.test(s);
        });
        if (flatNamed) return flatNamed;
        const c = sanitizeRelPath(nameExpr(p, peerOpts) || "");
        return alts.find((x) => sanitizeRelPath(x) === c)
          || alts.find((x) => x && !String(x).includes("/"))
          || alts[0];
      });
      res.preferred = fixJ(canonParts.join("/"));
      if (partsLeft && partsLeft.length >= 2 && partsLeft.length < partsFull.length) {
        const perL = partsLeft.map((p) => nameExprAlts(p, no).filter(Boolean));
        if (perL.every((a) => a.length)) {
          const leftSplits = perL.reduce((acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))), [""]);
          res.extra = uniq([...(res.extra || []), ...leftSplits.map(fixJ)]);
        }
      }
    }
    if (!res.preferred && parts.length >= 2) {
      const canonParts = parts.map((p, i) => {
        const c = sanitizeRelPath(nameExpr(p, no) || "");
        return perConjunct[i].find((x) => sanitizeRelPath(x) === c) || perConjunct[i][0];
      });
      if (canonParts.every(Boolean)) res.preferred = fixJ(canonParts.join("/"));
    }
    if (fixJ === fixMaxProbJointName) {
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
        ...short,
      ]);
      out.preferred = preferred || res.preferred;
      return out;
    }
    return res;
  };
  setRvNames(sig.indented);
  let implyAltsA = implyAltsOf(sig, nameOpts);
  const diskImplyHouse = implyStemFromRelPath(relCurrent);
  {
    const bodySymm = eqSymmToDualTSumBodyName(sig.implyStmts, diskImplyHouse);
    if (bodySymm) {
      implyAltsA = uniq([bodySymm, ...implyAltsA]);
      implyAltsA.preferred = bodySymm;
    }
  }
  {
    const bodyMapPi = mapPiGaussianRealEqProdChiSquareSBodyName(sig.implyStmts, diskImplyHouse);
    if (bodyMapPi) {
      implyAltsA = uniq([bodyMapPi, ...implyAltsA]);
      implyAltsA.preferred = bodyMapPi;
    }
  }

  {
    const houseMis = isMulInvSqrtEqFamily(diskImplyHouse) ? diskImplyHouse : "";
    const fromTree = mulInvSqrtEqImplyStemsFromTree(sig.implyStmts, nameOpts, houseMis);
    const nameMis = sanitizeRelPath(nameExpr(sig.implyStmts, nameOpts) || "");
    if (fromTree || isMulInvSqrtEqFamily(implyAltsA) || isMulInvSqrtEqFamily(nameMis) || houseMis) {
      const bodyMis =
        houseMis ||
        (fromTree && fromTree.stems.find((s) => String(s).includes("/eq/"))) ||
        (fromTree && fromTree.stems[0]) ||
        "";
      const injected = fromTree ? fromTree.stems : mulInvSqrtEqAllowedImplyStems(bodyMis, sig.implyStmts, nameOpts);
      const keepSet = new Set(injected);
      const isLegacyMulInvSqrtImply = (p) => {
        const core = String(p || "").replace(/\\/g, "/").replace(/\.lean$/, "");
        let leaf = core;
        const eqi = core.search(/(?:^|\/)(?:MulInvSqrt|MulInv|Mul)\/eq\//);
        if (eqi >= 0) {
          const start = eqi === 0 ? 0 : eqi + 1;
          const ofi = core.indexOf("/of/", start);
          leaf = ofi >= 0 ? core.slice(start, ofi) : core.slice(start);
        } else {
          const ofi = core.indexOf("/of/");
          const body = ofi >= 0 ? core.slice(0, ofi) : core;
          leaf = body.includes("/") ? body.slice(body.lastIndexOf("/") + 1) : body;
        }
        return !keepSet.has(leaf) && !isAllowedMulInvSqrtEqImply(core) && !isAllowedMulInvSqrtEqImply(leaf);
      };
      implyAltsA = uniq([
        ...injected,
        ...implyAltsA.filter((p) => isAllowedMulInvSqrtEqImply(p)),
      ]);
      if (bodyMis) implyAltsA.preferred = bodyMis;
      implyAltsA.isLegacyMulInvSqrtImply = isLegacyMulInvSqrtImply;
      implyAltsA.mulInvSqrtShowCap = keepSet.size;
      if (fromTree) {
        implyAltsA.mulInvSqrtLhs = fromTree.left;
        implyAltsA.mulInvSqrtRhs = fromTree.right;
      }
    }
  }
  const undig = (x) => sanitizeRelPath(x || "").replace(/(\d)'(?=\d)/g, "$1");
  const pickCanon = (alts, preferred) =>
    alts.find((a) => sanitizeRelPath(a) === sanitizeRelPath(preferred || "")) ||
    (preferred ? alts.find((a) => /\d'\d/.test(a) && undig(a) === undig(preferred)) : null) || alts[0] || preferred;
  {
    const eq = peelImplyEq(sig.implyStmts);
    if (eq && cls(eq) === "LeanEq" && typeof eq.lhs?.pathChoices === "function") {
      const stems = pathEqInfixChoices(
        eq.lhs.pathChoices(nameOpts) || [],
        eq.rhs?.pathChoices?.(nameOpts) || [],
      ).stems.filter((s) => s.includes("/eq/") && !unfilledHolePiece(s));
      if (stems.length) implyAltsA = uniq([...stems, ...implyAltsA]);
    }
  }
  {
    const eq = peelImplyEq(sig.implyStmts);
    const fromExpect = eq && typeof eq.pathExpectEqStems === "function" ? eq.pathExpectEqStems(nameOpts) : null;
    if (fromExpect) {
      const keep = new Set(fromExpect.stems);
      const canon = "Expect_Mul/eq/MulExpectS";
      implyAltsA = fromExpect.stems.slice();
      implyAltsA.preferred = canon;
      implyAltsA.isLegacyExpectEqImply = (p) => {
        const core = String(p || "").replace(/\\/g, "/").replace(/\.lean$/, "");
        const ofi = core.indexOf("/of/");
        const leaf = ofi >= 0 ? core.slice(0, ofi) : core;
        return !keep.has(leaf);
      };
    }
  }
  const implyNameA = pickCanon(implyAltsA, implyAltsA.preferred || nameExpr(sig.implyStmts, nameOpts)) || "Imply";
  const passB = (() => {
    KEEP_GREEK = true;
    try {
      const sigB = extractSignature(extractLemma(compileLemmaSource(source), lemmaName));
      for (const r of new Set([sigB.indented, sigB.nls, sigB.implyStmts])) reassociateDotProduct(r);
      const leavesB = collectLeafBinders(sigB.indented);
      collectLeafBinders(sigB.implyStmts, leavesB, true);
      collectImplyIntroducedIdents(sigB.implyStmts, leavesB);
      const quantLeavesB = new Set();
      collectLeafBinders(sigB.nls, quantLeavesB, true);
      collectLeafBinders(sigB.implyStmts, quantLeavesB, true);
      collectImplyIntroducedIdents(sigB.implyStmts, quantLeavesB);
      const bundlesB = bundleVars(sigB.indented);
      for (const r of new Set([sigB.nls, sigB.implyStmts])) holeBundleProjections(r, bundlesB, leavesB);
      const optsB = { leaves: leavesB, quantLeaves: quantLeavesB, typeLeaves: collectTypeBinders(sigB.indented), section };
      setRvNames(sigB.indented);
      const implyAlts = implyAltsOf(sigB, optsB);
      const implyName = pickCanon(implyAlts, implyAlts.preferred || nameExpr(sigB.implyStmts, optsB)) || "Imply";
      const givensAllB = extractGivens(sigB.nls);
      const multiGivenB = givensAllB.filter((h) => h.prop).length > 1;
      const givens = givensAllB.map((h) => ({
        alts: nameExprAlts(h.typeNode, { ...optsB, asGiven: true, multiGiven: multiGivenB }).filter(Boolean),
        name: nameExpr(h.typeNode, { ...optsB, asGiven: true, multiGiven: multiGivenB }) || "Given",
      }));
      return { implyAlts, implyName, givens };
    } catch {
      return null;
    } finally {
      KEEP_GREEK = false;
    }
  })();
  const legalMeqImply = (p) => {
    if (hasIllegalMeqImply(p)) return false;
    const segs = String(p).split("/").filter(Boolean);
    return !(segs.includes("MEq") && segs.length > 1);
  };
  const implyAlts = uniq([...implyAltsA, ...(passB?.implyAlts || [])])
    .filter(legalMeqImply)
    .filter((p) => !(implyAltsA.isLegacyMulInvSqrtImply && implyAltsA.isLegacyMulInvSqrtImply(p)))
    .filter((p) => !(implyAltsA.isLegacyExpectEqImply && implyAltsA.isLegacyExpectEqImply(p)));
  const implyExtraAlts = [...(implyAltsA.extra || []), ...(passB?.implyAlts?.extra || [])].filter(legalMeqImply);

  const SOFT = /^(of|is|in|sub|eq|ne|lt|gt|le|ge|dvd|ae[A-Za-z]*)$/;
  const lowerComp = (p) => sanitizeRelPath(p || "").split("/").some((c) => /^[a-z]/.test(c) && !SOFT.test(c));
  let preferB = !!passB && passB.implyName !== implyNameA && lowerComp(implyNameA) && !lowerComp(passB.implyName);
  let implyName = preferB ? passB.implyName : implyNameA;
  if (hasIllegalMeqImply(implyName)) {
    implyName = implyAlts.find((a) => !hasIllegalMeqImply(a)) || implyName;
  }
  const implyChain = classChain(sig.implyStmts);
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (cls(n) === "LeanProperty" && cls(n.args?.[0]) === "LeanToken") conclNames.add(n.args[0].text);
    for (const a of n.args || []) walk(a);
  })(sig.implyStmts);
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
    if (h.prop && structLike && conclNames.has(h.name) && !/^Is[A-Z]/.test(typeHead(t))) return { ...h, prop: false };
    if (h.prop && structLike && dataHeads.has(typeHead(t)) && !/^Is[A-Z]/.test(typeHead(t))) return { ...h, prop: false };
    if (h.prop && structLike && repoDecls().typeAbbrevs.has(typeHead(t)) && usedInConcl) return { ...h, optional: true, canonSkip: true };
    if (h.prop && structLike && usedInConcl && (TYPE_TO_SECTION[typeHead(t)] === typeHead(t) || typeHead(t) === "Measure")) return { ...h, optional: true, canonSkip: true };
    if (h.prop && structLike && usedInConcl && repoDecls().structs.has(typeHead(t))) return { ...h, optional: true };
    if (h.prop && section === "Random") {
      let b = t;
      while (cls(b) === "Lean_forall") b = unwrapParen(b.args?.[b.args.length - 1]);
      if (typeHead(b) === "Integrable") return { ...h, optional: true };
      if (conclTokenSet.has("𝔼") && /^(AE)?(Strongly)?Measurable$/.test(typeHead(b))) {
        const jn = nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "";
        if (/MeasurableJoint/.test(jn)) return { ...h, optional: true, canonSkip: true };
        return { ...h, optional: true };
      }
    }
    return h;
  });
  const hmmShape = isHmmNegLogCondShape(sig.implyStmts);
  const logJointFns = logProbJointFnNames(hyps.filter((h) => h.prop).map((h) => h.typeNode));
  const multiGiven = hyps.filter((h) => h.prop && !h.canonSkip).length > 1;
  let givenAltLists = [...hyps.filter((h) => h.prop)].reverse().map((h) => {
    const b = passB?.givens?.[h.idx];
    const altsA = nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true, multiGiven }).filter(Boolean);
    const nameA = nameExpr(h.typeNode, { ...nameOpts, asGiven: true, multiGiven }) || "Given";
    const lt0Joint = bvarAllLt0ProbJointName(h.typeNode);

    const neJoint0 = neProbJoint0GivenName(h.typeNode);
    const neProb0 = allNeProb0GivenName(h.typeNode);
    const bodyPrefer = lt0Joint || neJoint0 || neProb0 || null;
    const bodyLegacy = [
      ...(lt0Joint ? ["All_GtProbJoint__0"] : []),
      ...(neJoint0 ? ["Ne0ProbJoint", "NeProbS_0", "NeProb_0"] : []),
      ...(neProb0 ? ["NeProbS_0", "All_NeProbS_0", "NeProb_0"] : []),
    ];
    const maxLog = maxLogProbJointGiven(h.typeNode, logJointFns);
    const dropIllegalJoint = (xs) =>
      xs.filter((x) => !isIllegalGtProbJointAtom(x) && !isIllegalNeProbJointAtom(x) && !isIllegalTripleUnderscoreAtom(x));
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
        ...legacyQuantCamelAlts(allAlts),
        ...legacyTransposeAlts(allAlts),
      ]),

      name: rawName,
      nameB: rawNameB,
      chain: classChain(h.typeNode),
    };
  });
  for (const g of givenAltLists) {
    const kept = [], dropped = [];
    for (const a of g.alts || []) {
      if (hasCapToken(a, "Transpose")) dropped.push(a);
      else if (/(?:^|_)EqMulT(?!__)/.test(a) || /(?:^|_)Eq_Mul_T__/.test(a)) dropped.push(a);
      else kept.push(a);
    }
    for (const d of dropped) {
      const tt = replaceCapToken(d, "Transpose", "T");
      if (tt && tt !== d) kept.push(tt);
    }
    if (!kept.length) continue;
    g.extraAlts = uniq([...(g.extraAlts || []), ...dropped, ...legacyTransposeAlts(kept)]);
    g.alts = uniq(kept);
    if (hasCapToken(g.name, "Transpose")) g.name = replaceCapToken(g.name, "Transpose", "T");
    if (g.nameB && hasCapToken(g.nameB, "Transpose")) g.nameB = replaceCapToken(g.nameB, "Transpose", "T");
    const fixMulT = (n) => {
      if (!n) return n;
      if (n === "All_EqMulT_1" || n === "All_EqMulT1") return "All_Eq_MulT__1";
      if (n === "EqMulT_1" || n === "EqMulT1") return "Eq_MulT__1";
      if (n === "All_Eq_Mul_T__1") return "All_Eq_MulT__1";
      if (n === "Eq_Mul_T__1") return "Eq_MulT__1";
      return n;
    };
    g.name = fixMulT(g.name);
    if (g.nameB) g.nameB = fixMulT(g.nameB);
    if (g.name && !g.alts.includes(g.name)) g.alts = uniq([g.name, ...g.alts]);
  }
  for (const g of givenAltLists) {
    const pref = g.name || "";
    if (pref !== "EqAdjoint" && pref !== "Eq_Adjoint") continue;
    const kept = [], dropped = [];
    for (const a of g.alts || []) {
      if (a === "Eq_Adjoint" && pref === "EqAdjoint") dropped.push(a);
      else kept.push(a);
    }
    if (!kept.length) continue;
    g.extraAlts = uniq([...(g.extraAlts || []), ...dropped]);
    g.alts = kept;
    g.name = "EqAdjoint";
    if (g.nameB === "Eq_Adjoint") g.nameB = "EqAdjoint";
  }
  for (const g of givenAltLists) {
    const pref = g.name || "";
    if (!/^All_/.test(pref) || pref.includes("/")) continue;
    const rel0Scope = /^All_(Lt|Gt)0/.test(pref);
    const kept = [];
    const dropped = [];
    for (const a of g.alts || []) {
      if (/^All_\d/.test(a)) dropped.push(a);

      else if (/^All_(Lt|Gt)0_./.test(a)) dropped.push(a);

      else if (rel0Scope && /^All_/.test(a) && !/^All_(Lt|Gt)/.test(a)) dropped.push(a);

      else if (/DotMulVec/.test(a)) dropped.push(a);

      else if (/^All_/.test(a)) kept.push(a);
      else dropped.push(a);

    }
    if (!kept.length) continue;
    g.extraAlts = uniq([...(g.extraAlts || []), ...dropped, ...legacyQuantCamelAlts(kept)]);
    g.alts = kept;
  }
  const instAltLists = extractInstanceHyps(sig.indented).reverse().map((h) => ({
    binder: h.name,
    alts: nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true, multiGiven }).filter(Boolean),
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given",
    chain: classChain(h.typeNode),
  }));
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
  if (multiGiven) {
    const collapseRel = (xs) => {
      const out = [];
      for (const a of xs || []) {
        if (!a || REL_SPLIT_HAS.test(a)) {
          const one = relSplitInline(a);
          if (one) out.push(one);
        } else out.push(a);
      }
      return uniq(out);
    };
    for (const g of givenAltLists) {
      const won = pickCanon(g.alts, g.name);
      const inline = relSplitInline(won);
      g.alts = collapseRel(g.alts);
      if (g.extraAlts) g.extraAlts = collapseRel(g.extraAlts);
      if (inline) {
        g.name = inline;
        g.alts = uniq([inline, ...g.alts]);
      }
      if (g.nameB && relSplitInline(g.nameB)) g.nameB = relSplitInline(g.nameB);
    }
  }
  const canonGivenLists = givenAltLists.filter((g) => !g.canonSkip);

  let givenNames = canonGivenLists.map((g) => ({ binder: g.binder, name: pickCanon(g.alts, g.name), chain: g.chain }));
  if (preferB) givenNames = canonGivenLists.map((g) => ({ binder: g.binder, name: g.nameB || pickCanon(g.alts, g.name), chain: g.chain }));
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
  const useInstTail = instAltLists.length > 0 && instAltLists.length <= 3 && canonGivenLists.length === 0;
  const implyRegexAltsEarly = holeRegexAlternatives(sig.implyStmts, nameOpts);
  const uniqEmitTok = (xs) => [...new Set((xs || []).filter(Boolean).map((x) => String(x)))];
  const stemMatchesImplyHole = (stem) => stemMatchesAnyHoleRegex(stem, implyRegexAltsEarly);
  const implyFillStems = uniqEmitTok([
    ...holeFillStems(sig.implyStmts, nameOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
    ...holeFillStemsEqMulS(sig.implyStmts, nameOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
    ...implyRegexAltsEarly.flatMap((re) => holeRegexLanguageTokens(re || "")),
    implyStemFromRelPath(path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/")),
  ]).filter(stemMatchesImplyHole);
  const implyAltStemOk = (alt) => {
    const flat = sanitizeRelPath(String(alt || ""));
    if (!flat) return false;
    if (!flat.includes("/")) return stemMatchesImplyHole(flat);
    return stemMatchesImplyHole(flat);
  };
  let implyAltsEmit = uniqEmitTok([
    ...implyFillStems,
    ...implyAlts.filter(implyAltStemOk),
  ]);
  if (implyAlts.preferred && implyAltStemOk(implyAlts.preferred)) {
    implyAltsEmit = uniqEmitTok([sanitizeRelPath(implyAlts.preferred), ...implyAltsEmit]);
  }
  if (!implyAltsEmit.length) implyAltsEmit = implyFillStems.slice();
  const pathOrderHypsEarly = [...hyps.filter((h) => h.prop && !h.canonSkip)].reverse();
  const givenRegexListsEarly = pathOrderHypsEarly.map((h) =>
    holeRegexAlternatives(h.typeNode, { ...nameOpts, asGiven: true }),
  );
  const givenOptionalFlags = givenAltLists.map((g) => !!g.optional);
  const givenAltListsEmit = givenAltLists.map((g, i) => {
    const regexes = givenRegexListsEarly[i] || [];
    const matchG = (stem) => stemMatchesAnyHoleRegex(stem, regexes);
    const h = pathOrderHypsEarly[i];
    const fills = h
      ? uniqEmitTok([
          ...holeFillStems(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean).map((s) => sanitizePathSeg(s)),
          ...holeFillStemsPlural(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean).map((s) => sanitizePathSeg(s)),
          ...holeFillStems(h.typeNode, { ...nameOpts, asGiven: true, mulBothHolesBare: true }).filter(Boolean).map((s) => sanitizePathSeg(s)),
          ...holeFillStemsImpEqS(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean).map((s) => sanitizePathSeg(s)),
          ...regexes.flatMap((re) => holeRegexLanguageTokens(re || "")),
        ]).filter(matchG)
      : [];
    const kept = uniqEmitTok([...(g.alts || []), ...fills]).filter(matchG);
    let alts = kept.length ? kept : fills.slice();
    alts.sort((a, b) => (b.length - a.length) || (a < b ? -1 : a > b ? 1 : 0));
    const eqs = alts.filter((a) => /ImpEqS/.test(a) || /_ImpEqS/.test(a));
    if (eqs.length) alts = uniqEmitTok([...eqs, ...alts]);
    let name = g.name;
    if (eqs.length && (!name || !/ImpEqS/.test(name) || !matchG(name))) name = eqs[0];
    else if (name && !matchG(name)) name = alts[0] || name;
    let nameB = g.nameB;
    if (nameB && !matchG(nameB)) nameB = null;
    return {
      ...g,
      alts,
      name,
      nameB,
      extraAlts: uniqEmitTok([...(g.extraAlts || []), ...fills]).filter(matchG),
    };
  });
  {
    const curRel = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
    const ofSegs = ofStemsFromRelPath(curRel);
    for (let gi = 0; gi < ofSegs.length && gi < givenAltListsEmit.length; gi++) {
      const stem = ofSegs[gi];
      const g = givenAltListsEmit[gi];
      const regs = givenRegexListsEarly[gi] || [];
      if (!stemMatchesAnyHoleRegex(stem, regs)) continue;
      g.alts = uniqEmitTok([stem, ...(g.alts || [])]);
      g.extraAlts = uniqEmitTok([stem, ...(g.extraAlts || [])]);
      if (g.name && !stemMatchesAnyHoleRegex(g.name, regs)) g.name = stem;
    }
  }
  if (!stemMatchesImplyHole(sanitizeRelPath(implyName || ""))) {
    const matching = implyAltsEmit.filter((a) => stemMatchesImplyHole(sanitizeRelPath(a)));
    matching.sort((a, b) => (b.length - a.length) || (a < b ? -1 : a > b ? 1 : 0));
    implyName = matching[0] || implyName;
  }
  givenNames = givenAltListsEmit.filter((g) => !g.canonSkip).map((g, i) => {
    const prev = givenNames[i];
    return {
      binder: g.binder || prev?.binder,
      name: g.name || prev?.name || (g.alts || [])[0] || "Given",
      chain: g.chain || prev?.chain,
    };
  });
  const givenPaths = [...new Set([
    ...cartGiven(givenAltListsEmit),
  ])];
  const PATH_CAP = 20000;
  const implyShowCap = Math.max(200, implyAltsA.mulInvSqrtShowCap || 0, implyAltsEmit.length);
  const shownImply = implyAltsEmit.slice(0, implyShowCap);
  const shownGiven = givenPaths.slice(0, Math.max(1, Math.floor(PATH_CAP / Math.max(1, shownImply.length))));
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
  ).filter((p) => !/\[anonymous\]|anonymous/i.test(p)).filter((p) => !hasIllegalDistributedAddSnake(p)).filter((p) => !hasIllegalDistributedGaussianLower(p));
  const altSet = (alts) => new Set(alts.map((a) => sanitizeRelPath(a)));
  const implySet = altSet(implyExtraAlts.length ? [...implyAlts, ...implyExtraAlts] : implyAlts);
  const gSets = givenAltListsEmit.map((g) => {
    const xs = [...(g.alts || []), ...(g.extraAlts || [])];
    const s = xs.length ? altSet(xs) : new Set(["Given"]);
    if (g.optional) s.__optional = true;
    return s;
  });
  const iSets = useInstTail
    ? instAltLists.map((g) => (g.alts.length ? altSet(g.alts) : new Set(["Given"])))
    : null;
  const sectionFree = picked.score === 0;
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
    let cur = String(p).replace(/\\/g, "/").replace(/^Lemma\//, "").replace(/\.lean$/, "");
    if (!cur.includes("/") && cur.includes(".")) cur = cur.replace(/\./g, "/");
    if (/anonymous/i.test(cur)) return false;
    if (hasQuantEqSlash(cur)) return false;
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
  if (!allPaths.includes(relPath) && altMatch(relPath)
      && suggestionPathMatchesHoles(relPath, implyRegexAltsEarly, givenRegexListsEarly, { optionalFlags: givenOptionalFlags })) {
    allPaths.push(relPath);
  }
  if (!suggestionPathMatchesHoles(relPath, implyRegexAltsEarly, givenRegexListsEarly, { optionalFlags: givenOptionalFlags })) {
    const gEmitNames = givenAltListsEmit.filter((g) => !g.canonSkip).map((g) => ({
      binder: g.binder,
      name: g.name || (g.alts || [])[0] || "Given",
      chain: g.chain,
    }));
    const matchingImply = implyAltsEmit.filter((a) => stemMatchesImplyHole(sanitizeRelPath(a)));
    matchingImply.sort((a, b) => (b.length - a.length) || (a < b ? -1 : a > b ? 1 : 0));
    const rescueImply = matchingImply[0] || implyAltsEmit[0] || implyName;
    const rescued = buildRel(rescueImply, gEmitNames);
    if (suggestionPathMatchesHoles(rescued, implyRegexAltsEarly, givenRegexListsEarly, { optionalFlags: givenOptionalFlags })) {
      implyName = rescueImply;
      givenNames = gEmitNames;
      relPath = rescued;
    }
  }
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
  const validSorted = sorted.filter(validModulePath);
  const rawSuggestions = validSorted.length ? validSorted : sorted;
  const implyHoleRegex = implyHoleRegexFromAst(sig.implyStmts, nameOpts);
  const implyRegexAlts = implyRegexAltsEarly;
  const holeMatchOpts = { optionalFlags: givenOptionalFlags };
  let suggestions = rawSuggestions.filter((p) =>
    suggestionPathMatchesHoles(p, implyRegexAlts, givenRegexListsEarly, holeMatchOpts),
  );
  if (!suggestions.length && implyAltsEmit.length) {
    const rescueGiven = [...new Set(cartGiven(givenAltListsEmit))];
    suggestions = uniq(
      implyAltsEmit.flatMap((implyAlt) =>
        (rescueGiven.length ? rescueGiven : [""]).map((givenPath) => {
          const implyPath = sanitizeRelPath(implyAlt);
          const gp = givenPath ? sanitizeRelPath(givenPath) : "";
          const body = gp
            ? section + "/" + implyPath + "/of/" + gp + ".lean"
            : section + "/" + implyPath + ".lean";
          return body.replace(/\\/g, "/");
        }),
      ),
    ).filter((p) =>
      suggestionPathMatchesHoles(p, implyRegexAlts, givenRegexListsEarly, holeMatchOpts),
    ).filter(validModulePath).sort((a, b) =>
      (pathTakenByOther(a) - pathTakenByOther(b)) ||
      byBestToWorst(a, b));
  }
  {
    const givenStemLists = givenAltListsEmit.filter((g) => !g.canonSkip).map((g) => g.alts || []);
    const consistent = consistentSuggestionPaths(
      section,
      implyAltsEmit,
      givenStemLists,
      implyRegexAlts,
      givenRegexListsEarly,
      { optionalFlags: givenOptionalFlags, cap: PATH_CAP },
    ).filter(validModulePath);
    suggestions = uniq([...suggestions, ...consistent]).filter((p) => !hasQuantEqSlash(p) && !unfilledHolePiece(p)).sort((a, b) =>
      (pathTakenByOther(a) - pathTakenByOther(b)) ||
      (preferCanon ? (b === relPath) - (a === relPath) : 0) ||
      byBestToWorst(a, b));
  }
  const suggestionsHoleMatch = suggestions.map((p) =>
    suggestionPathMatchesHoles(p, implyRegexAlts, givenRegexListsEarly, holeMatchOpts),
  );
  const moduleName = relPath.replace(/\.lean$/, "").split(/[/\\]/).join(".");
  const firstSuggestion = suggestions[0] || relPath.replace(/\\/g, "/");
  const pathOrderHyps = pathOrderHypsEarly;
  const uniqTokens = (xs) => [...new Set((xs || []).filter(Boolean).map((x) => String(x)))];
  const tokensMatching = (reSource, candidates, pad) => {
    if (!reSource) return [];
    const src = typeof reSource === "object" ? String(reSource.regex || reSource.expr || "") : String(reSource);
    const p = pad == null ? holeRegexTrailingPad(reSource) : pad;
    const toks = uniqTokens(candidates).filter((t) => !unfilledHolePiece(t) && consistent(t, src, p));
    toks.sort((a, b) => (b.length - a.length) || (a < b ? -1 : a > b ? 1 : 0));
    return toks;
  };
  const implyAltStems = uniqTokens(implyAlts).map((a) => sanitizeRelPath(String(a)));
  const implyHoleStems = uniqTokens([
    ...holeFillStems(sig.implyStmts, nameOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
    ...holeFillStemsEqMulS(sig.implyStmts, nameOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
    ...implyRegexAlts.flatMap((re) => holeRegexLanguageTokens(re || "")),
    implyStemFromRelPath(currentNorm),
  ]);
  const implyCandidates = uniqTokens([
    ...implyHoleStems,
    ...implyAltStems.map((stem) => {
      const flat = stem.includes("/of/") ? stem.slice(0, stem.indexOf("/of/")) : stem;
      return flat.includes("/") ? (implyStemFromRelPath(section + "/" + flat + ".lean") || flat) : flat;
    }),
    implyPath,
  ]);
  const implyOut = implyRegexAlts.map((re) => {
    const src = re || "_";
    const pad = holeRegexTrailingPad(src);
    let toks = tokensMatching(src, implyCandidates, pad);
    return { token: toks, regex: src, pad };
  });
  if (!implyOut.length) implyOut.push({ token: [], regex: implyHoleRegex || "_", pad: holeRegexTrailingPad(implyHoleRegex || "_") });
  const givensOut = pathOrderHyps.map((h, i) => {
    const gList = (canonGivenLists[i] || givenAltLists[i] || {});
    const givenOpts = { ...nameOpts, asGiven: true };
    const regexes = holeRegexAlternatives(h.typeNode, givenOpts);
    const ofStemI = ofStemsFromRelPath(currentNorm)[i];
    const holeStems = uniqTokens([
      ...holeFillStems(h.typeNode, givenOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
      ...holeFillStemsPlural(h.typeNode, givenOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
      ...holeFillStems(h.typeNode, { ...givenOpts, mulBothHolesBare: true }).filter(Boolean).map((s) => sanitizePathSeg(s)),
      ...holeFillStemsImpEqS(h.typeNode, givenOpts).filter(Boolean).map((s) => sanitizePathSeg(s)),
      ...regexes.flatMap((re) => holeRegexLanguageTokens(re || "")),
      ...(ofStemI ? [ofStemI] : []),
    ]);
    const alts = uniqTokens([
      (givenNames[i] && givenNames[i].name) || "",
      ...holeStems,
      ...(gList.alts || []),
      ...(gList.extraAlts || []),
    ]);
    return regexes.map((re) => {
      const src = re || "_";
      const pad = holeRegexTrailingPad(src);
      return {
        token: tokensMatching(src, alts, pad),
        regex: src,
        pad,
        lean: strStmt(h.typeNode),
        node: h.typeNode,
      };
    });
  });
  const result = {
    path: currentNorm,
    section,
    implyLean: strStmt(sig.implyStmts),
    implyNode: sig.implyStmts,
    implyOpts: nameOpts,
    imply: implyOut,
    givens: givensOut,
    suggestions,
    file: abs,
    currentPath: currentNorm,
    moduleName,
    sectionScore: picked.score,
    sectionTokens: picked.tokens,
    implyHoleRegex,
    implyHolePad: holeRegexTrailingPad(implyHoleRegex || ""),
    suggestionsHoleMatch,
    implyChain: implyChain,
givensLeanOrder: hyps.map((h) => ({ binder: h.name, prop: h.prop, name: maxLogProbJointGiven(h.typeNode, logJointFns)?.name || bvarAllLt0ProbJointName(h.typeNode) || neProbJoint0GivenName(h.typeNode) || allNeProb0GivenName(h.typeNode) || nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) })),
    givensPathOrder: givenNames,
    warnings: [],
  };
  if (Array.isArray(options.probe)) result.probe = options.probe.map((p) => altMatch(p));
  if (sectionFree) result.warnings.push(`no section evidence (no data-type token): ${section} is the repo default for generic lemmas; Int/Real/Set/… are accepted too`);
  if (validSorted.length && validSorted.length < sorted.length) result.warnings.push(`${sorted.length - validSorted.length} alternative(s) dropped: not valid Lean module names`);
  if (!validModulePath(firstSuggestion)) result.warnings.push("suggestions[0] has a component that is not a valid Lean module name: " + firstSuggestion.replace(/\.lean$/, "").split("/").filter((c) => !validModuleComponent(c)).join(", "));
  if (tooLong(firstSuggestion)) {
    result.warnings.push(`suggestions[0] is ${("Lemma/" + firstSuggestion).length} chars (> ${PATH_WARN_LEN}); ` +
      "with build prefixes it may exceed Windows MAX_PATH (260) — consider shortening" +
      (suggestions.length > 1 ? `; shortest alternative (${("Lemma/" + [...suggestions].sort(byBestToWorst)[0]).length} chars): Lemma/${[...suggestions].sort(byBestToWorst)[0]}` : ""));
  }
  const danglingHole = unfilledHolePiece(result.currentPath);
  const currentHoleOk = !danglingHole && suggestionPathMatchesHoles(
    result.currentPath,
    implyRegexAlts,
    givenRegexListsEarly,
    holeMatchOpts,
  );
  const matchedSuggestion = currentHoleOk
    ? (
      suggestions.includes(result.currentPath)
        ? result.currentPath
        : altMatch(result.currentPath)
          ? result.currentPath
          : suggestions.find((s) => pathsConsistent(result.currentPath, s).ok)
    )
    : null;
  result.consistent = danglingHole
    ? {
        ok: false,
        reason: "unfilled hole: " + danglingHole,
        existing: result.currentPath,
        suggested: firstSuggestion,
      }
    : matchedSuggestion
    ? { ok: true, reason: "exact match", existing: result.currentPath, suggested: matchedSuggestion }
    : {
      ...(currentHoleOk
        ? pathsConsistent(result.currentPath, firstSuggestion)
        : {
          ok: false,
          reason: "hole regex mismatch (imply/given stem)",
          existing: result.currentPath,
          suggested: firstSuggestion,
        }),
    };
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
        suggested: firstSuggestion,
      };
      result.warnings.push("current imply path uses illegal MEq token(s): " +
        segs.filter((s) => isIllegalMeqImplySeg(s, multi) || s === "MEq").join(", "));
    }
    if (hasIllegalDistributedAddSnake(curImply)) {
      result.consistent = {
        ok: false,
        reason: "illegal Distributed/Add imply (use camel DistributedAdd)",
        existing: result.currentPath,
        suggested: firstSuggestion,
      };
      result.warnings.push("current imply path uses illegal snake Distributed/Add (prefer DistributedAdd)");
    }
    if (hasIllegalDistributedGaussianLower(result.currentPath)) {
      result.consistent = {
        ok: false,
        reason: "illegal Distributed_gaussian (use Distributed_Gaussian)",
        existing: result.currentPath,
        suggested: firstSuggestion,
      };
      result.warnings.push("current path uses lowercase Distributed_gaussian (prefer Distributed_Gaussian)");
    }
  }
  const curMod = result.currentPath.replace(/\.lean$/, "");
  const pyCounterpart = pyModuleExists(curMod);
  if (pyCounterpart) result.pyCounterpart = curMod;
  if (options.py) {
    const explicit = typeof options.py === "string" && options.py !== "auto";
    const pyName = explicit ? String(options.py).replace(/\\/g, "/").replace(/^Lemma\//, "").replace(/\.(lean|py)$/, "").replace(/\./g, "/") : pyCounterpart ? curMod : null;
    result.py = { name: pyName, source: explicit ? "flag" : "pyLink", derived: { suggestions, consistent: result.consistent } };
    if (pyName && pyName === curMod) result.consistent = { ok: true, reason: "py name", existing: result.currentPath, suggested: pyName + ".lean" };
    else if (pyName) result.consistent = { ok: false, reason: "py name mismatch: expected " + pyName, existing: result.currentPath, suggested: pyName + ".lean" };
  }
  return result;
}

function pyModuleExists(mod) {
  const base = path.join(REPO, "pyLink", "Lemma", ...String(mod).split("/"));
  try { return fs.existsSync(base + ".py") || fs.existsSync(path.join(base, "__init__.py")); } catch { return false; }
}

export {
  limitsBigOpBoundScope,
  legacyLimitsBigOpApp,
  isArgMaxMinApp,
  argMaxMinBody,
  argMaxMinTokenName,
  isArgMaxMinGetElem,
  isSupLtInfty,
  supBoundKind,
  supBoundCanon,
};

export function pathsConsistent(existing, suggested) {
  const norm = (p) =>
    String(p)
      .replace(/\\/g, "/")
      .replace(/^Lemma\//, "")
      .replace(/\.lean$/, "");
  const a = norm(existing);
  const b = norm(suggested);
  const hole = unfilledHolePiece(a) || unfilledHolePiece(b);
  if (hole) {
    return { ok: false, reason: "unfilled hole: " + hole, existing: a, suggested: b };
  }
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

const PATH_WARN_LEN = 150;

function pathBodyPenalty(p) {
  const s = String(p || "").replace(/\\/g, "/");
  let pen = 0;
  if (/(?:^|\/)Gt0(?=\/|\.lean$)/.test(s)) pen += 200;
  if (/(?:^|\/)Lt_0(?=\/|\.lean$)/.test(s)) pen += 200;
  return pen;
}
function byBestToWorst(a, b) {
  const pa = pathBodyPenalty(a), pb = pathBodyPenalty(b);
  if (pa !== pb) return pa - pb;
  const ba = Buffer.byteLength(a, "utf8");
  const bb = Buffer.byteLength(b, "utf8");
  if (ba !== bb) return ba - bb;
  return a < b ? -1 : a > b ? 1 : 0;
}

function printHuman(r) {
  console.log("path:       Lemma/" + (r.path || r.currentPath));
  console.log("current:    Lemma/" + r.currentPath);
  for (const w of r.warnings || []) console.log("warning:    " + w);
  {
    const chk = r.consistent || pathsConsistent(r.currentPath, (r.suggestions && r.suggestions[0]) || "");
    console.log("consistent: " + (chk.ok ? "yes" : "no") + (chk.ok ? "" : " (" + chk.reason + ")"));
  }
  if (r.py) console.log("py name:    " + (r.py.name ? "Lemma/" + r.py.name + " (" + r.py.source + ")" : "— (no py counterpart)") + "; derived: Lemma/" + ((r.py.derived.suggestions && r.py.derived.suggestions[0]) || "") + (r.py.derived.consistent.ok ? " (consistent)" : ""));
  else if (r.pyCounterpart) console.log("py:         pyLink/Lemma/" + r.pyCounterpart + ".py exists (use --py to keep the py name)");
  console.log("section:    " + r.section + " (score " + r.sectionScore + "; tokens: " + (r.sectionTokens.join(", ") || "—") + ")");
  console.log("suggestions (" + r.suggestions.length + ", best→worst: free paths first, then shortest ASCII bytes):");
  for (const s of r.suggestions) {
    const taken = s !== r.currentPath && fs.existsSync(path.join(LEMMA_ROOT, s));
    console.log("  - Lemma/" + s + "  [" + Buffer.byteLength(s, "utf8") + " B" + (taken ? ", taken" : "") + "]" + (("Lemma/" + s).length > PATH_WARN_LEN ? "  ⚠ long" : ""));
  }
  if (Array.isArray(r.imply)) {
    console.log("imply (" + r.imply.length + "):");
    for (const it of r.imply) {
      const toks = Array.isArray(it.token) ? it.token : [it.token];
      console.log("  - token[" + toks.length + "]: " + toks.slice(0, 12).join(" | ") + (toks.length > 12 ? " ..." : ""));
      console.log("    regex: " + (it.regex || "") + (it.pad != null ? "  pad " + it.pad : ""));
    }
  } else if (r.implyHoleRegex) {
    console.log("implyHoleRegex: " + r.implyHoleRegex);
  }
  if (Array.isArray(r.suggestionsHoleMatch)) {
    const nTrue = r.suggestionsHoleMatch.filter(Boolean).length;
    console.log("suggestionsHoleMatch: " + nTrue + "/" + r.suggestionsHoleMatch.length + " match implyHoleRegex");
  }
  if (Array.isArray(r.givens)) {
    console.log("givens (" + r.givens.length + ", path order):");
    for (const g0 of r.givens) {
      const alts = Array.isArray(g0) ? g0 : [g0];
      for (const g of alts) {
        const toks = Array.isArray(g.token) ? g.token : [g.token];
        console.log("  - token[" + toks.length + "]: " + toks.slice(0, 12).join(" | ") + (toks.length > 12 ? " ..." : ""));
        console.log("    regex: " + (g.regex || "") + (g.pad != null ? "  pad " + g.pad : ""));
      }
    }
  }
  if (r.implyChain) console.log("imply.chain: " + r.implyChain.join(" → "));
  if (Array.isArray(r.givensLeanOrder)) {
    console.log("givens (Lean order → path uses reverse):");
    for (const g of r.givensLeanOrder) console.log("  " + (g.prop ? "✓" : "·") + " " + g.binder + ": " + (g.name || "(skip)"));
  }
  if (Array.isArray(r.givensPathOrder)) {
    console.log("givensPathOrder:");
    for (const g of r.givensPathOrder) console.log("  " + g.name + "   [" + g.chain.join(" → ") + "]");
  }
}

function cli() {
  const argv = process.argv.slice(2);
  const json = argv.includes("--json");
  const table = argv.includes("--table");
  const lemmaIdx = argv.indexOf("--lemma");
  const lemmaName = lemmaIdx >= 0 ? argv[lemmaIdx + 1] : null;
  const fromIdx = argv.indexOf("--from");
  const fromPath = fromIdx >= 0 ? argv[fromIdx + 1] : null;
  let py = null;
  const pyEq = argv.find((a) => a.startsWith("--py="));
  const pyIdx = argv.indexOf("--py");
  if (pyEq) py = pyEq.slice(5) || true;
  else if (pyIdx >= 0) {
    const v = argv[pyIdx + 1];
    py = v && !v.startsWith("-") && !/\.lean$/.test(v) ? v : true;
  }
  const pyVal = typeof py === "string" ? py : null;
  const reserved = new Set([lemmaName, pyVal, fromPath].filter(Boolean));
  const file = argv.find((a) => !a.startsWith("-") && !reserved.has(a));
  if (!file) {
    console.error("Usage: node mjs/lemmaPath.mjs [--json] [--lemma <name>] [--py [<Section/Name/...>]] <path-to.lean>");
    console.error("       node mjs/lemmaPath.mjs --table [--from <statement.lean>] <Lemma/.../.lean>");
    process.exit(1);
  }
  try {
    if (table) {
      import("./implyGivenConsistencyTable.mjs").then((m) => {
        console.log(m.implyGivenConsistencyTable(file, { from: fromPath || undefined, lemma: lemmaName || undefined }));
      }).catch((e) => {
        console.error(e.message || e);
        process.exit(1);
      });
      return;
    }
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
