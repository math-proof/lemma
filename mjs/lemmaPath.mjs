import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import { compile } from "../js/parser/lean.js";
import { loadSectionKindMap } from "./lemmaSectionKind.mjs";
import { json2pathPatterns, suggestionMatches } from "../js/parser/lean/json2regex.js";

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

const CLASS_ANCESTOR_CACHE = new Map();

function hasAncestorClass(node, ancestorName) {
  const c = cls(node);
  if (!c) return false;
  const key = c + "|" + ancestorName;
  if (CLASS_ANCESTOR_CACHE.has(key)) return CLASS_ANCESTOR_CACHE.get(key);
  let hit = false;
  for (let p = Object.getPrototypeOf(node); p; p = Object.getPrototypeOf(p)) {
    if (p.constructor?.name === ancestorName) { hit = true; break; }
  }
  CLASS_ANCESTOR_CACHE.set(key, hit);
  return hit;
}

// Any binder big-operator (`∑ ∏ ∫ ∂ ∇ ℙ 𝔼` …): its token always comes from `pathToken`.
function isBigOp(node) { return hasAncestorClass(node, "LeanBigOperator"); }

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

function subscriptedMulAtom(node) {
  if (cls(node) !== "LeanMul" || node.subscript !== "ᵥ") return null;
  return node.isLeftSubscript ? "VecMul" : "MulVec";
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
    if (cls(h) === "LeanGet") h = h.args?.[0];
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
      concl.args.every((a) => { const u = unwrapParen(a); return isBigOp(u) && (u.args || []).some((b) => cls(b) === "Lean_in"); })) {
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
        return isBigOp(u) && (u.args || []).some((b) => cls(b) === "Lean_in");
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
    cls(n) === "LeanGet" && cls(n.args?.[1]) === "LeanToken" && n.args[1].text === "X")) {
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
    if (cls(head) === "LeanGet" && cls(head.args?.[0]) === "LeanToken") head = head.args[0];

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
  Get: "Get",
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

function nameToken(text) {
  if (!text) return "";
  const t = String(text);
  const last = t.includes(".") ? t.slice(t.lastIndexOf(".") + 1) : t;
  if (SYMBOL_NAME[last] !== undefined) return SYMBOL_NAME[last];
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

function validModuleComponentBasic(c) {
  return /^[\p{L}_][\p{L}\p{N}_'!?\u2080-\u209C\u1D62-\u1D6A\u2070-\u207F]*$/u.test(c || "");
}

function setBuilderCond(n) {
  const u = unwrapParen(n);
  if (cls(u) !== "LeanBrace") return null;
  const a = u.args?.[0];
  if (cls(a) === "LeanCond") return a.args?.[1] || null;
  if (cls(a) === "LeanColon") {
    let t = a.args?.[1];
    while (t && cls(t) !== "LeanCond" && (cls(t) === "Lean_rightarrow" || cls(t) === "LeanArgsSpaceSeparated")) t = t.args?.[t.args.length - 1];
    if (cls(t) === "LeanCond") return t.args?.[1] || null;
  }
  return null;
}

function isSetBuilder(n) { return !!setBuilderCond(n); }

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
  if (cls(u) === "LeanCond" && cls(stripIndepWrap(u.args?.[0])) === "Lean_perp") return "CondIndep";
  return "";
}

function unwrapParen(node) {
  let n = node;
  while (cls(n) === "LeanParenthesis") n = n.args?.[0];
  return n;
}

function isSfBvarText(text) {
  return /^\\sf\{\w\}$/.test(text || "") || /^«\\sf\{\w\}»$/.test(text || "");
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

function firstConclusion(node) {
  const args = node?.args || [];
  const meaningful = args.filter((a) => {
    const c = cls(a);
    return c && c !== "LeanLineComment" && c !== "Lean_have" && c !== "Lean_let";
  });
  if (meaningful.length) return meaningful[meaningful.length - 1];
  return args.filter((a) => cls(a) !== "LeanLineComment").pop() || null;
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
  const isGivenMarker = (a) => cls(a) === "LeanLineComment" && /given/i.test(a.text || "");
  let pastGiven = !args.some(isGivenMarker);
  const hyps = [];
  for (const a of args) {
    if (isGivenMarker(a)) { pastGiven = true; continue; }
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

function readPathSignature(filePath, lemmaName, options) {
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
  const givens = extractGivens(sig.nls ?? sig.colon.args[0])
    .filter((h) => h.prop || expressionRelation(h.typeNode));
  const givenTypeNodes = givens.map((h) => h.typeNode);
  const currentCustom = nonDataFolder(curTop) ? customSection(sections, sig.implyStmts, givenTypeNodes, importSections(source, sections), sig.indented) : null;
  const keepCurrentCustom = !!currentCustom && nonDataFolder(currentCustom) && curTop === currentCustom;
  const custom = keepCurrentCustom ? currentCustom : customSection(dataSections, sig.implyStmts, givenTypeNodes, importSections(source, dataSections), sig.indented);
  const picked = pickSection(sig.colon, keepCurrentCustom ? sections : dataSections, {
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
  return { sig, section, givens };
}

const EXPRESSION_RELATIONS = new Map([
  ["=", "eq"], ["<", "lt"], ["≤", "le"], [">", "gt"], ["≥", "ge"],
  ["≠", "ne"], ["↔", "is"], ["∈", "in"], ["∨", "ou"], ["≃", "as"],
  ["≪", "ll"], ["≫", "gg"],
]);

const EXPRESSION_RELATION_TOKENS = new Set([...EXPRESSION_RELATIONS.values(), "ae"]);

function expressionRelation(node) {
  const expr = unwrapParen(node);
  if (expr?.args?.length !== 2) return null;
  if (expr.operator === "=" && expr.superscript === "ᵐ") return "ae";
  return expr.superscript ? null : EXPRESSION_RELATIONS.get(expr.operator) ?? null;
}

function expressionPathPart(node) {
  const expr = unwrapParen(node);
  const relation = expressionRelation(expr);
  const json = expr.toJSON();
  const patterns = json2pathPatterns(relation === "ae" && json.Eq ? { MEq: json.Eq } : json);
  let token = "";
  for (const pattern of patterns) {
    const candidate = pattern.token;
    if (validModuleComponentBasic(candidate) && (!token || candidate.length < token.length)) token = candidate;
  }
  return { node: expr, token, patterns };
}

/** Suggest a dotted lemma path using the base and plural expression DAGs. */
export function suggestExpressionPath(filePath, lemmaName, options = {}) {
  const { sig, section, givens } = readPathSignature(filePath, lemmaName, options);
  const conclusion = conclusionNode(sig.colon);
  if (!conclusion) throw new Error("Could not find the lemma conclusion");
  const implyParts = (splitTopConjunction(conclusion, true) ?? [conclusion]).map((node) => {
    const expr = unwrapParen(node);
    const flat = expressionPathPart(expr);
    const relation = expressionRelation(expr);
    if (!relation) return { flat };
    const [left, right] = expr.args.map(expressionPathPart);
    return { flat, relation, left, right };
  });
  const givenParts = [...givens].reverse().map(({ name, typeNode }) => ({
    name,
    ...expressionPathPart(typeNode),
  }));
  const imply = implyParts.map(({ flat, relation, left, right }) => {
    const split = left?.token && right?.token ? [left.token, relation, right.token].join(".") : "";
    const token = split && (!flat.token || split.length < flat.token.length)
      ? split : flat.token;
    if (!token) throw new Error("Could not generate a path token for a conclusion");
    return token;
  }).join(".");
  const givenTokens = givenParts.map(({ name, token }) => {
    if (!token) throw new Error(`Could not generate a path token for hypothesis ${name}`);
    return token;
  });
  return {
    section, imply, givens: givenTokens.join("."),
    path: [section, imply, ...(givenTokens.length ? ["of", ...givenTokens] : [])].join("."),
    implyParts, givenParts,
  };
}

function expressionPathSegments(candidate) {
  const normalized = String(candidate).replace(/\\/g, "/");
  const relative = path.isAbsolute(normalized) ? path.relative(LEMMA_ROOT, normalized) : normalized;
  return relative.replace(/\.lean$/, "").replace(/^Lemma[./]/, "").split(/[./]/);
}

/** Render `{ token, regex, ok, lean }` rows as the four-column markdown table. */
function renderTable(rows) {
  const cell = (value) => String(value ?? "—").replace(/\|/g, "\\|").replace(/[\r\n]+/g, " ");
  return [
    "| token | regex | verdict | lean |",
    "| --- | --- | --- | --- |",
    ...rows.map(({ token, regex, ok, lean }) =>
      `| ${cell(token)} | ${cell(regex)} | ${ok ? "√" : "×"} | ${cell(lean)} |`),
  ].join("\n");
}

/** Check a dotted or filesystem lemma path against the parsed statement. */
export function checkExpressionPath(filePath, candidate, lemmaName, options = {}) {
  const suggestion = suggestExpressionPath(filePath, lemmaName, options);
  const [section, ...parts] = expressionPathSegments(candidate);
  const of = parts.indexOf("of");
  const imply = of < 0 ? parts : parts.slice(0, of);
  const givens = of < 0 ? [] : parts.slice(of + 1);
  const rows = [];
  const lean = (node) => String(node ?? "").replace(/\s+/g, " ").trim();
  const row = (part, token, regex, ok, node) => rows.push({ part, token, regex, ok, lean: lean(node) });
  const match = (part, token, expression) => {
    const patterns = expression?.patterns ?? [];
    const hit = patterns.find(({ regex }) => suggestionMatches(regex, token));
    row(part, token, (hit ?? patterns[0])?.regex, !!hit, expression?.node);
  };
  // The section and the `eq` / `of` markers are part of the path but not rows;
  // they still take part in the verdict (reported below the table when wrong).
  const notes = [];
  let ok = section === suggestion.section;
  if (!ok) notes.push(`section "${section}" ≠ "${suggestion.section}"`);
  let index = 0;
  suggestion.implyParts.forEach(({ flat, relation, left, right }, i) => {
    const label = `Conclusion ${i + 1}`;
    if (relation && EXPRESSION_RELATION_TOKENS.has(imply[index + 1])) {
      match(label + " LHS", imply[index++], left);
      const got = imply[index++];
      if (got !== relation) { ok = false; notes.push(`relation "${got}" ≠ "${relation}"`); }
      match(label + " RHS", imply[index++], right);
    } else {
      match(label, imply[index++], flat);
    }
  });
  for (const token of imply.slice(index)) row("Extra conclusion", token, undefined, false);
  if (suggestion.givenParts.length ? of < 0 : of >= 0) {
    ok = false;
    notes.push(suggestion.givenParts.length ? 'missing "of"' : 'unexpected "of"');
  }
  for (let i = 0; i < Math.max(givens.length, suggestion.givenParts.length); i++) {
    const expected = suggestion.givenParts[i];
    match(expected ? `Given ${i + 1} (${expected.name})` : "Extra given", givens[i], expected);
  }
  const table = [
    renderTable(rows),
    ...(notes.length ? ["", `× ${notes.join("; ")}`] : []),
  ].join("\n");
  return { ok: ok && rows.every((entry) => entry.ok), path: suggestion.path, rows, notes, table };
}

/**
 * Check a *proposed* dotted path against each top-level semantic unit (conclusion
 * LHS / RHS and every given) of the parsed statement.
 *
 * The first segment is the root/namespace and `eq` / `of` are connective markers:
 * none of them is a row. A unit is consistent only when its segment matches one of
 * the regexes its Lean expression yields as a whole.
 */
export function checkProposedPath(filePath, candidate, lemmaName, options = {}) {
  const suggestion = suggestExpressionPath(filePath, lemmaName, options);
  const [, ...proposed] = expressionPathSegments(candidate);
  const of = proposed.indexOf("of");
  const implySegments = of < 0 ? proposed : proposed.slice(0, of);
  const givenSegments = of < 0 ? [] : proposed.slice(of + 1);
  const rows = [];
  let index = 0;
  const lean = (part) => String(part?.node ?? "").replace(/\s+/g, " ").trim();

  const addRow = (segment, part, label) => {
    const patterns = part?.patterns ?? [];
    if (!segment) {
      rows.push({
        token: "(missing)", lean: lean(part), regex: patterns[0]?.regex, ok: false,
        mode: "missing", detail: `missing ${label} segment`,
      });
      return;
    }
    const whole = patterns.find(({ regex }) => suggestionMatches(regex, segment));
    if (whole) {
      rows.push({ token: segment, lean: lean(part), regex: whole.regex, ok: true, mode: "whole" });
      return;
    }
    rows.push({ token: segment, lean: lean(part), regex: patterns[0]?.regex, ok: false, mode: "no" });
  };
  const surplus = (segment) => {
    rows.push({ token: segment, lean: "(unexpected segment)", regex: undefined, ok: false, mode: "surplus", detail: "surplus segment" });
  };

  suggestion.implyParts.forEach(({ flat, relation, left, right }, i) => {
    const label = `conclusion ${i + 1}`;
    if (relation && EXPRESSION_RELATION_TOKENS.has(implySegments[index + 1])) {
      addRow(implySegments[index++], left, label + " LHS");
      index++; // the relation marker (`eq`, `is`, …) is not a row
      addRow(implySegments[index++], right, label + " RHS");
    } else {
      addRow(implySegments[index++], flat, label);
    }
  });
  for (const segment of implySegments.slice(index)) surplus(segment);
  for (let i = 0; i < Math.max(givenSegments.length, suggestion.givenParts.length); i++) {
    const part = suggestion.givenParts[i];
    if (part) addRow(givenSegments[i], part, `given ${i + 1} (${part.name})`);
    else surplus(givenSegments[i]);
  }

  const table = renderTable(rows);
  return { ok: rows.every((entry) => entry.ok), path: suggestion.path, rows, table };
}

async function cli() {
  const options = new Map();
  let file;
  const argv = process.argv.slice(2);
  try {
    for (let i = 0; i < argv.length; i++) {
      const arg = argv[i];
      if (arg === "--json" || arg === "--table") options.set(arg, true);
      else if (arg.startsWith("--path=")) {
        const value = arg.slice("--path=".length);
        if (!value) throw new Error("--path requires a value");
        options.set("--path", value);
      } else if (arg === "--lemma" || arg === "--check" || arg === "--from" || arg === "--path") {
        const value = argv[++i];
        if (!value || value.startsWith("-")) throw new Error(`${arg} requires a value`);
        options.set(arg, value);
      } else if (arg.startsWith("-") || file) throw new Error(`Unexpected argument: ${arg}`);
      else file = arg;
    }
    if (!file) throw new Error("Usage: node mjs/lemmaPath.mjs [--json] [--lemma <name>] [--check <candidate>] [--table [--from <file>] [--path=<proposal>]] <file.lean>");
    const json = options.has("--json");
    const lemmaName = options.get("--lemma");
    if (options.has("--path")) {
      let statement = file;
      if (options.get("--from")) {
        const { resolveStatementFile } = await import("./implyGivenConsistencyTable.mjs");
        statement = resolveStatementFile(file, { from: options.get("--from") });
      }
      const report = checkProposedPath(statement, options.get("--path"), lemmaName);
      console.log(json ? JSON.stringify(report, null, 2) : report.table);
      if (!report.ok) process.exitCode = 1;
      return;
    }
    if (options.has("--check") || options.has("--table")) {
      let statement = file;
      let candidate = options.get("--check");
      if (!candidate) {
        const { resolveStatementFile } = await import("./implyGivenConsistencyTable.mjs");
        candidate = file;
        statement = resolveStatementFile(candidate, { from: options.get("--from") });
      }
      const report = checkExpressionPath(statement, candidate, lemmaName);
      console.log(json ? JSON.stringify(report, null, 2) : report.table);
      if (!report.ok) process.exitCode = 1;
      return;
    }
    if (options.has("--from")) throw new Error("--from requires --table");
    const { section, imply, givens, path: suggested } = suggestExpressionPath(file, lemmaName);
    console.log(json ? JSON.stringify({ section, imply, givens, path: suggested }, null, 2) : suggested);
  } catch (e) {
    console.error(e.message || e);
    process.exitCode = 1;
  }
}

const isMain =
  process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;

if (isMain) cli();
