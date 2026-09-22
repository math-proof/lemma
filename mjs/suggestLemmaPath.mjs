/**
 * suggestLemmaPath.mjs
 * Suggest Lemma/ path from lean.js AST + README naming.
 *
 * Steps:
 *   1. Section from typeclasses/datatypes (TYPE_TO_SECTION).
 *   2. Imply from conclusion AST (root→leaf). Equality → LHS/eq/RHS.
 *   3. Prop givens same way; path order = reverse Lean order.
 *
 * Usage: node mjs/suggestLemmaPath.mjs [--json] <path-to.lean>
 *
 * Path atoms:
 *   - binder leaves (n, A, …) are holes — not emitted (same idea as pathFromStruct symbols)
 *   - `_/eq/One` collapses to `Eq_One`, then `Eq_1` (README Snake_Case; Windows-safe)
 *   - bare segment `1` alone is spelled `One` (not `/1/`) so Windows lake can build
 */
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
  Measurable: "Measure",
  Measure: "Measure",
  Kernel: "Kernel",
  ENNReal: "ENNReal",
  NNReal: "ENNReal",
  Real: "Real",
  Complex: "Complex",
  Nat: "Nat",
  Int: "Int",
  Rat: "Rat",
  Fin: "Fin",
  Finset: "Finset",
  List: "List",
  Set: "Set",
  Filter: "Filter",
  Matrix: "Matrix",
  Tensor: "Tensor",
  Vector: "Vector",
  Bool: "Bool",
  Hyperreal: "Hyperreal",
  ZMod: "ZMod",
};

const DATA_TYPE_SECTIONS = new Set(Object.values(TYPE_TO_SECTION));

const CLASS_TOKEN = {
  Lean_exists: "Any",
  Lean_forall: "All",
  Lean_eq: "Eq",
  LeanEq: "Eq",
  Lean_ne: "Ne",
  LeanNe: "Ne",
  Lean_lt: "Lt",
  Lean_gt: "Gt",
  Lean_le: "Le",
  Lean_ge: "Ge",
  Lean_iff: "Iff",
  Lean_and: "And",
  Lean_or: "Or",
  Lean_lnot: "Not",
  Lean_not: "Not",
  LeanSub: "Sub",
  LeanAdd: "Add",
  LeanMul: "Mul",
  LeanDiv: "Div",
  LeanNeg: "Neg",
  LeanPow: "Pow",
  LeanDvd: "Dvd",
  Lean_dvd: "Dvd",
  Lean_in: "In",
  LeanIn: "In",
  LeanInf: "Inf",
  Lean_iInf: "Inf",
};

function cls(n) { return n?.constructor?.name || ""; }

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

function pickSection(sigNode, sections) {
  const tokens = collectTokens(sigNode);
  const depths = sectionDepths(sigNode);
  const candidates = [...new Set([...sections, ...DATA_TYPE_SECTIONS])];
  const scores = new Map(candidates.map((s) => [s, 0]));
  for (const t of tokens) {
    const sec = TYPE_TO_SECTION[t];
    if (sec && scores.has(sec)) scores.set(sec, scores.get(sec) + (t === sec ? 3 : 1));
  }
  if (tokens.has("AbsoluteValue") && scores.has("AbsoluteValue"))
    scores.set("AbsoluteValue", scores.get("AbsoluteValue") + 5);
  if (tokens.has("List") && scores.has("List")) scores.set("List", scores.get("List") + 2);
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
  return { section: best, score: scores.get(best) ?? 0, tokens: [...tokens].sort() };
}

function isPropHyp(typeNode) {
  if (!typeNode) return false;
  const name = cls(typeNode);
  if (["Lean_forall","Lean_exists","Lean_lt","Lean_gt","Lean_le","Lean_ge","Lean_eq","LeanEq","Lean_ne","LeanNe","Lean_iff","Lean_and","Lean_or","Lean_lnot","Lean_not"].includes(name)) return true;
  if (name === "LeanArgsSpaceSeparated") {
    const head = typeNode.args?.[0];
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

function nameToken(text) {
  if (!text) return "";
  let s = String(text);
  if (s.includes(".")) s = s.slice(s.lastIndexOf(".") + 1);
  if (!s || s === "[anonymous]" || s === "anonymous" || s === "_") return "";
  if (TOKEN_ALIAS[s] !== undefined) return TOKEN_ALIAS[s];
  const c = s.charAt(0).toUpperCase() + s.slice(1);
  return TOKEN_ALIAS[c] !== undefined ? TOKEN_ALIAS[c] : c;
}



/** Binder names that must not appear as path atoms (holes / `_`). */
function collectLeafBinders(node, out = new Set()) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  // {x : T} or (h : P)
  if (name === "LeanBrace" || name === "LeanParenthesis") {
    const colon = node.args?.[0];
    if (cls(colon) === "LeanColon" && cls(colon.args?.[0]) === "LeanToken") {
      const t = colon.args[0].text;
      if (t) out.add(t);
    }
  }
  // ∀ a ∈ A, ... / ∃ a ∈ A, ...
  if (name === "Lean_forall" || name === "Lean_exists") {
    const head = node.args?.[0];
    if ((cls(head) === "Lean_in" || cls(head) === "LeanIn") && cls(head.args?.[0]) === "LeanToken") {
      const t = head.args[0].text;
      if (t) out.add(t);
    }
    // bare ∀ j, ... / ∃ j, ... (binder token then body)
    if (cls(head) === "LeanToken" && head.text) out.add(head.text);
    if (cls(head) === "LeanColon" && cls(head.args?.[0]) === "LeanToken" && head.args[0].text) {
      out.add(head.args[0].text);
    }
  }
  for (const a of node.args || []) collectLeafBinders(a, out);
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
 * Same rule as pathFromStruct.mjs (nat literal 1 → One).
 */
function sanitizePathSeg(seg) {
  return seg === "1" ? "One" : seg;
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

/**
 * Rough lean.js path atom(s). Offline fallback for phase-1 scaffolding;
 * precise alts live in pathFromStruct / suggestFromLean.
 */
function nameExpr(node, opts = {}) {
  if (!node) return "";
  const name = cls(node);

  if (CLASS_TOKEN[name]) {
    const tag = CLASS_TOKEN[name];
    const args = node.args || [];
    if (name === "Lean_exists" || name === "Lean_forall") {
      const body = nameExpr(args[args.length - 1], opts);
      return body ? tag + "_" + body : tag;
    }
    if (name === "Lean_lnot" || name === "Lean_not") {
      const body = nameExpr(args[args.length - 1], opts);
      return body ? "Not" + body : "Not";
    }
    if (name === "Lean_and" || name === "Lean_or") {
      const left = nameExpr(args[0], opts);
      const right = nameExpr(args[1], opts);
      const join = name === "Lean_and" ? "And" : "Or";
      if (left && right) return left + join + right;
      return left || right || join;
    }
    // Relations: Left/tag/Right, or Snake F_Y when one side is a hole (binder leaf).
    // `_/eq/One` → Eq_One → Eq_1; `L1Norm/gt/0` → L1Norm/Gt_0 (repo Gt_0 atom)
    const left = nameExpr(args[0], opts);
    const right = nameExpr(args[1], opts);
    const soft = tag.toLowerCase();
    if (left && right) {
      // ‖ofL1 …‖ > 0 → GtNormOfL1_0 (README: Gt_0 with Camel NormOfL1 in the hole)
      if (right === "0" && soft === "gt" && (left === "L1Norm" || left === "NormOfL1")) {
        return "GtNormOfL1_0";
      }
      if (right === "0" && (soft === "gt" || soft === "lt")) {
        return left + "/" + (soft === "gt" ? "Gt_0" : "Lt_0");
      }
      return left + "/" + soft + "/" + right;
    }
    if (!left && right) return snakeFocus(tag, right);
    if (left && !right) return snakeFocus(tag, left);
    return tag;
  }

  // ‖ofL1 …‖ → NormOfL1 (README Camel: Norm (ofL1 ·)); L1Norm.eq.* paths stay hand-named
  if (name === "LeanNorm") {
    const arg = node.args?.[0];
    if (cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken" && arg.args[0].text === "ofL1") {
      return "NormOfL1";
    }
    const inner = nameExpr(arg, opts);
    return inner ? "Norm_" + inner : "Norm";
  }

  if (name === "LeanToken") {
    const raw = node.text || "";
    if (opts.leaves?.has(raw)) return ""; // binder leaf → hole
    if (raw === "1") return "One"; // intermediate; snakeFocus / sanitizePathSeg finalize
    if (/^-?\d+$/.test(raw)) return raw; // keep 0 etc.
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
    // AST fallback only: Lean JSON (suggestFromLean) owns const vs method.
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
  if (name === "Lean_fun" || name === "LeanRightarrow") {
    const body = node.args?.[node.args.length - 1];
    const bodyName = nameExpr(body, opts);
    if (name === "LeanRightarrow") return bodyName;
    if (!bodyName) return "Fun";
    return bodyName.startsWith("Fun") ? bodyName : "Fun" + bodyName;
  }
  if (name === "LeanArgsSpaceSeparated") {
    const args = node.args || [];
    const head = args[0];
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
    if (cls(last) === "LeanParenthesis" && cls(last.args?.[0]) === "LeanSub") return "UFnSub";
    if (cls(head) === "LeanProperty") {
      const method = nameExpr(head, opts);
      const argNames = args.slice(1).map((a) => nameExpr(a, opts)).filter(Boolean);
      // FlatMap (Fun...) -> FlatMap_Fun... ; Product (Cons) -> ProductCons
      if (method && argNames.length === 1) {
        const arg = argNames[0];
        if (arg.startsWith("Fun")) return method + "_" + arg;
        return method + arg;
      }
      if (method && argNames.length === 0) return method;
      if (method && argNames.length > 1) return method + "_" + argNames.join("");
    }
    if (cls(head) === "LeanToken") {
      const headName = opts.leaves?.has(head.text) ? "" : nameToken(head.text || "");
      const argNames = args.slice(1).map((a) => nameExpr(a, opts)).filter(Boolean);
      if (headName && argNames.length === 1) {
        const arg = argNames[0];
        if (arg.startsWith("Fun")) return headName + "_" + arg;
        return headName + arg;
      }
      if (headName && argNames.length === 0) return headName;
      if (headName && argNames.length > 1) return headName + "_" + argNames.join("");
    }
    const named = args.map((a) => nameExpr(a, opts)).filter(Boolean);
    if (named.length === 0) return "";
    if (named.length === 1) return named[0];
    return named.join("");
  }
  if (name === "LeanStatements") {
    const expr = (node.args || []).find((a) => cls(a) !== "LeanLineComment");
    return nameExpr(expr, opts);
  }
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg") {
    const tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanNeg") {
      const body = nameExpr(args[0], opts);
      return body ? "Neg" + body : "Neg";
    }
    const left = nameExpr(args[0], opts);
    const right = nameExpr(args[1], opts);
    if (left && right) return tag + left + right;
    return left || right || tag;
  }
  if (Array.isArray(node.args)) {
    for (const a of node.args) { const n = nameExpr(a, opts); if (n) return n; }
  }
  return "";
}

function classChain(node, out = []) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  if (CLASS_TOKEN[name] || name === "LeanEq" || name === "LeanConstruct" || name === "LeanProperty") out.push(name);
  else if (name === "LeanToken" && node.text && /^[A-Z]/.test(node.text)) out.push("Token:" + node.text);
  if (name === "Lean_exists" || name === "Lean_forall") { classChain(node.args?.[node.args.length - 1], out); return out; }
  if (name === "LeanEq" || name === "Lean_eq" || name === "Lean_lt" || name === "LeanSub") {
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
  if (name === "LeanParenthesis" || name === "LeanStatements") {
    classChain(node.args?.[0] || node.args?.find((a) => cls(a) !== "LeanLineComment"), out); return out;
  }
  if (name === "Lean_lnot" || name === "Lean_not" || name === "Lean_fun" || name === "LeanRightarrow") {
    classChain(node.args?.[node.args.length - 1], out); return out;
  }
  if (Array.isArray(node.args)) for (const a of node.args) classChain(a, out);
  return out;
}

function extractLemma(ast) { return (ast.args || []).find((a) => cls(a) === "Lean_lemma"); }

function extractSignature(lemma) {
  const outerAssign = (lemma.args || []).find((a) => cls(a) === "LeanAssign");
  if (!outerAssign) return null;
  const nested = (outerAssign.args || []).find((a) => cls(a) === "LeanAssign");
  const colon = (nested?.args || []).find((a) => cls(a) === "LeanColon") || (outerAssign.args || []).find((a) => cls(a) === "LeanColon");
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
    if (cls(a) !== "LeanParenthesis") continue;
    const colon = a.args?.[0];
    if (cls(colon) !== "LeanColon") continue;
    const binder = colon.args?.[0];
    const typeNode = colon.args?.[1];
    hyps.push({ name: binder?.text || "", typeNode, prop: isPropHyp(typeNode) });
  }
  return hyps;
}

export function suggest(filePath) {
  const abs = path.resolve(filePath);
  const source = fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const ast = compile(source);
  const lemma = extractLemma(ast);
  if (!lemma) throw new Error("No Lean_lemma found");
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  const sections = existingSections();
  const picked = pickSection(sig.colon, sections);
  const leaves = collectLeafBinders(lemma);
  const nameOpts = { leaves };
  const implyName = nameExpr(sig.implyStmts, nameOpts) || "Imply";
  const implyChain = classChain(sig.implyStmts);
  const hyps = extractGivens(sig.nls);
  const givenNames = [...hyps.filter((h) => h.prop)].reverse().map((h) => ({
    binder: h.name,
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given",
    chain: classChain(h.typeNode),
  }));
  const givenPath = givenNames.map((g) => sanitizeRelPath(g.name)).join("/");
  const implyPath = sanitizeRelPath(implyName);
  const relPath = sanitizeRelPath(
    givenPath
      ? picked.section + "/" + implyPath + "/of/" + givenPath + ".lean"
      : picked.section + "/" + implyPath + ".lean",
  );
  const moduleName = relPath.replace(/\.lean$/, "").split(/[/\\]/).join(".");
  let relCurrent = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
  if (relCurrent.startsWith("..")) relCurrent = path.relative(REPO, abs).replace(/\\/g, "/");
  const result = {
    file: abs,
    currentPath: relCurrent.startsWith("Lemma/") ? relCurrent.slice(6) : relCurrent,
    suggestedPath: relPath.replace(/\\/g, "/"),
    moduleName,
    section: picked.section,
    sectionScore: picked.score,
    sectionTokens: picked.tokens,
    imply: { name: implyPath, chain: implyChain },
    givensLeanOrder: hyps.map((h) => ({ binder: h.name, prop: h.prop, name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) })),
    givensPathOrder: givenNames,
  };
  result.consistent = pathsConsistent(result.currentPath, result.suggestedPath);
  return result;
}

/** Structural path segments (connectives), compared exactly. */
const STRUCT_SEGS = new Set([
  "eq", "ne", "is", "as", "of", "ae", "et", "ou", "lt", "gt", "le", "ge",
  "in", "to", "dvd", "sub", "sup", "ll", "gg",
]);

/**
 * Are two content segments structurally consistent?
 * - exact match
 * - underscore-insensitive (ProductCons ~ Product_Cons)
 * - underscore-atom prefix either way
 *   (FlatMap_FunMapProduct ~ FlatMap_FunMapProduct_FunCons)
 */
function segmentsConsistent(a, b) {
  if (!a || !b) return a === b;
  if (a === b) return true;
  // bare digit 1 vs One (Windows-safe spelling)
  if ((a === "1" && b === "One") || (a === "One" && b === "1")) return true;
  if (a.replace(/_/g, "") === b.replace(/_/g, "")) return true;
  const ap = a.split("_").filter(Boolean);
  const bp = b.split("_").filter(Boolean);
  const prefix = (x, y) => x.length <= y.length && x.every((v, i) => v === y[i]);
  return prefix(ap, bp) || prefix(bp, ap);
}

/**
 * Does `existing` lemma path match the structure of `suggested`?
 * Paths need not be identical; content segments may refine each other.
 * Returns { ok, reason, existing, suggested }.
 */
export function pathsConsistent(existing, suggested) {
  const norm = (p) =>
    String(p)
      .replace(/\\/g, "/")
      .replace(/^Lemma\//, "")
      .replace(/\.lean$/, "")
      .split("/")
      .filter(Boolean);
  const a = norm(existing);
  const b = norm(suggested);
  if (a.length === 0 || b.length === 0) {
    return { ok: false, reason: "empty path", existing: a, suggested: b };
  }
  if (a[0] !== b[0]) {
    return { ok: false, reason: "section mismatch: " + a[0] + " vs " + b[0], existing: a, suggested: b };
  }
  let i = 1;
  let j = 1;
  while (i < a.length || j < b.length) {
    const sa = a[i];
    const sb = b[j];
    if (sa === undefined || sb === undefined) {
      if (sa !== undefined && STRUCT_SEGS.has(sa)) {
        return { ok: false, reason: "extra structural segment in existing: " + sa, existing: a, suggested: b };
      }
      if (sb !== undefined && STRUCT_SEGS.has(sb)) {
        return { ok: false, reason: "extra structural segment in suggested: " + sb, existing: a, suggested: b };
      }
      break;
    }
    const aStruct = STRUCT_SEGS.has(sa);
    const bStruct = STRUCT_SEGS.has(sb);
    if (aStruct || bStruct) {
      if (sa !== sb) {
        return { ok: false, reason: "structural mismatch at " + i + "/" + j + ": " + sa + " vs " + sb, existing: a, suggested: b };
      }
      i++;
      j++;
      continue;
    }
    if (!segmentsConsistent(sa, sb)) {
      return { ok: false, reason: "content mismatch: " + sa + " vs " + sb, existing: a, suggested: b };
    }
    i++;
    j++;
  }
  return { ok: true, reason: "consistent", existing: a, suggested: b };
}

function printHuman(r) {
  console.log("current:    Lemma/" + r.currentPath);
  console.log("suggested:  Lemma/" + r.suggestedPath);
  {
    const chk = r.consistent || pathsConsistent(r.currentPath, r.suggestedPath);
    console.log("consistent: " + (chk.ok ? "yes" : "no") + (chk.ok ? "" : " (" + chk.reason + ")"));
  }
  console.log("module:     " + r.moduleName);
  console.log("section:    " + r.section + " (score " + r.sectionScore + "; tokens: " + (r.sectionTokens.join(", ") || "—") + ")");
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
  const file = argv.find((a) => !a.startsWith("-"));
  if (!file) {
    console.error("Usage: node mjs/suggestLemmaPath.mjs [--json] <path-to.lean>");
    process.exit(1);
  }
  try {
    const result = suggest(file);
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
