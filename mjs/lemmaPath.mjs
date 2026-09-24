
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
  Lean_land: "And",
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
  // RV binders (Ω → _) / PSpace overweight Measure from {π : Measure Ω}.
  if (hasRandomAstCues(sigNode) && scores.has("Random"))
    scores.set("Random", scores.get("Random") + 5);
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
  if (["Lean_forall","Lean_exists","Lean_lt","Lean_gt","Lean_le","Lean_ge","Lean_eq","LeanEq","Lean_ne","LeanNe","Lean_iff","Lean_and","Lean_or","Lean_lnot","Lean_not","Lean_in","LeanIn"].includes(name)) return true;
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

function nameToken(text) {
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



/** Binder names that must not appear as path atoms (holes / `_`). */
function collectLeafBinders(node, out = new Set()) {
  if (!node || typeof node !== "object") return out;
  const name = cls(node);
  if (name === "LeanBrace" || name === "LeanParenthesis") {
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
 * Nat literal 1 is spelled One in path segments (Windows-safe).
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
  if (n === "Lean_and" || n === "Lean_land" || n === "LeanAnd") return true;
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

const GUARD_REL = new Set(["Lean_lt", "Lean_gt", "Lean_le", "Lean_ge", "Lean_in", "LeanIn"]);

function guardRestConjunct(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n || (cls(n) !== "Lean_and" && cls(n) !== "Lean_land")) return null;
  const [left, right] = n.args || [];
  if (!right) return null;
  let l = left;
  while (cls(l) === "LeanParenthesis") l = l.args?.[0];
  return GUARD_REL.has(cls(l)) ? right : null;
}

function splitTopConjunction(node) {
  let n = node;
  while (n && (cls(n) === "LeanParenthesis" || cls(n) === "LeanStatements" || cls(n) === "LeanArgsNewLineSeparated")) {
    n = cls(n) === "LeanParenthesis" ? n.args?.[0] : firstConclusion(n);
  }
  if (!n || (cls(n) !== "Lean_and" && cls(n) !== "Lean_land")) return null;
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
function nameExpr(node, opts = {}) {
  if (!node) return "";
  const name = cls(node);

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
    if (name === "Lean_exists" || name === "Lean_forall") {
      const body = nameExpr(args[args.length - 1], opts);
      if (!body) return tag;
      if (isAeQuantifier(node)) return body;
      const rest = guardRestConjunct(args[args.length - 1]);
      if (rest) {
        const restName = nameExpr(rest, opts);
        if (restName) return tag + "_And_" + restName;
      }
      if (body.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(body)) return body;
      return tag + "_" + body;
    }
    if (name === "Lean_lnot" || name === "Lean_not") {
      const body = nameExpr(args[args.length - 1], opts);
      return body ? "Not" + body : "Not";
    }
    if (name === "Lean_and" || name === "Lean_land" || name === "Lean_or") {
      const left = nameExpr(args[0], opts);
      const right = nameExpr(args[1], opts);
      const join = name === "Lean_or" ? "Or" : "And";
      if (left && right) return left + join + right;
      return left || right || join;
    }
    const left = nameExpr(args[0], opts);
    const right = nameExpr(args[1], opts);
    const soft = tag.toLowerCase();
    if (left && right) {
      if (right === "0" && (soft === "gt" || soft === "lt")) {
        return left + "/" + (soft === "gt" ? "Gt_0" : "Lt_0");
      }
      return left + "/" + soft + "/" + right;
    }
    if (!left && right) return snakeFocus(tag, right);
    if (left && !right) return snakeFocus(tag, left);
    return tag;
    } // end non-arith CLASS_TOKEN
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
    // Bare subtraction arg (|a - b|, ⌈a - b⌉, …) → OpSub
    if (cls(unwrapParen(arg)) === "LeanSub") return wrapPrefix + "Sub";
    if (cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken") {
      const fn = arg.args[0].text;
      const inner = unwrapParen(arg.args?.[1]);
      const isSub = cls(inner) === "LeanSub";
      const camelFn = nameToken(fn);
      return wrapPrefix + camelFn + (isSub ? "Sub" : "");
    }
    const inner = nameExpr(arg, opts);
    return inner ? wrapPrefix + "_" + inner : wrapPrefix;
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
    if (cls(head) === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") {
      const headName = nameExpr(head, opts);
      if (headName) {
        let acc = joinHeadChild("Get", headName);
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
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg") {
    const tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanNeg") {
      const body = nameExpr(args[0], opts);
      return body ? "Neg" + body : "Neg";
    }
    // Conditional-prob algebra idioms (Random.ProbCond_* / DivProbS*):
    //   ℙ(joint) / ℙ(cond)  → DivProbS or DivProbSCond
    //   ℙ(·|·) * ℙ(·|·)     → MulProbCond
    if (name === "LeanDiv" || name === "LeanMul") {
      const lEv = matchProbApp(args[0]);
      const rEv = matchProbApp(args[1]);
      if (lEv && rEv) {
        const ln = nameProbEvent(lEv);
        const rn = nameProbEvent(rEv);
        if (name === "LeanDiv") {
          // Repo atoms: DivProbSCond = ProbCondJoint/ProbCond (or ProbS/ProbS joint form)
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
    if (left && right) return left === right ? tag + pluralMidS(left) : tag + left + right;
    if (right) return snakeFocus(tag, right);
    if (left) return snakeFocus(tag, left);
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
  if (child.startsWith("Fun") || child.includes("_")) {
    if (!child.startsWith("Fun") && child.includes("_")) return head + child;
    return head + "_" + child;
  }
  return head + child;
}

function nameExprAlts(node, opts = {}) {
  if (!node) return [];
  const name = cls(node);

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
      if (name === "Lean_exists" || name === "Lean_forall") {
        const bodyNode = args[args.length - 1];
        const bodyAlts = nameExprAlts(bodyNode, opts);
        const rest = guardRestConjunct(bodyNode);
        const guardAlts = rest ? nameExprAlts(rest, opts).map((r) => tag + "_And_" + r) : [];
        if (!bodyAlts.length) return uniq([...guardAlts, tag]);
        if (isAeQuantifier(node)) return uniq([...bodyAlts, ...guardAlts]);
        if (bodyAlts.some(b => b.includes("/") || /^(Prob|DivProb|MulProb|Eq)/.test(b))) {
          return uniq([...bodyAlts, ...guardAlts]);
        }
        const out = [];
        for (const b of bodyAlts) {
          out.push(tag + "_" + b);
          out.push(tag + b);
        }
        return uniq([...guardAlts, ...out]);
      }
      if (name === "Lean_lnot" || name === "Lean_not") {
        const bodyAlts = nameExprAlts(args[args.length - 1], opts);
        if (!bodyAlts.length) return ["Not"];
        return bodyAlts.map(b => "Not" + b);
      }
      if (name === "Lean_and" || name === "Lean_land" || name === "Lean_or") {
        const leftAlts = nameExprAlts(args[0], opts);
        const rightAlts = nameExprAlts(args[1], opts);
        const join = name === "Lean_or" ? "Or" : "And";
        const out = [];
        // LeftJoinRight (Camel)
        for (const l of leftAlts) {
          for (const r of rightAlts) {
            out.push(l + join + r);
            out.push(l + "_" + join + "_" + r);
          }
        }
        return uniq(out);
      }
      // Equality/relation: Left/rel/Right and RelLeftRight styles
      const leftAlts = nameExprAlts(args[0], opts);
      const rightAlts = nameExprAlts(args[1], opts);
      const soft = tag.toLowerCase();
      const out = [];
      for (const l of leftAlts) {
        for (const r of rightAlts) {
          if (l && r) {
            if (r === "0" && (soft === "gt" || soft === "lt")) {
              out.push(l + "/" + (soft === "gt" ? "Gt_0" : "Lt_0"));
            }
            out.push(l + "/" + soft + "/" + r);
            out.push(tag + l + r);
            out.push(l + tag + r);
          }
        }
      }
      if (!leftAlts.length && rightAlts.length) {
        for (const r of rightAlts) {
          out.push(tag + "_" + r);
        }
      }
      if (leftAlts.length && !rightAlts.length) {
        for (const l of leftAlts) {
          out.push(tag + "_" + l);
        }
      }
      if (!leftAlts.length && !rightAlts.length) out.push(tag);
      return uniq(out);
    }
  }

  // Wrapper ops: Norm, Abs, Ceil, Floor
  const WRAP_OP_PREFIX = { LeanNorm: "Norm", LeanAbs: "Abs", LeanCeil: "Ceil", LeanFloor: "Floor" };
  const wrapPrefix = WRAP_OP_PREFIX[name];
  if (wrapPrefix !== undefined) {
    const arg = node.args?.[0];
    if (cls(unwrapParen(arg)) === "LeanSub") return [wrapPrefix + "Sub"];
    if (cls(arg) === "LeanArgsSpaceSeparated" && cls(arg.args?.[0]) === "LeanToken") {
      const fn = arg.args[0].text;
      const inner = unwrapParen(arg.args?.[1]);
      const isSub = cls(inner) === "LeanSub";
      const camelFn = nameToken(fn);
      return [wrapPrefix + camelFn + (isSub ? "Sub" : "")];
    }
    const innerAlts = nameExprAlts(arg, opts);
    if (!innerAlts.length) return [wrapPrefix];
    const out = [];
    for (const i of innerAlts) {
      out.push(wrapPrefix + "_" + i);
      out.push(wrapPrefix + i);
    }
    return uniq(out);
  }

  if (name === "LeanToken") {
    const raw = node.text || "";
    if (opts.leaves?.has(raw)) return [];
    if (raw === "1") return ["One"];
    if (/^-?\d+$/.test(raw)) return [raw];
    return [nameToken(raw)];
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
    return bodyAlts.map(b => b.startsWith("Fun") ? b : "Fun" + b);
  }

  if (name === "LeanArgsSpaceSeparated") {
    const args = node.args || [];
    const head = args[0];
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
    if (cls(last) === "LeanParenthesis" && cls(last.args?.[0]) === "LeanSub") return ["UFnSub"];

    // Matrix/vector indexing: `(M expr) i j` parses with a parenthesized
    // compound head (GetElem via coeFun) → Get + head alts; binder indices
    // are holes. (P ^ m) i k → GetPow, (P ^ (m+n)) i j → GetPow_Add.
    if (cls(head) === "LeanParenthesis" && cls(unwrapParen(head)) !== "LeanToken") {
      const headAlts = nameExprAlts(head, opts);
      if (headAlts.length) {
        const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
        let acc = cartJoin(["Get"], headAlts, joinHeadChild);
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
      for (const argAlts of argAltLists) {
        acc = cartJoin(acc, argAlts, joinHeadChild);
        all.push(...acc);
      }
      return uniq(all);
    }

    // Token head: Func(args)
    if (cls(head) === "LeanToken") {
      const headName = opts.leaves?.has(head.text) ? "" : nameToken(head.text || "");
      if (!headName) return [];
      const argAltLists = args.slice(1).map(a => nameExprAlts(a, opts)).filter(a => a.length);
      if (!argAltLists.length) return [headName];
      // Generate multiple composition styles
      let acc = [headName];
      const all = [headName];
      for (const argAlts of argAltLists) {
        acc = cartJoin(acc, argAlts, joinHeadChild);
        all.push(...acc);
      }
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
  if (name === "LeanSub" || name === "LeanAdd" || name === "LeanMul" || name === "LeanDiv" || name === "LeanPow" || name === "LeanNeg") {
    const tag = CLASS_TOKEN[name] || name.replace(/^Lean/, "");
    const args = node.args || [];
    if (name === "LeanNeg") {
      const bodyAlts = nameExprAlts(args[0], opts);
      if (!bodyAlts.length) return ["Neg"];
      return bodyAlts.map(b => "Neg" + b);
    }
    // Prob algebra idioms
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
    // TagLeftRight, LeftTagRight, LeftRightTag, etc.
    for (const l of leftAlts) {
      for (const r of rightAlts) {
        if (l && r) {
          if (l === r) {
            out.push(tag + pluralMidS(l));
            out.push(tag + sameChildS(l));
          }
          out.push(tag + l + r);
          out.push(l + tag + r);
          out.push(l + r + tag);
          out.push(l + "_" + tag + "_" + r);
        }
      }
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
    if (cls(a) !== "LeanParenthesis") continue;
    const colon = a.args?.[0];
    if (cls(colon) !== "LeanColon") continue;
    const binder = colon.args?.[0];
    const typeNode = colon.args?.[1];
    hyps.push({ name: binder?.text || "", typeNode, prop: isPropHyp(typeNode) });
  }
  return hyps;
}

export function suggest(filePath, lemmaName) {
  const abs = path.resolve(filePath);
  const source = fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const ast = compile(source);
  const lemma = extractLemma(ast, lemmaName);
  if (!lemma) throw new Error("No Lean_lemma found");
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  const sections = existingSections();
  const picked = pickSection(sig.colon, sections);
  const section = picked.section;
  let relCurrent = path.relative(LEMMA_ROOT, abs).replace(/\\/g, "/");
  if (relCurrent.startsWith("..")) relCurrent = path.relative(REPO, abs).replace(/\\/g, "/");
  const leaves = collectLeafBinders(lemma);
  const nameOpts = { leaves };
  const implyAlts = (() => {
    const joined = nameExprAlts(sig.implyStmts, nameOpts).filter(Boolean);
    const parts = splitTopConjunction(sig.implyStmts);
    if (!parts || parts.length < 2) return joined;
    const perConjunct = parts.map((p) => nameExprAlts(p, nameOpts).filter(Boolean));
    if (!perConjunct.every((a) => a.length)) return joined;
    const splitAlts = perConjunct.reduce(
      (acc, a) => acc.flatMap((pfx) => a.map((x) => (pfx ? pfx + "/" + x : x))),
      [""],
    );
    return uniq([...splitAlts, ...joined]);
  })();
  const implyName = implyAlts[0] || "Imply";
  const implyChain = classChain(sig.implyStmts);
  const hyps = extractGivens(sig.nls);
  // Generate ALL given name alternatives (reverse order for path)
  const givenAltLists = [...hyps.filter((h) => h.prop)].reverse().map((h) => ({
    binder: h.name,
    alts: nameExprAlts(h.typeNode, { ...nameOpts, asGiven: true }).filter(Boolean),
    name: nameExpr(h.typeNode, { ...nameOpts, asGiven: true }) || "Given",
    chain: classChain(h.typeNode),
  }));
  const givenNames = givenAltLists.map((g) => ({ binder: g.binder, name: g.name, chain: g.chain }));
  // Cartesian product of given alternatives
  function cartGiven(lists) {
    if (!lists.length) return [""];
    return lists.reduce(
      (acc, g) => acc.flatMap((p) => (g.alts.length ? g.alts : ["Given"]).map((a) => (p ? p + "/" + a : a))),
      [""],
    );
  }
  const givenPaths = cartGiven(givenAltLists);
  // Generate ALL path combinations
  const allPaths = uniq(
    implyAlts.flatMap((implyAlt) =>
      givenPaths.map((givenPath) => {
        const implyPath = sanitizeRelPath(implyAlt);
        const gp = givenPath ? sanitizeRelPath(givenPath) : "";
        const body = gp
          ? section + "/" + implyPath + "/of/" + gp + ".lean"
          : section + "/" + implyPath + ".lean";
        return body.replace(/\\/g, "/");
      }),
    ),
  ).filter((p) => !/\[anonymous\]|anonymous/i.test(p));
  const suggestions = allPaths.sort(byBestToWorst);
  const implyPath = sanitizeRelPath(implyName);
  const givenPath = givenNames.map((g) => sanitizeRelPath(g.name)).join("/");
  const relPath = sanitizeRelPath(
    givenPath
      ? section + "/" + implyPath + "/of/" + givenPath + ".lean"
      : section + "/" + implyPath + ".lean",
  );
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
  };
  const matchedSuggestion = suggestions.find((s) => pathsConsistent(result.currentPath, s).ok);
  result.consistent = matchedSuggestion
    ? { ok: true, reason: "exact match", existing: result.currentPath, suggested: matchedSuggestion }
    : pathsConsistent(result.currentPath, result.suggestedPath);
  return result;
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

/** Best = shortest ASCII bytes; worst = longest (redundant). Tie-break lexicographic. */
function byBestToWorst(a, b) {
  const ba = Buffer.byteLength(a, "utf8");
  const bb = Buffer.byteLength(b, "utf8");
  if (ba !== bb) return ba - bb;
  return a < b ? -1 : a > b ? 1 : 0;
}

function printHuman(r) {
  console.log("current:    Lemma/" + r.currentPath);
  {
    const chk = r.consistent || pathsConsistent(r.currentPath, r.suggestedPath);
    console.log("consistent: " + (chk.ok ? "yes" : "no") + (chk.ok ? "" : " (" + chk.reason + ")"));
  }
  console.log("section:    " + r.section + " (score " + r.sectionScore + "; tokens: " + (r.sectionTokens.join(", ") || "—") + ")");
  console.log("suggestions (" + r.suggestions.length + ", best→worst by ASCII bytes):");
  for (const s of r.suggestions) {
    console.log("  - Lemma/" + s + "  [" + Buffer.byteLength(s, "utf8") + " B]");
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
  const file = argv.find((a) => !a.startsWith("-") && a !== lemmaName);
  if (!file) {
    console.error("Usage: node mjs/lemmaPath.mjs [--json] [--lemma <name>] <path-to.lean>");
    process.exit(1);
  }
  try {
    const result = suggest(file, lemmaName);
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
