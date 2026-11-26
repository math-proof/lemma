import fs from "fs";
import path from "path";
import { pathToFileURL } from "url";
import { compile } from "../js/parser/lean.js";
import { Lean } from "../js/parser/lean/base.js";
import { json2pathPatterns, regex2dag, dag2suggession, suggestionMatches } from "../js/parser/lean/json2regex.js";
import {
  TYPE_TO_SECTION,
  DATA_TYPE_SECTIONS,
  LEMMA_ROOT,
  pickSection,
  existingSections,
  nonDataFolder,
  customSection,
  importSections,
  openDataSections,
  refusedSectionFolder,
  sectionKindMap,
  cls,
  unwrapParen,
  firstConclusion,
  conclusionNode,
  reassociateDotProduct,
} from "./lemmaSection.mjs";
import { collapseEqSelf } from "./lean/modulePath.mjs";

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

function validModuleComponentBasic(c) {
  return /^[\p{L}_][\p{L}\p{N}_'!?\u2080-\u209C\u1D62-\u1D6A\u2070-\u207F]*$/u.test(c || "");
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
  return selectLemma(ast, lemmaName).lemma;
}

/**
 * The declaration the conclusion fingerprint is taken from, and its zero-based
 * position among the file's `lemma` / `theorem` declarations: the declaration
 * carrying the `main` attribute wins, otherwise the first one. That position is
 * `inverted.lemma_id` — `main` is not necessarily declaration 0.
 */
function selectLemma(ast, lemmaName, lemmaId) {
  const lemmas = extractLemmas(ast);
  const index = Number(lemmaId);
  if (Number.isInteger(index) && index >= 0 && lemmas[index])
    return { lemma: lemmas[index], index };
  if (lemmaName) {
    const named = lemmas.find((l) => getLemmaName(l) === lemmaName);
    if (named) return { lemma: named, index: lemmas.indexOf(named) };
  }
  const lemma = lemmas.find(hasMainAttr) || lemmas[0];
  return { lemma, index: lemma ? lemmas.indexOf(lemma) : -1 };
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

/** Constructor and literal nodes. A hole `_` is not a node. */
function pathNodeCount(regex) {
  if (!regex) return 0;
  let tree;
  try {
    tree = parseRegexTree(regex);
  } catch {
    return 0;
  }
  let count = 0;
  (function walk(node) {
    if (!node) return;
    if (node.kind === "tok") {
      if (node.text.replace(/_/g, "") !== "") count++;
      return;
    }
    for (const child of node.children || []) walk(child);
  })(tree);
  return count;
}

function expressionPathPart(node) {
  const expr = unwrapParen(node);
  const relation = expressionRelation(expr);
  const json = expr.toJSON();
  const patterns = json2pathPatterns(relation === "ae" && json.Eq ? { MEq: json.Eq } : json);
  const named = patterns.filter((pattern) => validModuleComponentBasic(pattern.token));
  const descriptive = named.filter((pattern) => pathNodeCount(pattern.regex) >= MIN_PATH_NODES);
  const pool = descriptive.length ? descriptive : named;
  let token = "";
  let regex = "";
  for (const pattern of pool) {
    if (!token || pattern.token.length < token.length) {
      token = pattern.token;
      regex = pattern.regex;
    }
  }
  return { node: expr, token, regex, patterns };
}

/** Module path budget. The dotted name itself, not a filesystem path. */
const MODULE_PATH_MAX = 256;

/**
 * A path token must keep at least two tree nodes when the expression has them.
 * `All` alone does not say what was quantified; `All_Differentiable` does.
 */
const MIN_PATH_NODES = 2;

function parseRegexTree(regex) {
  const tokens = regex.match(/[()]|[^()]+/g) ?? [];
  let index = 0;
  function seq() {
    const children = [];
    while (index < tokens.length && tokens[index] !== ")") {
      if (tokens[index] === "(") {
        index++;
        children.push(group());
      } else {
        children.push({ kind: "tok", text: tokens[index++] });
      }
    }
    return { kind: "seq", children };
  }
  function group() {
    const body = seq();
    if (tokens[index++] !== ")") throw new Error("Unclosed regex group");
    return { kind: "group", children: body.children };
  }
  return seq();
}

function serializeRegexTree(node) {
  if (node.kind === "tok") return node.text;
  if (node.kind === "group") return "(" + node.children.map(serializeRegexTree).join("") + ")";
  return node.children.map(serializeRegexTree).join("");
}

/** Every group, deepest first, so a leaf is dropped before its parent. */
function groupsDeepestFirst(node, parent, index, depth, acc) {
  if (!node || node.kind === "tok") return;
  if (node.kind === "group" && parent) acc.push({ parent, index, depth });
  for (const [i, child] of (node.children || []).entries()) {
    groupsDeepestFirst(child, node.kind === "group" ? node : node, i, depth + 1, acc);
  }
}

/**
 * Drop one leaf group and rebuild the path token. A leaf that the suggestion
 * already ignores is skipped in favour of the next deepest group that actually
 * shortens the token.
 * @returns {{ regex: string, token: string } | null}
 */
function dropPathLeaf(regex, previousToken) {
  let tree;
  try {
    tree = parseRegexTree(regex);
  } catch {
    return null;
  }
  const groups = [];
  groupsDeepestFirst(tree, null, 0, 0, groups);
  groups.sort((a, b) => b.depth - a.depth);
  for (const { parent, index } of groups) {
    const removed = parent.children.splice(index, 1);
    const next = serializeRegexTree(tree);
    let token = "";
    try {
      token = dag2suggession(regex2dag(next));
    } catch {
      token = "";
    }
    const nodes = pathNodeCount(next);
    if (nodes < MIN_PATH_NODES && pathNodeCount(regex) >= MIN_PATH_NODES) {
      parent.children.splice(index, 0, ...removed);
      continue;
    }
    if (validModuleComponentBasic(token) && token.length < previousToken.length) {
      return { regex: next, token };
    }
    parent.children.splice(index, 0, ...removed);
  }
  return null;
}

function implyToken(part) {
  const split = part.relation && isRealPathToken(part.left?.token) && isRealPathToken(part.right?.token)
    ? [part.left.token, part.relation, part.right.token].join(".")
    : "";
  return split || part.flat.token;
}

function modulePath(section, implyParts, givenParts) {
  const imply = implyParts.map(implyToken).join(".");
  const givens = givenParts.map((part) => part.token);
  return [section, imply, ...(givens.length ? ["of", ...givens] : [])].join(".");
}

/**
 * When the suggested module is longer than 256 characters, drop one leaf from
 * every imply token and every given token, and repeat. Each tree loses the
 * same number of leaves until the path fits or no tree has a leaf left.
 */
function fitModulePath(section, implyParts, givenParts, max = MODULE_PATH_MAX) {
  const trees = [];
  for (const part of implyParts) {
    if (part.relation && part.left && part.right) trees.push(part.left, part.right);
    else trees.push(part.flat);
  }
  for (const part of givenParts) trees.push(part);
  let guard = 0;
  while (modulePath(section, implyParts, givenParts).length > max && guard++ < 500) {
    let dropped = 0;
    for (const tree of trees) {
      if (!tree?.regex) continue;
      const next = dropPathLeaf(tree.regex, tree.token);
      if (!next || next.token.length >= tree.token.length) continue;
      tree.regex = next.regex;
      tree.token = next.token;
      dropped++;
    }
    if (!dropped) break;
  }
  return modulePath(section, implyParts, givenParts);
}

/** A usable path token: non-empty and not the `_` placeholder. */
function isRealPathToken(token) {
  return typeof token === "string" && token.length > 0 && token !== "_";
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
  for (const part of implyParts) {
    if (!implyToken(part)) throw new Error("Could not generate a path token for a conclusion");
  }
  for (const part of givenParts) {
    if (!part.token) throw new Error(`Could not generate a path token for hypothesis ${part.name}`);
  }
  const path = fitModulePath(section, implyParts, givenParts);
  const imply = implyParts.map(implyToken).join(".");
  const givenText = givenParts.map((part) => part.token).join(".");
  // Collapse redundant `… .X.eq.X …` suffixes (e.g. Real.Sum_IteAnd.eq.Sum_IteAnd → Real.Sum_IteAnd).
  const collapsedPath = collapseEqSelf(path);
  return { section, imply, givens: givenText, path: collapsedPath, implyParts, givenParts };
}

/**
 * Parse a lemma file offline and return its conclusion as a `toJSON()` tree.
 *
 * Much cheaper than `suggestExpressionPath`: it skips the section bookkeeping
 * (which is what makes a whole-tree scan slow) and is meant for building a
 * structural search index, see `mjs/leanExprSearch.mjs`.
 *
 * @param {string} filePath - path to the `.lean` file (relative to the cwd or absolute).
 * @param {string} [lemmaName] - pick this lemma instead of the main one.
 * @param {{ file?: string, source?: string, lemmaId?: number }} [options]
 * @returns {object} the conclusion node's JSON tree.
 */
/** The AST node of a lemma conclusion (`lemma main` after `-- imply`). */
export function conclusionNodeOf(filePath, lemmaName, options = {}) {
  const abs = options.file ? path.resolve(options.file) : path.resolve(filePath);
  const source = options.source != null
    ? String(options.source).replace(/\r\n/g, "\n")
    : fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const ast = compileLemmaSource(source);
  const { lemma, index } = selectLemma(ast, lemmaName, options.lemmaId);
  if (!lemma) throw new Error("No Lean_lemma found");
  // `lemma_id` of the fingerprinted declaration, for axiom.inverted postings.
  if (options.location && typeof options.location === "object") {
    options.location.lemmaId = Math.max(0, index);
  }
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  const conclusion = conclusionNode(sig.colon);
  if (!conclusion) throw new Error("Could not find the lemma conclusion");
  return conclusion;
}

export function conclusionJson(filePath, lemmaName, options = {}) {
  return conclusionNodeOf(filePath, lemmaName, options).toJSON();
}

/** Fingerprint tree: free leaves `$n`, binders De Bruijn `?n`. */
export function conclusionSearchJson(filePath, lemmaName, options = {}) {
  return conclusionNodeOf(filePath, lemmaName, options).toJSON({ leaves: new Map(), binders: [] });
}

function searchContext() {
  return { leaves: new Map(), binders: [] };
}

/** Proof steps in the same source-level positions as `render2vue(null)`. */
function proofStepsOf(lemma) {
  const L = Lean.classes;
  const assign = (lemma.args || []).find((a) => cls(a) === "LeanAssign");
  const proof = assign?.rhs ?? assign?.args?.[1];
  if (!proof) return [];
  const root = proof instanceof L.LeanBy ? proof.arg : proof;
  if (!root) return [];
  const list = (proof instanceof L.LeanCalc ? [proof] : (root.args || [root]))
    .filter((s) => !(s instanceof L.LeanCaret))
    .filter((s, i) => !(i === 0 && s instanceof L.LeanLineComment && s.text === "proof"));
  const syntax = {};
  const statements = [];
  for (const statement of list) statements.push(...statement.split(syntax));
  const steps = [];
  let current = [];
  for (const statement of statements) {
    if (statement instanceof L.Lean_let || statement instanceof L.LeanTactic) {
      current.push(statement);
      steps.push(current);
      current = [];
    } else {
      current.push(statement);
    }
  }
  if (current.length) steps.push(current);
  return steps;
}

function withoutTacticJson(json) {
  if (Array.isArray(json)) {
    return json.map(withoutTacticJson).filter((item) => item !== null);
  }
  if (json && typeof json === "object") {
    // LeanTactic.toJSON() always carries `modifiers`; nested `by` terms can
    // therefore be removed after an enclosing mathematical application renders.
    if (Object.hasOwn(json, "modifiers")) return null;
    return Object.fromEntries(
      Object.entries(json)
        .map(([key, value]) => [key, withoutTacticJson(value)])
        .filter(([, value]) => value !== null),
    );
  }
  return json;
}

/**
 * Collect mathematical expressions below a proof step without indexing tactic
 * names as expression heads. In particular, `have h : P := proof` contributes
 * the asserted proposition `P` only: the proof term (`Real.cos_sq_add_sin_sq θ`)
 * is not mathematics, and its LaTeX would just print the lemma name.
 */
function appendProofMath(node, ctx, out, onNode = null) {
  if (!node || typeof node !== "object") return;
  const L = Lean.classes;
  if (node instanceof L.LeanLineComment || node instanceof L.LeanCaret) return;
  if (node instanceof L.LeanAssign) {
    const lhs = node.lhs ?? node.args?.[0];
    const rhs = node.rhs ?? node.args?.[1];
    if (lhs instanceof L.LeanColon) {
      appendProofMath(lhs.rhs ?? lhs.args?.[1], ctx, out, onNode);
      return;
    }
    appendProofMath(lhs, ctx, out, onNode);
    appendProofMath(rhs, ctx, out, onNode);
    return;
  }
  if (node instanceof L.LeanColon) {
    appendProofMath(node.rhs ?? node.args?.[1], ctx, out, onNode);
    return;
  }
  const containers = [
    L.Lean_let, L.LeanTactic, L.Lean_show, L.LeanBy, L.LeanCalc, L.LeanIte,
    L.LeanStatements, L.LeanArgsNewLineSeparated, L.LeanArgsIndented,
    L.LeanBracket, L.LeanParenthesis, L.LeanArgsCommaSeparated,
    L.LeanArgsCommaNewLineSeparated, L.LeanFrom,
    L.LeanSequentialTacticCombinator, L.LeanUsing, L.LeanWith,
  ].filter(Boolean);
  if (containers.some((Ctor) => node instanceof Ctor)) {
    for (const arg of node.args || []) appendProofMath(arg, ctx, out, onNode);
    return;
  }
  if (typeof node.toJSON === "function") {
    const json = withoutTacticJson(node.toJSON(ctx));
    if (json !== null) {
      out.push(json);
      if (onNode) onNode(node, json);
    }
  }
}

/**
 * Given / imply-conjunct / proof-step documents of one declaration.
 * Throws when the declaration has no parseable signature.
 */
function documentsForLemma(lemma, lemmaId, withProof = true) {
  const sig = extractSignature(lemma);
  if (!sig) throw new Error("Could not find lemma signature");
  const conclusion = conclusionNode(sig.colon);
  if (!conclusion) throw new Error("Could not find the lemma conclusion");

  const documents = [];
  const givens = extractGivens(sig.nls ?? sig.colon.args[0])
    .filter((h) => h.prop || expressionRelation(h.typeNode));
  givens.forEach(({ typeNode }, latexId) => {
    documents.push({ json: typeNode.toJSON(searchContext()), lemmaId, section: "given", latexId });
  });

  const implyParts = splitTopConjunction(conclusion, true) ?? [conclusion];
  implyParts.forEach((node, latexId) => {
    documents.push({ json: node.toJSON(searchContext()), lemmaId, section: "imply", latexId });
  });

  if (withProof) {
    proofStepsOf(lemma).forEach((step, latexId) => {
      const json = [];
      const ctx = searchContext();
      for (const node of step) appendProofMath(node, ctx, json);
      documents.push({ json, lemmaId, section: "proof", latexId });
    });
  }

  return { conclusion, documents };
}

/**
 * Extract every searchable formula from the selected declaration. The whole
 * imply tree remains the metadata fingerprint used by exact conclusion search;
 * postings point at individual given / imply-conjunct / proof-step formulas.
 *
 * `options.allLemmas` also collects the same sections for every other
 * declaration in the file (private helpers included), so the lemma page can
 * answer hover requests for their conclusions and proof steps.
 *
 * @returns {{ lemmaId: number, fingerprint: object, documents: {json: object|object[], lemmaId: number, section: 'given'|'imply'|'proof', latexId: number}[] }}
 */
export function lemmaSearchDocuments(filePath, lemmaName, options = {}) {
  const abs = options.file ? path.resolve(options.file) : path.resolve(filePath);
  const source = options.source != null
    ? String(options.source).replace(/\r\n/g, "\n")
    : fs.readFileSync(abs, "utf8").replace(/\r\n/g, "\n");
  const ast = compileLemmaSource(source);
  const { lemma, index } = selectLemma(ast, lemmaName);
  if (!lemma) throw new Error("No Lean_lemma found");
  const lemmaId = Math.max(0, index);
  if (options.location && typeof options.location === "object") options.location.lemmaId = lemmaId;
  const { conclusion, documents } = documentsForLemma(lemma, lemmaId, !options.omitProof);
  if (options.allLemmas) {
    extractLemmas(ast).forEach((other, otherId) => {
      if (otherId === lemmaId) return;
      try {
        documents.push(...documentsForLemma(other, otherId, !options.omitProof).documents);
      } catch {
        // a sub-declaration without a parseable signature contributes nothing
      }
    });
  }

  return { lemmaId, fingerprint: conclusion.toJSON(searchContext()), documents };
}

/**
 * Source AST nodes of one section formula, in the same order as
 * `lemmaSearchDocuments`. Used by search results to render the formula that
 * actually matched instead of the conclusion.
 */
export function sectionFormulaNodes(filePath, section, latexId, lemmaId) {
  const ast = compile(fs.readFileSync(filePath, "utf8"));
  const { lemma } = selectLemma(ast, undefined, lemmaId);
  const sig = extractSignature(lemma);
  if (!sig) return [];
  const nodeItem = (node) => {
    if (!node) return [];
    try {
      return [{ node, json: node.toJSON(searchContext()) }];
    } catch {
      return [];
    }
  };
  if (section === "given") {
    const givens = extractGivens(sig.nls ?? sig.colon.args[0])
      .filter((h) => h.prop || expressionRelation(h.typeNode));
    return nodeItem(givens[latexId]?.typeNode);
  }
  const conclusion = conclusionNode(sig.colon);
  if (!conclusion) return [];
  if (section === "imply") {
    const parts = splitTopConjunction(conclusion, true) ?? [conclusion];
    return nodeItem(parts[latexId]);
  }
  if (section === "proof") {
    const step = proofStepsOf(lemma)[latexId];
    if (!step) return [];
    const items = [];
    const ctx = searchContext();
    for (const node of step) appendProofMath(node, ctx, [], (n, json) => items.push({ node: n, json }));
    return items;
  }
  return [];
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
    const infix = isRealPathToken(left?.token) && isRealPathToken(right?.token);
    if (relation && (infix || EXPRESSION_RELATION_TOKENS.has(imply[index + 1]))) {
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
    const infix = isRealPathToken(left?.token) && isRealPathToken(right?.token);
    if (relation && (infix || EXPRESSION_RELATION_TOKENS.has(implySegments[index + 1]))) {
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
