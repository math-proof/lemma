/**
 * Polymorphic hole-regex alternatives: each Lean node can emit a primary
 * structured regex plus same-head collapses (OpHS…), for any operator
 * or function, not only * / + / ^.
 */
import { storedHoleOpt, holeRegexDefaultNameToken } from "./pathChoices.js";

/** Observation combinators: equal operands do not compact into an S-plural. */
export const NON_PLURAL_ALT_HEADS = new Set(["Joint"]);

export function peelAltNode(node) {
  let n = node;
  for (let i = 0; i < 8 && n; i++) {
    const c = n.constructor?.name || "";
    if (c === "LeanParenthesis") {
      n = n.arg ?? n.args?.[0];
      continue;
    }
    if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") {
      const args = n.args || [];
      n = args.find((a) => (a?.constructor?.name || "") !== "LeanLineComment") || args[0];
      continue;
    }
    if (c === "LeanColon") {
      n = n.args?.[0];
      continue;
    }
    if (c === "LeanAngleBracket" && (n.args || []).length === 1) {
      n = n.args[0];
      continue;
    }
    break;
  }
  return n;
}

export function holeRegexAltTag(node) {
  const n = peelAltNode(node);
  if (!n) return null;
  // Prefer the alternatives-only tag so the main holeRegex()/lemmaPath
  // walk, which reads `holeRegexTag`, is unchanged.
  if (typeof n.holeRegexAltTag === "string") return n.holeRegexAltTag;
  return n.holeRegexTag || null;
}

export function altOperands(node) {
  const n = peelAltNode(node);
  if (!n) return [];
  if (typeof n.holeRegexAltOperands === "function") return n.holeRegexAltOperands();
  if (n.lhs != null || n.rhs != null) return [n.lhs, n.rhs];
  if (Object.prototype.hasOwnProperty.call(n, "arg") && (n.args || []).length <= 1) {
    return n.arg != null ? [n.arg] : [];
  }
  return n.args || [];
}

function isLeafNode(node, opts) {
  const n = peelAltNode(node);
  const raw = n?.text || "";
  if (typeof opts?.isLeaf === "function") return opts.isLeaf(raw);
  return !!(opts?.leaves?.has?.(raw));
}

function combineAlt(tag, left, right) {
  const lHole = !left;
  const rHole = !right;
  if (lHole && rHole) return tag + "__";
  if (!lHole && rHole) {
    if (/^-?\d+$/.test(left) || /[(|]/.test(left)) return tag + storedHoleOpt(left) + "_";
    return tag + left;
  }
  if (lHole && !rHole) return tag + "_" + storedHoleOpt(right);
  return tag + storedHoleOpt(left) + storedHoleOpt(right);
}

function combineFills(tag, fills) {
  if (fills.length === 0) return tag;
  // Brace always exposes its slots: `{y'}` → Brace_, `{x | P}` → Brace(Cond__).
  if (tag === "Brace" && fills.length === 1 && !fills[0]) return "Brace_";
  if (fills.length === 1) return fills[0] ? tag + storedHoleOpt(fills[0]) : tag;
  if (fills.length === 2) return combineAlt(tag, fills[0], fills[1]);
  if (fills.every((f) => !f)) return tag + "_".repeat(fills.length);
  return tag + fills.map((f) => (f ? storedHoleOpt(f) : "_")).join("");
}

/** Structured fill with both-hole binaries as Tag__. */
export function holeRegexAltFill(node, opts = {}) {
  const n = peelAltNode(node);
  if (!n) return "";
  const c = n.constructor?.name || "";
  if (c === "LeanToken") {
    const raw = n.text || "";
    if (!raw || raw === "_") return "";
    if (isLeafNode(n, opts)) return "";
    if (/^-?\d+$/.test(raw)) return raw;
    const nameToken = opts.nameToken || holeRegexDefaultNameToken;
    return nameToken(raw) || "";
  }
  const tag = holeRegexAltTag(n);
  const parts = altOperands(n);
  if (tag && parts.length) {
    return combineFills(tag, parts.map((p) => holeRegexAltFill(p, opts)));
  }
  if (typeof n.holeRegex === "function") {
    const raw = n.holeRegex(opts);
    if (raw && raw !== "_") return String(raw).replace(/\(_\|/g, "(");
  }
  return "";
}

export function meetAltFill(a, b, opts = {}) {
  const na = peelAltNode(a);
  const nb = peelAltNode(b);
  const ta = holeRegexAltTag(na);
  const tb = holeRegexAltTag(nb);
  if (ta && ta === tb) {
    const oa = altOperands(na);
    const ob = altOperands(nb);
    if (!oa.length || oa.length !== ob.length) {
      return ta + (oa.length === 2 || ob.length === 2 ? "__" : "");
    }
    const fills = oa.map((x, i) => meetAltFill(x, ob[i], opts));
    return combineFills(ta, fills);
  }
  // Literals and identical atoms agree (`2` vs `2`); a hole vs a structure does not.
  const fa = holeRegexAltFill(na, opts);
  const fb = holeRegexAltFill(nb, opts);
  if (fa && fa === fb) return fa;
  return "";
}

export function dropAltHead(tag, fill) {
  if (!fill) return "";
  if (!tag || !String(fill).startsWith(tag)) return fill;
  return String(fill).slice(tag.length);
}

function uniq(xs) {
  const out = [];
  for (const x of xs) if (x && !out.includes(x)) out.push(x);
  return out;
}

/**
 * Primary structured regex plus same-head alternatives for `node`.
 * @param {object} node
 * @param {object} [opts]
 * @returns {string[]}
 */
export function collectHoleRegexAlternatives(node, opts = {}) {
  const n = peelAltNode(node);
  if (!n) return [];
  if (n !== node && typeof n.holeRegexAlternatives === "function") {
    return n.holeRegexAlternatives(opts);
  }

  const tag = holeRegexAltTag(n);
  const parts = altOperands(n);
  const primary = holeRegexAltFill(n, opts);
  if (tag && parts.length === 1) {
    const inner = parts[0];
    const nested = typeof inner?.holeRegexAlternatives === "function"
      ? inner.holeRegexAlternatives(opts)
      : collectHoleRegexAlternatives(inner, opts);
    const inners = uniq([holeRegexAltFill(inner, opts), ...(nested || [])]);
    return uniq(inners.map((fill) => combineFills(tag, [fill])));
  }
  if (!tag || parts.length < 2) return primary ? [primary] : [];

  const out = [];
  if (primary) out.push(primary);
  const childAlts = parts.map((p) => {
    const nested = typeof p?.holeRegexAlternatives === "function"
      ? p.holeRegexAlternatives(opts)
      : collectHoleRegexAlternatives(p, opts);
    return uniq([holeRegexAltFill(p, opts), ...(nested || [])]);
  });

  const heads = parts.map((p) => holeRegexAltTag(p));
  const shared = heads[0];
  if (
    shared
    && heads.every((h) => h === shared)
    && !NON_PLURAL_ALT_HEADS.has(shared)
    && !NON_PLURAL_ALT_HEADS.has(tag)
  ) {
    let meetStr = meetAltFill(parts[0], parts[1], opts);
    for (let i = 2; i < parts.length; i++) {
      const next = meetAltFill(parts[0], parts[i], opts);
      meetStr = meetFillStrings(meetStr, next);
    }
    const collapsed = tag + shared + "S" + dropAltHead(shared, meetStr);
    if (collapsed) out.push(collapsed);
  }

  const cart = (i, acc) => {
    if (out.length > 64) return;
    if (i === childAlts.length) {
      const combined = combineFills(tag, acc);
      if (combined) out.push(combined);
      return;
    }
    const choices = childAlts[i].length ? childAlts[i] : [""];
    for (const a of choices) cart(i + 1, [...acc, a]);
  };
  cart(0, []);

  for (let i = 0; i < parts.length; i++) {
    const p = peelAltNode(parts[i]);
    const ptag = holeRegexAltTag(p);
    const sub = altOperands(p);
    if (!ptag || sub.length < 2) continue;
    const subHeads = sub.map((s) => holeRegexAltTag(s));
    if (!subHeads[0] || subHeads.some((h) => h !== subHeads[0])) continue;
    if (NON_PLURAL_ALT_HEADS.has(subHeads[0])) continue;
    const one = ptag + subHeads[0] + "S" + "__";
    const fills = parts.map((q, j) => (j === i ? one : holeRegexAltFill(q, opts)));
    out.push(combineFills(tag, fills));
  }

  return uniq(out);
}

/** Conservative meet of two already-built fills: keep a character prefix only
 *  through a shared operator spelling; if they differ, fall back to hole `_`
 *  groups. For binary n-ary>2 only. */
function meetFillStrings(a, b) {
  if (!a || !b) return "";
  if (a === b) return a;
  // If both start with the same tag, drop to `__` when structure diverges
  // unless one is a prefix hole of the other (Mul(2)_ vs Mul(2)(Div__)).
  const m = /^([A-Z][A-Za-z0-9]*)/.exec(a);
  const tag = m?.[1];
  if (!tag || !String(b).startsWith(tag)) return "";
  // Character-level is brittle; empty is safe. Binary fold does not use this.
  return "";
}
