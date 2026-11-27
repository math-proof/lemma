/**
 * Exact subtree match on binder-aware search-JSON trees
 * (`toJSON({ leaves: new Map(), binders: [] })`).
 *
 * - The query may appear as a subtree of a document conclusion.
 * - Query `$n` holes bind to any document subtree, consistently when repeated.
 * - Document `$n` are rigid free-name identities (compared as leaves).
 * - Binders are De Bruijn `?n` and must match by index, not surface name.
 * - Operator heads and children are compared syntactically, not by value.
 */
const HOLE_RE = /^\$\d+$/;

export function isSearchHole(node) {
  return typeof node === "string" && HOLE_RE.test(node);
}

/** Structural equality of two search-JSON values. */
export function treesEqual(a, b) {
  if (a === b) return true;
  if (a == null || b == null) return a === b;
  if (typeof a !== typeof b) return false;
  if (typeof a !== "object") return false;
  if (Array.isArray(a)) {
    if (!Array.isArray(b) || a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!treesEqual(a[i], b[i])) return false;
    }
    return true;
  }
  if (Array.isArray(b)) return false;
  const aKeys = Object.keys(a);
  const bKeys = Object.keys(b);
  if (aKeys.length !== bKeys.length) return false;
  for (const key of aKeys) {
    if (!Object.prototype.hasOwnProperty.call(b, key)) return false;
    if (!treesEqual(a[key], b[key])) return false;
  }
  return true;
}

/**
 * Match `query` at the root of `doc`. `env` maps query hole names (`$1`) to the
 * document subtree they bound on first occurrence.
 */
/** Layout-only wrapper from an indented big-op body; treat as the inner tree. */
function unwrapSingleton(node) {
  if (Array.isArray(node) && node.length === 1) return unwrapSingleton(node[0]);
  return node;
}

export function matchAt(query, doc, env = new Map()) {
  query = unwrapSingleton(query);
  doc = unwrapSingleton(doc);
  if (isSearchHole(query)) {
    if (env.has(query)) return treesEqual(env.get(query), doc);
    env.set(query, doc);
    return true;
  }
  if (typeof query !== "object" || query == null) return query === doc;
  if (typeof doc !== "object" || doc == null) return false;
  if (Array.isArray(query)) {
    if (!Array.isArray(doc) || query.length !== doc.length) return false;
    for (let i = 0; i < query.length; i++) {
      if (!matchAt(query[i], doc[i], env)) return false;
    }
    return true;
  }
  if (Array.isArray(doc)) return false;
  const qKeys = Object.keys(query);
  const dKeys = Object.keys(doc);
  if (qKeys.length !== dKeys.length) return false;
  for (const key of qKeys) {
    if (!Object.prototype.hasOwnProperty.call(doc, key)) return false;
    if (!matchAt(query[key], doc[key], env)) return false;
  }
  return true;
}

function someNode(node, pred) {
  if (pred(node)) return true;
  if (node && typeof node === "object") {
    const children = Array.isArray(node) ? node : Object.values(node);
    for (const child of children) {
      if (someNode(child, pred)) return true;
    }
  }
  return false;
}

/** True when `query` matches `doc` or any of its subtrees. */
export function matchesSubtree(query, doc) {
  return someNode(doc, (node) => matchAt(query, node, new Map()));
}
