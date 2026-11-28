/**
 * A JSON fingerprint used as a repair query.
 * `"_"` matches one subtree; each `"_"` is independent.
 * `"/expr/"` matches a string leaf against `expr` (`/[2-4]/` is the exponent 2, 3, or 4).
 * `$n` is a repeated hole, the same as subtree search.
 */
import { matchesSubtree } from '../leanSubtreeMatch.mjs';

const HOLE_RE = /^\$(\d+)$/;

function maxHole(node) {
  let max = 0;
  const walk = (n) => {
    if (typeof n === 'string') {
      const m = HOLE_RE.exec(n);
      if (m) max = Math.max(max, Number(m[1]));
      return;
    }
    if (Array.isArray(n)) {
      for (const x of n) walk(x);
      return;
    }
    if (n && typeof n === 'object') {
      for (const v of Object.values(n)) walk(v);
    }
  };
  walk(node);
  return max;
}

/** Replace each `"_"` with a fresh `$n` so subtree search treats it as an anonymous hole. */
export function compileFingerprintPattern(pattern) {
  let next = maxHole(pattern);
  const walk = (node) => {
    if (node === '_') return '$' + (++next);
    if (Array.isArray(node)) return node.map(walk);
    if (node && typeof node === 'object') {
      const out = {};
      for (const [key, value] of Object.entries(node)) out[key] = walk(value);
      return out;
    }
    return node;
  };
  return walk(pattern);
}

/** True when `pattern` matches `doc` or any subtree of `doc`. */
export function fingerprintMatches(pattern, doc) {
  return matchesSubtree(compileFingerprintPattern(pattern), doc);
}

export function parseFingerprintPattern(text) {
  let value;
  try {
    value = JSON.parse(text);
  } catch (e) {
    throw new Error('invalid json fingerprint: ' + (e.message || e));
  }
  if (value == null || typeof value !== 'object') {
    throw new Error('json fingerprint must be an object or array');
  }
  return value;
}

/** Operator heads in a pattern, in first-seen order. Used to prefilter rows. */
export function patternHeads(pattern) {
  const heads = [];
  const seen = new Set();
  const walk = (node) => {
    if (Array.isArray(node)) {
      for (const x of node) walk(x);
      return;
    }
    if (!node || typeof node !== 'object') return;
    for (const [key, value] of Object.entries(node)) {
      if (!seen.has(key)) {
        seen.add(key);
        heads.push(key);
      }
      walk(value);
    }
  };
  walk(pattern);
  return heads;
}
