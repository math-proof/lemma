/**
 * Query expansions for similarity matching (see `searchLeanSimilar` in
 * mjs/leanInvertedIndex.mjs). Exact search keeps using the original query; these
 * variants only feed the separate "similarity" section.
 *
 * Sum/product binders are rewritten in the source because the search-JSON tree
 * cannot tell `∑ t ∈ _` from `∑ t ∈ s` (both become a `$n` hole), and rewriting
 * the source preserves binder structure and free-name numbering. The same rules
 * apply to `∏`.
 *
 * Powers are rewritten on the tree (`Square(x)` <-> `Pow(x)(2)`), because a
 * source-level `²` -> `^ 2` replacement would change parsing in application
 * position (`f x²` is `f (x²)`, but `f x ^ 2` is `(f x)^2`).
 */

const BIG_OP = '[∑∏]';
const IDENT = String.raw`[\p{L}_][\p{L}\p{N}_'!?]*`;

/** `∑ t, f` / `∏ t, f` — a plain binder, immediately followed by the comma. */
const BINDER_PLAIN = new RegExp(`(${BIG_OP})\\s*(${IDENT})\\s*,`, 'gu');
/** `∑ t ∈ _, f` / `∏ t ∈ _, f` */
const BINDER_MEM = new RegExp(`(${BIG_OP})\\s*(${IDENT})\\s*∈\\s*_\\s*,`, 'gu');
/** `∑ t : _, f` / `∏ t : _, f` */
const BINDER_TYPE = new RegExp(`(${BIG_OP})\\s*(${IDENT})\\s*:\\s*_\\s*,`, 'gu');

/**
 * Source variants for the big-operator binder rewrites (`∑` and `∏`), in both
 * directions. The original expression is included first so the caller can
 * deduplicate by fingerprint.
 * @param {string} expr
 * @returns {string[]}
 */
export function binderQueryVariants(expr) {
  const variants = [expr];
  const push = (text) => {
    if (text !== expr && !variants.includes(text)) variants.push(text);
  };
  push(expr.replace(BINDER_PLAIN, (_, op, v) => `${op} ${v} ∈ _,`));
  push(expr.replace(BINDER_PLAIN, (_, op, v) => `${op} ${v} : _,`));
  push(expr.replace(BINDER_MEM, (_, op, v) => `${op} ${v},`));
  push(expr.replace(BINDER_TYPE, (_, op, v) => `${op} ${v},`));
  return variants;
}

const SUPERSCRIPT_HEAD = { Square: '2', Cube: '3', Tesseract: '4' };
const SUPERSCRIPT_OF = { 2: 'Square', 3: 'Cube', 4: 'Tesseract' };

/** @param {any} node @param {(head: string, args: any) => object | null} fn */
function mapTree(node, fn) {
  if (node == null || typeof node !== 'object') return node;
  if (Array.isArray(node)) return node.map((child) => mapTree(child, fn));
  const head = Object.keys(node)[0];
  const args = node[head];
  const mapped = Array.isArray(args) ? args.map((child) => mapTree(child, fn)) : mapTree(args, fn);
  return fn(head, mapped) ?? { [head]: mapped };
}

/**
 * Tree variants for `x²` <-> `x ^ 2` (and ³/⁴), applied wherever they occur.
 * @param {any} json search-JSON tree
 * @returns {any[]} variants that actually changed the tree
 */
export function powerQueryVariants(json) {
  const toPow = (head, args) => {
    const exponent = SUPERSCRIPT_HEAD[head];
    if (!exponent || !Array.isArray(args) || args.length !== 1) return null;
    return { Pow: [args[0], exponent] };
  };
  const toSuperscript = (head, args) => {
    if (head !== 'Pow' || !Array.isArray(args) || args.length !== 2) return null;
    const superscript = SUPERSCRIPT_OF[args[1]];
    if (!superscript) return null;
    return { [superscript]: [args[0]] };
  };
  const original = JSON.stringify(json);
  return [mapTree(json, toPow), mapTree(json, toSuperscript)]
    .filter((variant) => JSON.stringify(variant) !== original);
}
