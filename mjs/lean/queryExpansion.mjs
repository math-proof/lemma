/**
 * Query expansions for similarity matching (see `searchLeanSimilar` in
 * mjs/leanInvertedIndex.mjs). Exact search keeps using the original query; these
 * variants only feed the separate "similarity" section.
 *
 * Sum/product binders are rewritten in the source because the search-JSON tree
 * cannot tell `∑ t ∈ _` from `∑ t ∈ s` (both become a `$n` hole), and rewriting
 * the source preserves binder structure and free-name numbering. The same rules
 * apply to `∏`.
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
