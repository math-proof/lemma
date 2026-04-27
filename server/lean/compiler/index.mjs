/**
 * Lean `compile` → `render2vue` — JavaScript API.
 * Uses `compile()` / `LeanModule.render2vue` from `static/js/parser/lean.js`; `render2vue.mjs` re-exports helpers.
 * Falls back to regex stub (`parseLeanStub.mjs`) when JS parse fails.
 *
 * See `server/lean/compiler/README.md`.
 */

import { render2vueFromSource as render2vueFromCompiledTree } from './render2vue.mjs';

/**
 * @param {string} source
 * @param {{ user?: string }} [opts]
 * @returns {object} Vue `render` payload (`module` is `null` here; MySQL rows set it in `codeFromMysqlRow`).
 */
export function render2vueFromSource(source, opts = {}) {
  const code = render2vueFromCompiledTree(source, false);
  code.module = null;
  if (opts.user) code.user = opts.user;
  return code;
}

export { tokenizeLeanSource } from './tokenize.mjs';
export {
  echo2vueFromSource,
  mergeProof,
  render2vue,
  render2vueFromSource as render2vueFromCompiledTree,
} from './render2vue.mjs';
