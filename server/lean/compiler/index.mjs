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
 * @param {string} _module  Dotted module (reserved for callers; payload `module` is set in `app.mjs`).
 * @param {{ user?: string }} [opts]
 * @returns {object} Vue `render` payload
 */
export function render2vueFromSource(source, _module, opts = {}) {
  const code = render2vueFromCompiledTree(source, false);
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
