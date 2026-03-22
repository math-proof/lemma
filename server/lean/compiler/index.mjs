/**
 * Lean `compile` → `render2vue` — JavaScript API.
 * Uses `compile()` from `static/js/parser/lean.js` + `render2vue.mjs`.
 * Falls back to regex stub (`parseLeanStub.mjs`) when JS parse fails.
 *
 * See `server/lean/compiler/README.md`.
 */

import { buildRenderPropsFromSource } from '../parseLeanStub.mjs';
import { render2vueFromSource as render2vueFromCompiledTree } from './render2vue.mjs';

/**
 * @param {string} source
 * @param {string} module
 * @param {{ user?: string }} [opts]
 * @returns {object} Vue `render` payload
 */
export function render2vueFromSource(source, module, opts = {}) {
  try {
    const code = render2vueFromCompiledTree(source, false);
    code.module = module;
    if (opts.user) code.user = opts.user;
    return code;
  } catch (e) {
    console.warn('[lean compiler] JS render2vue failed, using stub:', e.message);
    return buildRenderPropsFromSource(source, module, { user: opts.user });
  }
}

export { tokenizeLeanSource } from './tokenize.mjs';
export { mergeProof, render2vue, render2vueFromSource as render2vueFromCompiledTree } from './render2vue.mjs';
