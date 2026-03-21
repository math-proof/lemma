/**
 * Lean `compile` → `render2vue` / `echo2vue` — JavaScript API.
 *
 * - **PHP** (`LEAN_COMPILER=php` or `auto` when `php` works): delegates to
 *   `server/lean/php-bridge/render2vue.php` — same JSON as `php/parser/lean.php`.
 * - **JavaScript** (`LEAN_COMPILER=js`): `compile()` from `static/js/parser/lean.js` +
 *   `render2vue.mjs` (AST parity is still growing; no PHP subprocess).
 * - **`echo2vue`**: `echo2vueFromModule(module)` runs **`server/lean/php-bridge/echo2vue.php`** (PHP + lake + lean), same as `php/request/echo.php`.
 * - **Stub** (`parseLeanStub`) when `LEAN_COMPILER=stub` or chosen backend fails.
 *
 * See `server/lean/compiler/README.md`.
 */

import { buildRenderPropsFromSource } from '../parseLeanStub.mjs';
import { moduleToLeanPath } from '../modulePath.mjs';
import { render2vueViaPhp, phpAvailable, echo2vueViaPhp } from './compilePhp.mjs';
import { render2vueFromSource as render2vueFromCompiledTree } from './render2vue.mjs';

/**
 * @param {string} source
 * @param {string} module
 * @param {{ user?: string }} [opts]
 * @returns {object} Vue `render` payload
 */
export function render2vueFromSource(source, module, opts = {}) {
  const mode = process.env.LEAN_COMPILER || 'auto';
  if (mode === 'stub') {
    return buildRenderPropsFromSource(source, module, { user: opts.user });
  }
  if (mode === 'js' || mode === 'javascript') {
    try {
      const code = render2vueFromCompiledTree(source, false);
      code.module = module;
      if (opts.user) code.user = opts.user;
      return code;
    } catch (e) {
      console.warn('[lean compiler] LEAN_COMPILER=js failed, using stub:', e.message);
      return buildRenderPropsFromSource(source, module, { user: opts.user });
    }
  }
  if (mode === 'php') {
    try {
      const code = render2vueViaPhp(source);
      code.module = module;
      if (opts.user) code.user = opts.user;
      return code;
    } catch (e) {
      console.warn('[lean compiler] LEAN_COMPILER=php failed, using stub:', e.message);
      return buildRenderPropsFromSource(source, module, { user: opts.user });
    }
  }
  // auto: PHP → JS render2vue → stub
  if (phpAvailable()) {
    try {
      const code = render2vueViaPhp(source);
      code.module = module;
      if (opts.user) code.user = opts.user;
      return code;
    } catch (e) {
      console.warn('[lean compiler] PHP render2vue failed, trying JS:', e.message);
    }
  }
  try {
    const code = render2vueFromCompiledTree(source, false);
    code.module = module;
    if (opts.user) code.user = opts.user;
    return code;
  } catch (e) {
    console.warn('[lean compiler] JS render2vue failed, using stub:', e.message);
  }
  return buildRenderPropsFromSource(source, module, { user: opts.user });
}

/**
 * `compile(leanFile)->echo2vue(leanFile)` via PHP — writes `*.echo.lean`, runs lake + lean, merges goal JSON into `echo` tactics.
 * Requires **PHP**, **lake**, and **lean** (same as `php/request/echo.php`).
 *
 * @param {string} module e.g. `Nat.Min` → `Lemma/Nat/Min.lean`
 * @param {{ user?: string, cwd?: string }} [opts]
 * @returns {object} Vue render payload (includes merged LaTeX for echoed goals)
 */
export function echo2vueFromModule(module, opts = {}) {
  const p = moduleToLeanPath(module);
  if (!p) throw new Error('echo2vueFromModule: invalid module');
  const code = echo2vueViaPhp(p, opts);
  code.module = module;
  if (opts.user) code.user = opts.user;
  return code;
}

/** @deprecated Use {@link echo2vueFromModule}. */
export function echo2vueNotImplemented() {
  throw new Error(
    'Use echo2vueFromModule(module) — requires PHP, lake, and lean (server/lean/php-bridge/echo2vue.php).',
  );
}

export { tokenizeLeanSource } from './tokenize.mjs';
export { render2vueViaPhp, phpAvailable, echo2vueViaPhp } from './compilePhp.mjs';
export { mergeProof, render2vue, render2vueFromSource as render2vueFromCompiledTree } from './render2vue.mjs';
