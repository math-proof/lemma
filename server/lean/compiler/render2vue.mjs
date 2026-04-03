/**
 * `LeanModule::render2vue` / `merge_proof` — implementation lives in `static/js/parser/lean.js`.
 */

import { compile, LeanModule } from '../../../static/js/parser/lean.js';
import { runEcho2Vue } from '../echo2vuePhp.mjs';

export function mergeProof(proof, echo, syntax = {}) {
    return LeanModule.merge_proof(proof, echo, syntax);
}

export function render2vue(mod, echo, modify = null, syntax = {}) {
    return mod.render2vue(echo, modify, syntax);
}

/**
 * @param {string} source
 * @param {boolean} [echo]
 */
export function render2vueFromSource(source, echo = false) {
    const tree = compile(source);
    if (!(tree instanceof LeanModule)) throw new Error('compile() root must be LeanModule');
    const modify = { value: false };
    const syntax = {};
    return tree.render2vue(echo, modify, syntax);
}

/**
 * Port of `compile(…)->echo2vue($leanFile)` (php/request/echo.php + php/parser/lean.php ~4738–4852).
 * Requires `leanAbsPath` (absolute path to the `.lean` file) for `*.echo.lean` and `lake env lean`.
 *
 * @param {string} source
 * @param {{ module?: string, leanAbsPath: string }} options
 */
export function echo2vueFromSource(source, options) {
    const { leanAbsPath, module: moduleName } = options || {};
    if (!leanAbsPath || typeof leanAbsPath !== 'string') {
        throw new Error('echo2vueFromSource requires options.leanAbsPath');
    }
    const tree = compile(source);
    if (!(tree instanceof LeanModule)) throw new Error('compile() root must be LeanModule');
    return runEcho2Vue(tree, leanAbsPath, { module: moduleName });
}
