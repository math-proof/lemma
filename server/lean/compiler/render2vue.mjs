/**
 * `LeanModule::render2vue` / `merge_proof` — implementation lives in `static/js/parser/lean.js`.
 */

import { compile, LeanModule } from '../../../static/js/parser/lean.js';

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
