/**
 * Moved to `./lint/` (rule `open-section`); kept as a thin compatibility layer.
 */
import { blankLeanComments, prepare } from './lint/scan.mjs';
import { scanImportsAndOpens as scan } from './lint/headerRules.mjs';
import { lintLean } from './lint/index.mjs';

export { blankLeanComments };

/** @param {string} source */
export function scanImportsAndOpens(source) {
    const { imports, opened, scoped } = scan(prepare(source));
    return { imports, opened, scoped };
}

/**
 * @param {string} source
 * @param {{ sections?: Iterable<string> }} [opts]
 */
export function sectionOpenWarnings(source, opts = {}) {
    return lintLean(source, { ...opts, rules: ['open-section'] });
}
