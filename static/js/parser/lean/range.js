/**
 * Interval notation `a..b` (`LeanUpto`).
 *
 * `LeanBinary` and `LeanCaret` already exist and are passed in. JS `sep`
 * inserts a space when the right-hand side is still a caret; PHP `sep` stays
 * empty. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanCaret
 */
export function createRangeFamily(deps) {
    const {
        LeanBinary,
        LeanCaret,
    } = deps;

    /**
     * Interval notation `a..b` used by `∫ x in a..b, f x` (Mathlib `notation3 "a".."b"`).
     * Binds looser than arithmetic/relational nodes, matching the term-level parsing of the bounds.
     */
    class LeanUpto extends LeanBinary {
        static input_priority = 49; // LeanRelational::$input_priority - 1

        get operator() {
            return '..';
        }

        get command() {
            return '..';
        }

        strFormat() {
            return '%s' + this.sep() + '..%s';
        }

        latexFormat() {
            return '%s' + this.sep() + '..%s';
        }

        sep() {
            return this.rhs instanceof LeanCaret ? ' ' : '';
        }
    }

    return {
        LeanUpto,
    };
}
