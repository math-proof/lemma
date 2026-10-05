/**
 * Negation: `Lean_lnot` (`¬`) and `LeanNot` (`!`).
 *
 * `LeanUnary` and `LeanProp` stay in `lean.js` and are passed in. `LeanStatements`
 * already exists and is passed in; `LeanNot.is_indented` uses it via `instanceof`.
 * This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.LeanProp
 * @param {Function} deps.LeanStatements
 */
export function createNegationFamily(deps) {
    const { LeanUnary, LeanProp, LeanStatements } = deps;

    /** Logical not `¬`. */
    class Lean_lnot extends LeanProp(LeanUnary) {
        static input_priority = 40;

        get operator() {
            return '¬';
        }

        strFormat() {
            return `${this.operator}%s`;
        }
    }

    class LeanNot extends LeanProp(LeanUnary) {
        static input_priority = 40;

        get operator() {
            return '!';
        }

        get command() {
            return '\\text{!}';
        }

        is_indented() {
            return this.parent instanceof LeanStatements;
        }

        latexFormat() {
            return `${this.command} %s`;
        }

        strFormat() {
            return `${this.operator}%s`;
        }
    }

    return {
        Lean_lnot,
        LeanNot,
    };
}
