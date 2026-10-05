/**
 * Lambda binder head: `Lean_fun` (`fun` / `λ`).
 *
 * `LeanUnary`, `LeanArgsNewLineSeparated`, and `LeanStatements` stay in
 * `lean.js` and are passed in. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.LeanArgsNewLineSeparated
 * @param {Function} deps.LeanStatements
 */
export function createFunFamily(deps) {
    const {
        LeanUnary,
        LeanArgsNewLineSeparated,
        LeanStatements,
    } = deps;

    /** `fun` (λ-style binder head). */
    class Lean_fun extends LeanUnary {
        static input_priority = 18;
        get operator() {
            return 'fun';
        }
        get command() {
            return '\\lambda';
        }
        is_indented() {
            const parent = this.parent;
            return parent instanceof LeanArgsNewLineSeparated || parent instanceof LeanStatements;
        }
        toJSON() {
            return { [this.operator]: this.arg.toJSON() };
        }
        latexFormat() {
            return `${this.command}\\ %s`;
        }
        strFormat() {
            return `${this.operator} %s`;
        }
    }


    return {
        Lean_fun,
    };
}
