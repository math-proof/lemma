/**
 * Membership and iff: `∈` / `∉` / `↔` (`Lean_in`, `Lean_notin`, `Lean_leftrightarrow`).
 *
 * All three extend `LeanBinaryBoolean`. `LeanParenthesis` and `LeanIte` are
 * filled on `membershipLate` after those classes exist; methods only use them
 * via `instanceof`. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinaryBoolean
 * @param {Function} deps.LeanColon
 * @param {object} deps.membershipLate
 */
export function createMembershipFamily(deps) {
    const { LeanBinaryBoolean, LeanColon, membershipLate } = deps;
    function lateClass(name) {
        function Ctor() {}
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = membershipLate[name];
                if (real == null) throw new Error(`${name} used before membership registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanParenthesis = lateClass('LeanParenthesis');
    const LeanIte = lateClass('LeanIte');

    /** Set / arrow: `∈` (membership). */
    class Lean_in extends LeanBinaryBoolean {
        static input_priority = 50;

        get operator() {
            return '∈';
        }

        latexArgs(syntax) {
            let lhs = this.lhs;
            if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon)) lhs = lhs.arg;
            let rhs = this.rhs;
            if (rhs instanceof LeanParenthesis && rhs.arg instanceof LeanIte) rhs = rhs.arg;
            return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
        }
    }
    class Lean_notin extends LeanBinaryBoolean {
        static input_priority = 50;

        get operator() {
            return '∉';
        }

        latexArgs(syntax) {
            let lhs = this.lhs;
            if (lhs instanceof LeanParenthesis) lhs = lhs.arg;
            return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
        }
    }
    /** `↔`. */
    class Lean_leftrightarrow extends LeanBinaryBoolean {
        static input_priority = 20;

        get operator() {
            return '↔';
        }
    }


    return {
        Lean_in,
        Lean_notin,
        Lean_leftrightarrow,
    };
}
