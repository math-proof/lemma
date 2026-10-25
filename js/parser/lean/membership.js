/**
 * Membership and iff: `∈` / `∉` / `↔` (`Lean_in`, `Lean_notin`, `Lean_leftrightarrow`).
 *
 * All three extend `LeanBinaryBoolean`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinaryBoolean } from './boolean.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** Set / arrow: `∈` (membership). */
export class Lean_in extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '∈';
    }

    /**
     * LaTeX-only: drop `(i : ℕ)` / `(i : Nat)` (and bare `i : ℕ`) on the ∈ element.
     * Lean still needs the cast when `i : Fin m` and the set is `Finset ℕ` (e.g. `Finset.Ico`);
     * pretty-print like choose's `((i : ℕ).choose j)` → `\binom{i}{j}`.
     * @param {import('./base.js').Lean} node
     * @returns {import('./base.js').Lean}
     */
    static peelLatexElem(node) {
        let n = node;
        if (n instanceof L.LeanParenthesis) {
            if (n.arg instanceof L.LeanColon && n.arg.rhs instanceof L.LeanToken)
                return n.arg.lhs;
            if (!(n.arg instanceof L.LeanColon))
                return n.arg;
        }
        if (n instanceof L.LeanColon && n.rhs instanceof L.LeanToken)
            return n.lhs;
        return n;
    }

    latexArgs(syntax) {
        const lhs = Lean_in.peelLatexElem(this.lhs);
        let rhs = this.rhs;
        if (rhs instanceof L.LeanParenthesis && rhs.arg instanceof L.LeanIte) rhs = rhs.arg;
        return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
    }
}
export class Lean_notin extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '∉';
    }

    latexArgs(syntax) {
        const lhs = L.Lean_in.peelLatexElem(this.lhs);
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
/** `↔`. */
export class Lean_leftrightarrow extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 20;

    get operator() {
        return '↔';
    }
}
