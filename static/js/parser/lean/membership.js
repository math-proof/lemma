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

    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof L.LeanParenthesis && !(lhs.arg instanceof L.LeanColon)) lhs = lhs.arg;
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
        let lhs = this.lhs;
        if (lhs instanceof L.LeanParenthesis) lhs = lhs.arg;
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
