/**
 * Negation: `Lean_lnot` (`¬`) and `LeanNot` (`!`).
 *
 * `LeanNot.is_indented` checks `LeanStatements` via `instanceof`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanProp } from './utility.js';
import { LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** Logical not `¬`. */
export class Lean_lnot extends LeanProp(LeanUnary) {
    static { this.register(); }

    static input_priority = 40;

    get operator() {
        return '¬';
    }

    strFormat() {
        return `${this.operator}%s`;
    }
}

export class LeanNot extends LeanProp(LeanUnary) {
    static { this.register(); }

    static input_priority = 40;

    get operator() {
        return '!';
    }

    get command() {
        return '\\text{!}';
    }

    is_indented() {
        return this.parent instanceof L.LeanStatements;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    strFormat() {
        return `${this.operator}%s`;
    }
}
