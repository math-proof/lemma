/**
 * Lambda binder head: `Lean_fun` (`fun` / `λ`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** `fun` (λ-style binder head). */
export class Lean_fun extends LeanUnary {
    static { this.register(); }

    static input_priority = 18;
    get operator() {
        return 'fun';
    }
    get command() {
        return '\\lambda';
    }
    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanArgsNewLineSeparated || parent instanceof L.LeanStatements;
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
