/**
 * Type tests `is` / `is not` (`Lean_is`, `Lean_is_not`).
 *
 * PHP `operator` and `command` stay on `__get`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** `is`. */
export class Lean_is extends LeanBinary {
    static { this.register(); }

    static input_priority = 62;

    get operator() {
        return 'is';
    }

    get command() {
        return '{\\color{blue}\\text{is}}';
    }

    is_indented() {
        return this.parent instanceof L.LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    latexFormat() {
        return `{%s}\\ ${this.command}\\ {%s}`;
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

/** `is not`. */
export class Lean_is_not extends LeanBinary {
    static { this.register(); }

    static input_priority = 62;

    get command() {
        return '{\\color{blue}\\text{is not}}';
    }

    get operator() {
        return 'is not';
    }

    is_indented() {
        return this.parent instanceof L.LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}
