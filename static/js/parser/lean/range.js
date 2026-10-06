/**
 * Interval notation `a..b` (`LeanUpto`).
 *
 * JS `sep` inserts a space when the right-hand side is still a caret; PHP `sep`
 * stays empty.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/**
 * Interval notation `a..b` used by `∫ x in a..b, f x` (Mathlib `notation3 "a".."b"`).
 * Binds looser than arithmetic/relational nodes, matching the term-level parsing of the bounds.
 */
export class LeanUpto extends LeanBinary {
    static { this.register(); }

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
        return this.rhs instanceof L.LeanCaret ? ' ' : '';
    }
}
