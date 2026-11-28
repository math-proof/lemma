/**
 * Lazy application `<|` (`Lean_lazy`).
 *
 * `a <| b` is `b a`, low precedence and right-associative.
 * This class keeps `input_priority` and `stack_priority`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
export class Lean_lazy extends LeanBinary {
    static { this.register(); }

    static input_priority = 20;
    get stack_priority() {
        return 19;
    }

    /**
     * `exact t <| by tac` — `by` is the lazy argument, not a second tactic
     * argument. Leaving the rhs caret empty stamps it on the `<|` line with
     * no span, so the line check anchors it to the term's first line.
     */
    insert(caret, func, type) {
        if (
            this.rhs === caret &&
            caret instanceof L.LeanCaret &&
            (func === 'LeanBy' || func === 'LeanCalc')
        ) {
            const Ctor = L[func];
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }
}
