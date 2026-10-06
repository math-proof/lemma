/**
 * Lazy application `<|` (`Lean_lazy`).
 *
 * `a <| b` is `b a`, low precedence and right-associative. PHP `operator`,
 * `sep`, and `strFormat` stay in the PHP class; JS keeps only
 * `input_priority` and `stack_priority`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';

/** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
export class Lean_lazy extends LeanBinary {
    static { this.register(); }

    static input_priority = 20;
    get stack_priority() {
        return 19;
    }
}
