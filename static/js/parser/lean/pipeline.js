/**
 * Pipeline dot `|>.` (`LeanMethodChaining`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';

/** Pipeline `|>.`. */
export class LeanMethodChaining extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;

    get stack_priority() {
        return 59;
    }

    latexFormat() {
        return '%s\\ \\texttt{|>.}%s';
    }

    sep() {
        return '';
    }

    strFormat() {
        return '%s |>.%s';
    }
}
