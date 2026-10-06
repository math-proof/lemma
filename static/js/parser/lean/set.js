/**
 * Set operators and inclusion: `LeanSetOperator` (`\\`, `∪`, `∩`) and
 * `⊆` / `⊂` / `⊇` / `⊃`.
 *
 * `⊇` / `⊃` extend `LeanLogic` (hanging indentation), imported from `logic.js`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { LeanBinaryBoolean } from './boolean.js';
import { LeanLogic } from './logic.js';

/** Set-theoretic binary (`\\`, `∪`, `∩`); abstract base like `LeanSetOperator`. */
export class LeanSetOperator extends LeanBinary {
    static { this.register(); }

    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class Lean_setminus extends LeanSetOperator {
    static { this.register(); }

    static input_priority = 70;

    get operator() {
        return '\\';
    }
}

export class Lean_cup extends LeanSetOperator {
    static { this.register(); }

    static input_priority = 65;

    get operator() {
        return '∪';
    }
}

export class Lean_cap extends LeanSetOperator {
    static { this.register(); }

    static input_priority = 70;

    get operator() {
        return '∩';
    }
}

/** `⊆`. */
export class Lean_subseteq extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '⊆';
    }
}

/** `⊂`. */
export class Lean_subset extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '⊂';
    }
}

/** `⊇`. */
export class Lean_supseteq extends LeanLogic {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '⊇';
    }
}

/** `⊃`. */
export class Lean_supset extends LeanLogic {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '⊃';
    }
}
