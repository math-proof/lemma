/**
 * Set operators and inclusion: `LeanSetOperator` (`\\`, `∪`, `∩`) and
 * `⊆` / `⊂` / `⊇` / `⊃`.
 *
 * `⊇` / `⊃` extend `LeanLogic` (hanging indentation). That base is created by
 * `createLogicFamily` and passed in. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanBinaryBoolean
 * @param {Function} deps.LeanLogic
 */
export function createSetFamily(deps) {
    const { LeanBinary, LeanBinaryBoolean, LeanLogic } = deps;

    /** Set-theoretic binary (`\\`, `∪`, `∩`); abstract base like `LeanSetOperator`. */
    class LeanSetOperator extends LeanBinary {
        sep() {
            return ' ';
        }

        strFormat() {
            return `%s ${this.operator} %s`;
        }
    }

    class Lean_setminus extends LeanSetOperator {
        static input_priority = 70;

        get operator() {
            return '\\';
        }
    }

    class Lean_cup extends LeanSetOperator {
        static input_priority = 65;

        get operator() {
            return '∪';
        }
    }

    class Lean_cap extends LeanSetOperator {
        static input_priority = 70;

        get operator() {
            return '∩';
        }
    }

    /** `⊆`. */
    class Lean_subseteq extends LeanBinaryBoolean {
        static input_priority = 50;

        get operator() {
            return '⊆';
        }
    }

    /** `⊂`. */
    class Lean_subset extends LeanBinaryBoolean {
        static input_priority = 50;

        get operator() {
            return '⊂';
        }
    }

    /** `⊇`. */
    class Lean_supseteq extends LeanLogic {
        static input_priority = 50;

        get operator() {
            return '⊇';
        }
    }

    /** `⊃`. */
    class Lean_supset extends LeanLogic {
        static input_priority = 50;

        get operator() {
            return '⊃';
        }
    }

    return {
        LeanSetOperator,
        Lean_setminus,
        Lean_cup,
        Lean_cap,
        Lean_subseteq,
        Lean_subset,
        Lean_supseteq,
        Lean_supset,
    };
}

