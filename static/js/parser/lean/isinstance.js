/**
 * Type tests `is` / `is not` (`Lean_is`, `Lean_is_not`).
 *
 * `LeanBinary` already exists and is passed in. `LeanStatements` is filled
 * on `isinstanceLate` (`is_indented` checks the parent). This factory does
 * not import `lean.js`. PHP `operator` and `command` stay on `__get`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {object} deps.isinstanceLate
 */
export function createIsInstanceFamily(deps) {
    const { LeanBinary, isinstanceLate } = deps;
    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = isinstanceLate[name];
                if (real == null) throw new Error(`${name} used before isinstance registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = isinstanceLate[name];
                if (real == null) throw new Error(`${name} used before isinstance registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanStatements = lateCtor('LeanStatements');

    /** `is`. */
    class Lean_is extends LeanBinary {
        static input_priority = 62;

        get operator() {
            return 'is';
        }

        get command() {
            return '{\\color{blue}\\text{is}}';
        }

        is_indented() {
            return this.parent instanceof LeanStatements;
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
    class Lean_is_not extends LeanBinary {
        static input_priority = 62;

        get command() {
            return '{\\color{blue}\\text{is not}}';
        }

        get operator() {
            return 'is not';
        }

        is_indented() {
            return this.parent instanceof LeanStatements;
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

    return {
        Lean_is,
        Lean_is_not,
    };
}
