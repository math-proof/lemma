/**
 * Logic / boolean connectives: `LeanLogic` and `&&` / `||` / `^^` / `∨` / `∧`.
 *
 * `LeanBinaryBoolean` stays in `lean.js`. `LeanStatements` is filled on
 * `logicLate` after that class exists; methods only use it via `instanceof`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinaryBoolean
 * @param {Function} deps.LeanCaret
 * @param {object} deps.logicLate
 */
export function createLogicFamily(deps) {
    const { LeanBinaryBoolean, LeanCaret, logicLate } = deps;
    function lateClass(name) {
        function Ctor() {}
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = logicLate[name];
                if (real == null) throw new Error(`${name} used before logic registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanStatements = lateClass('LeanStatements');

    class LeanLogic extends LeanBinaryBoolean {
        /** @type {boolean|undefined} */
        hanging_indentation;

        is_indented() {
            return this.parent instanceof LeanStatements;
        }

        sep() {
            if (this.hanging_indentation) {
                const indent = this.rhs.indent ?? 0;
                return '\n' + ' '.repeat(indent);
            }
            return ' ';
        }

        strFormat() {
            const sep = this.sep();
            return `%s ${this.operator}${sep}%s`;
        }
    }

    class LeanLogicAnd extends LeanLogic {
        static input_priority = 37;

        get stack_priority() {
            return 50;
        }

        get command() {
            return '\\&\\&';
        }

        get operator() {
            return '&&';
        }

        toJSON() {
            const lhs = this.lhs.toJSON();
            const rhs = this.rhs.toJSON();
            const f = this.func;
            const rec = lhs && typeof lhs === 'object' ? lhs : null;
            if (this.lhs instanceof LeanLogicAnd && rec && Array.isArray(rec[f])) {
                return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
            }
            return { [f]: [lhs, rhs] };
        }

        strFormat() {
            return `%s ${this.operator} %s`;
        }
    }

    class LeanLogicOr extends LeanLogic {
        static input_priority = 37;

        get stack_priority() {
            return 36;
        }

        get command() {
            return '\\|\\|';
        }

        get operator() {
            return '||';
        }

        toJSON() {
            const lhs = this.lhs.toJSON();
            const rhs = this.rhs.toJSON();
            const f = this.func;
            const rec = lhs && typeof lhs === 'object' ? lhs : null;
            if (this.lhs instanceof LeanLogicOr && rec && Array.isArray(rec[f])) {
                return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
            }
            return { [f]: [lhs, rhs] };
        }

        strFormat() {
            return `%s ${this.operator} %s`;
        }
    }

    class LeanLogicXor extends LeanLogic {
        static input_priority = 33;

        get command() {
            return '\\^\\^';
        }

        get operator() {
            return '^^';
        }

        strFormat() {
            return `%s ${this.operator} %s`;
        }
    }

    class Lean_lor extends LeanLogic {
        static input_priority = 30;

        get stack_priority() {
            return 29;
        }

        get operator() {
            return '∨';
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.rhs && caret instanceof LeanCaret) {
                if (indent >= this.indent) {
                    if (indent === this.indent) indent = this.indent + 2;
                    this.hanging_indentation = true;
                    caret.indent = indent;
                    return caret;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        toJSON() {
            return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
        }
    }

    class Lean_land extends LeanLogic {
        static input_priority = 35;

        get stack_priority() {
            return 34;
        }

        get operator() {
            return '∧';
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.rhs && caret instanceof LeanCaret) {
                if (indent >= this.indent) {
                    this.hanging_indentation = true;
                    caret.indent = indent;
                    return caret;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        toJSON() {
            return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
        }
    }

    return {
        LeanLogic,
        LeanLogicAnd,
        LeanLogicOr,
        LeanLogicXor,
        Lean_lor,
        Lean_land,
    };
}
