/**
 * Logic / boolean connectives: `LeanLogic` and `&&` / `||` / `^^` / `∨` / `∧`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinaryBoolean } from './boolean.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanLogic extends LeanBinaryBoolean {
    static { this.register(); }

    /** @type {boolean|undefined} */
    hanging_indentation;

    is_indented() {
        return this.parent instanceof L.LeanStatements;
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

export class LeanLogicAnd extends LeanLogic {
    static { this.register(); }

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

export class LeanLogicOr extends LeanLogic {
    static { this.register(); }

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

export class LeanLogicXor extends LeanLogic {
    static { this.register(); }

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

export class Lean_lor extends LeanLogic {
    static { this.register(); }

    static input_priority = 30;

    get stack_priority() {
        return 29;
    }

    get operator() {
        return '∨';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.rhs && caret instanceof L.LeanCaret) {
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

export class Lean_land extends LeanLogic {
    static { this.register(); }

    static input_priority = 35;

    get stack_priority() {
        return 34;
    }

    get operator() {
        return '∧';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.rhs && caret instanceof L.LeanCaret) {
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
