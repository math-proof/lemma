/**
 * Abstract boolean-valued binary base (`LeanBinaryBoolean`).
 *
 * Relational comparisons, membership, and logic connectives extend this.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanProp } from './utility.js';
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanBinaryBoolean extends LeanProp(LeanBinary) {
    static { this.register(); }

    append(new_, type) {
        const {indent, level} = this;
        const caret = new L.LeanCaret(indent, level);
        if (typeof new_ === 'string') {
            const Ctor = L[new_];
            const newNode = new Ctor(caret, indent, level);
            this.rhs = new L.LeanArgsSpaceSeparated([this.rhs, newNode], indent, level);
            return caret;
        } else {
            this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, new_], indent, level));
            return new_;
        }
    }

    insert_colon(caret) {
        if (caret === this.rhs) {
            const newCaret = new L.LeanCaret(caret.indent, caret.level);
            this.parent.replace(this, new L.LeanColon(this, newCaret, caret.indent, caret.level));
            return newCaret;
        }
        return caret.push_binary(L.LeanColon);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.rhs === caret && caret instanceof L.LeanCaret && indent >= this.indent) {
            caret.indent = indent;
            return caret;
        }
        if (this.rhs === caret && indent > this.indent) {
            return this.parent.push_args_indented(indent, newline_count, false);
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        const {parent} = this;
        return parent instanceof L.LeanStatements || (parent instanceof L.LeanArgsNewLineSeparated && this.indent > 0);
    }

    sep() {
        return this.rhs instanceof L.LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}
