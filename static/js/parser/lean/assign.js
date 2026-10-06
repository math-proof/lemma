/**
 * Assignment `:=` (`LeanAssign`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanAssign extends LeanBinary {
    static { this.register(); }

    static input_priority = 18;

    get operator() {
        return ':=';
    }

    get command() {
        return ':=';
    }

    echo() {
        this.rhs.echo();
        if (this.lhs && typeof this.lhs.echo === 'function') this.lhs.echo();
    }

    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof L.LeanCaret) {
            const Ctor = typeof func === 'string' ? L[func] : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent < indent) {
            if (caret === this.rhs) {
                let out = caret;
                if (caret instanceof L.LeanCaret) {
                    caret.indent = indent;
                    this.rhs = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
                    out = this.rhs.push_newlines(newline_count - 1);
                } else if (caret instanceof L.LeanArgsNewLineSeparated) {
                    if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
                } else {
                    if (this.parent instanceof L.LeanCalc)
                        return this.parent.insert_newline(this, newline_count, indent, next);
                    const p = this.parent;
                    const brace = p instanceof L.LeanBrace ? p
                        : (p instanceof L.LeanStatements && p.parent instanceof L.LeanBrace) ? p.parent
                        : null;
                    if (brace && brace.indent < indent)
                        return brace.insert_newline(this, newline_count, indent, next);
                    out = this.push_args_indented(indent, newline_count, false);
                }
                return out;
            }
            throw new Error(`insert_newline is unexpected for ${this.constructor.name}`);
        }
        if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
    }

    insert_tactic(caret, type) {
        return this.insert_word(caret, type);
    }

    is_indented() {
        const p = this.parent;
        if (!p || p instanceof L.LeanArgsNewLineSeparated) return true;
        if (p instanceof L.LeanArgsIndented && p.rhs === this) return true;
        // Structure-instance fields inside a brace: `{ toFun := …, map_add' := … }`
        if (p instanceof L.LeanStatements && p.parent instanceof L.LeanBrace) return true;
        return false;
    }

    relocate_last_comment() {
        this.rhs.relocate_last_comment();
    }

    sep() {
        const rhs = this.rhs;
        if (rhs instanceof L.LeanArgsNewLineSeparated) {
            const lines = rhs.args;
            const l0 = lines[0];
            const l1 = lines[1];
            if (lines.length > 2 || !(l1 instanceof L.LeanArgsNewLineSeparated) || l0 instanceof L.LeanLineComment) {
                return '\n';
            }
        }
        if (rhs instanceof L.LeanArgsIndented) {
            return '\n';
        }
        if (
            rhs instanceof L.Lean_blacktriangleright &&
            rhs.lhs instanceof L.LeanArgsNewLineSeparated &&
            rhs.lhs.args[0] instanceof L.LeanLineComment
        ) {
            return '\n';
        }
        return ' ';
    }

    split(syntax) {
        const {rhs} = this;
        if (rhs instanceof L.LeanBy && rhs.arg instanceof L.LeanStatements) {
            const self = this.clone();
            const stmts = rhs.arg;
            self.rhs.arg = new L.LeanCaret(rhs.indent, rhs.level);
            const statements = [self];
            stmts.swap_echo_star(syntax, statements);
            return statements;
        }
        if (rhs instanceof L.LeanCalc) {
            if (syntax) syntax.calc = true;
            const self = this.clone();
            const calc = self.rhs;
            const statements = calc.split(syntax);
            calc.arg = new L.LeanCaret(calc.indent, calc.level);
            statements[0] = self;
            return statements;
        }
        return [this];
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}
