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
                    // `have h : a =\n    b :=\n  by tac` — `:=` sits on the
                    // continuation of the type. A newline list here stays empty
                    // once `by` / `calc` climbs out to the `have`, and that
                    // empty list is stamped on the `:=` line rather than the
                    // type's first line. Leave the cursor so the keyword
                    // becomes the proof.
                    const lhsLine = this.lhs?.line;
                    if (
                        (next === 'by' || next === 'calc') &&
                        typeof lhsLine === 'number' &&
                        typeof caret.line === 'number' &&
                        caret.line > lhsLine
                    )
                        return caret;
                    this.rhs = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
                    out = this.rhs.push_newlines(newline_count - 1);
                } else if (caret instanceof L.LeanArgsNewLineSeparated) {
                    if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
                } else {
                    if (this.parent instanceof L.LeanCalc)
                        return this.parent.insert_newline(this, newline_count, indent, next);
                    const p = this.parent;
                    const {LeanBrace, LeanStatements, LeanWith} = L;
                    // first field of `{ a := 1⏎ b := 2 }` / `{ s with a := 1⏎ b := 2 }`: the brace / `with` opens the
                    // structure-instance body. A deeper line after a field of that body continues the field's value.
                    const owner = p instanceof LeanBrace ? p
                        : p instanceof LeanWith && p.isStructUpdate() ? p
                        : (p instanceof LeanStatements && p.parent instanceof LeanBrace && p.structInst !== true) ? p.parent
                        : null;
                    const brace = owner instanceof LeanWith ? owner.parent.parent : owner;
                    if (brace && brace.indent < indent)
                        return owner.insert_newline(this, newline_count, indent, next);
                    // `set q := expr\n    with h` — `with` names the equation.
                    // A continuation caret under `:=` stays empty once `with`
                    // climbs out, and reprints as a blank indented line.
                    if (next === 'with' && p instanceof L.Lean_let && !p.is_term()) {
                        const c = new L.LeanCaret(indent, caret.level).stampFollowingLine(Math.max(0, newline_count - 1));
                        c.hangingModifier = true;
                        p.push(c);
                        return c;
                    }
                    out = this.push_args_indented(indent, newline_count, false);
                }
                return out;
            }
            throw new Error(`insert_newline is unexpected for ${this.constructor.name}`);
        }
        // `· obtain p :=\n  term` — the value lines up with `obtain`, not deeper.
        // A newline list would also swallow the following tactics, which share
        // that column. Keep the caret so only this line becomes the value.
        if (
            caret === this.rhs &&
            caret instanceof L.LeanCaret &&
            indent === this.indent &&
            this.parent instanceof L.LeanTactic
        ) {
            caret.indent = indent;
            caret.stampFollowingLine(newline_count - 1);
            return caret;
        }
        // `fg :=\n  B.dual …` — the value is not deeper than the field name.
        // Leaving the caret empty starts a new statement and parses `B.dual` at
        // the module, which drops the dot.
        if (
            caret === this.rhs &&
            caret instanceof L.LeanCaret &&
            indent > 0 &&
            this.parent instanceof L.LeanStatements &&
            this.parent.structInst === true
        ) {
            caret.indent = indent;
            this.rhs = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
            return this.rhs.push_newlines(newline_count - 1);
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
        if (p instanceof L.LeanStatements && (p.parent instanceof L.LeanBrace || p.structInst === true)) return true;
        // `surj y := by` parsed as its own statement after a `where` field dedents.
        if (p instanceof L.LeanModule && this.indent > 0) return true;
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
            return rhs.line != null && rhs.line === this._birthLine ? ' ' : '\n';
        }
        // `b :=\n  by tac` — the proof keyword was parsed on the next line.
        // `· obtain p :=\n  term` — the value is a later line, aligned with the tactic.
        if (rhs instanceof L.LeanBy || rhs instanceof L.LeanCalc || this.parent instanceof L.LeanTactic) {
            const lhsEnd = Lean.lastSourceLine(this.lhs);
            if (lhsEnd >= 0 && typeof rhs.line === 'number' && rhs.line > lhsEnd) return '\n';
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

    strArgs() {
        const args = super.strArgs();
        if (this.rhs instanceof L.LeanArgsIndented && this.sep() === ' ') {
            return [args[0], String(args[1]).replace(/^ +/, '')];
        }
        return args;
    }
}
