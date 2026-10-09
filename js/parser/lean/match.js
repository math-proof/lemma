/**
 * Match: `Lean_match` (`match`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanArgs } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class Lean_match extends LeanArgs {
    static { this.register(); }

    /**
     * @param {Lean} subject
     * @param {number} indent
     * @param {number} level
     * @param {import('../node.js').Node | null} [parent]
     */
    constructor(subject, indent, level, parent = null) {
        super([subject], indent, level, parent);
    }

    get stack_priority() {
        return L.LeanColon.input_priority - 1;
    }

    get subject() {
        return this.args[0];
    }
    set subject(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get with() {
        return this.args[1] ?? null;
    }
    set with(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    get operator() {
        return 'match';
    }

    is_indented() {
        return true;
    }

    strFormat() {
        if (this.with) return `${this.operator} %s %s`;
        return `${this.operator} %s`;
    }

    latexFormat() {
        if (this.with) {
            const n = this.with.args.length;
            const cases = Array(n).fill('%s').join('\\\\');
            return `\\begin{cases} ${cases} \\end{cases}`;
        }
        return 'match\\ %s';
    }

    latexArgs(syntax) {
        const subject = this.subject.toLatex(syntax);
        const w = this.with;
        if (w) {
            return w.args.map((row) => {
                const a = row.arg;
                const type = a.lhs.toLatex(syntax);
                const value = a.rhs.toLatex(syntax);
                return `{${value}} & {\\color{blue}\\text{if}}\\ \\: ${subject}\\ =\\ ${type}`;
            });
        }
        return [subject];
    }

    insert(caret, func, type) {
        if (!this.with && func === 'LeanWith') {
            const c = new L.LeanCaret(this.indent, caret.level);
            const Ctor = L[func];
            const w = new Ctor(c, this.indent, c.level);
            this.with = w;
            return c;
        }
        throw new Error(`Lean_match.insert: unexpected for ${String(func)}`);
    }

    insert_comma(caret) {
        if (caret === this.subject) {
            const c = new L.LeanCaret(this.indent, caret.level);
            this.subject = new L.LeanArgsCommaSeparated([this.subject, c], this.indent, caret.level);
            return c;
        }
        if (this.parent) return this.parent.insert_comma(this);
    }

    relocate_last_comment() {
        const w = this.with;
        if (w instanceof L.LeanWith) w.relocate_last_comment();
    }

    insert_tactic(caret, token) {
        if (caret instanceof L.LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    split(syntax) {
        const w = this.with;
        if (!w) return [this];
        const self = this.clone();
        if (self.with) self.with.args = [];
        const statements = [self];
        for (const stmt of w.args) {
            statements.push(...stmt.split(syntax));
        }
        return statements;
    }

    isProp(vars) {
        const w = this.with;
        if (!w) return undefined;
        const cases = w.args;
        const first = cases[0];
        if (first instanceof L.LeanBar) {
            const arrow = first.arg;
            if (arrow instanceof L.LeanRightarrow) {
                return arrow.rhs.isProp(vars);
            }
        }
        return undefined;
    }
}
