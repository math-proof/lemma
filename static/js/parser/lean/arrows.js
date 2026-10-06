/**
 * Arrows: `LeanRightarrow` (`=>`), `Lean_rightarrow` (`→`), `Lean_mapsto` (`↦`),
 * and `Lean_leftarrow` (`←`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary, LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanRightarrow extends LeanBinary {
    static { this.register(); }

    static input_priority = 19;

    get operator() {
        return '=>';
    }

    echo() {
        const token = [];
        var {parent} = this;
        if (parent instanceof L.LeanBar && (parent = parent.parent) instanceof L.LeanWith && ((parent = parent.parent) instanceof L.Lean_match || (parent instanceof L.LeanTactic && parent.tacticName === 'induction'))) {
            token.push(new L.LeanToken('⊢', this.rhs.indent, this.rhs.level));
            const subject = parent.args[0];
            if (subject instanceof L.LeanArgsCommaSeparated) {
                for (const sujet of subject.args) {
                    if (sujet instanceof L.LeanColon) token.push(sujet.lhs);
                }
            } else if (subject instanceof L.LeanColon) {
                token.push(subject.lhs);
            }
        }
        const expr = this.lhs;
        if (expr instanceof L.LeanArgsSpaceSeparated) {
            let func;
            if (expr.args[0] instanceof L.LeanToken) func = expr.args[0].text;
            else if (
                expr.args[0] instanceof L.LeanProperty &&
                expr.args[0].lhs instanceof L.LeanCaret &&
                expr.args[0].rhs instanceof L.LeanToken
            ) {
                func = expr.args[0].rhs.text;
            }
            else
                func = null;
            let start;
            switch (func) {
                case 'succ':
                case 'ofNat':
                case 'negSucc':
                    start = 2;
                    break;
                case 'cons':
                    start = 3;
                    break;
                default:
                    start = 1;
            }
            token.push(...expr.args.slice(start));
        } else if (expr instanceof L.LeanAngleBracket) {
            if (expr.arg instanceof L.LeanArgsCommaSeparated) {
                // | ⟨v, property⟩ =>
                token.push(...expr.arg.args.slice(1));
            }
        } else if (expr instanceof L.LeanArgsCommaSeparated) {
            // | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
            for (const arg of expr.args) {
                if (arg instanceof L.LeanAngleBracket && arg.arg instanceof L.LeanArgsCommaSeparated) {
                    token.push(arg.arg.args[1]);
                }
            }
        }
        const stmt = this.rhs;
        stmt.echo();
        if (token.length && stmt instanceof L.LeanStatements) {
            const {indent, level} = stmt.args[0];
            let payload;
            if (token.length > 1) {
                payload = new L.LeanArgsCommaSeparated(
                    token.map((arg) => {
                        const c = arg.clone();
                        c.indent = indent;
                        c.level = level;
                        return c;
                    }),
                    indent,
                    level
                );
            } else {
                const [only] = token;
                payload = only;
            }
            stmt.unshift(new L.LeanTactic('echo', payload, indent, level));
        }
    }

    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof L.LeanCaret) {
            const Ctor = typeof func === 'string' ? L[func] : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret === this.rhs) {
            if (caret instanceof L.LeanCaret || caret instanceof L.LeanLineComment) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const stmts = new L.LeanStatements([caret], indent, caret.level);
                this.replace(caret, stmts);
                let nl = newline_count;
                if (!(caret instanceof L.LeanCaret)) nl++;
                let last = caret;
                for (let i = 1; i < nl; i++) {
                    last = new L.LeanCaret(indent, caret.level);
                    stmts.push(last);
                }
                return last;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        return false;
    }

    relocate_last_comment() {
        this.rhs.relocate_last_comment();
    }

    sep() {
        return this.rhs instanceof L.LeanStatements ? '\n' : this.rhs instanceof L.LeanCaret ? '' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        let lhs = '%s';
        if (!(this.lhs instanceof L.LeanCaret)) lhs += ' ';
        return `${lhs}${this.operator}${sep}%s`;
    }
}

export class Lean_rightarrow extends LeanBinary {
    static { this.register(); }

    static input_priority = 25;

    /** `→ₗ` / `→L` — the subscript letter (e.g. the `ₗ` in `→ₗ[ℝ]`). */
    subscript = '';
    /** `→ₗ[ℝ]` — the bracketed scalar ring modifier (e.g. `ℝ`). */
    modifier = '';

    get stack_priority() {
        return 24;
    }

    get operator() {
        return '→';
    }

    /** `→ₗ` or `→L` rendered with the subscript attached (for echo / str). */
    arrowStr() {
        return this.subscript ? `→${this.subscript}` : '→';
    }

    /** LaTeX for the arrow including subscript and optional `[modifier]`. */
    arrowLatex() {
        let op = '\\to';
        if (this.subscript) {
            const map = L.LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            op += `_{${inner}}`;
        }
        if (this.modifier) op += `[${this.modifier}]`;
        return op;
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.rhs) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            const stmts = new L.LeanStatements([caret], indent, caret.level);
            this.replace(caret, stmts);
            for (let i = 1; i < newline_count; i++) {
                const c = new L.LeanCaret(indent, caret.level);
                stmts.push(c);
            }
            return stmts.args[stmts.args.length - 1];
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        return this.parent instanceof L.LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [vars]
     */
    isProp(vars) {
        const rhs = this.rhs;
        if ((rhs instanceof L.LeanToken && (rhs.text === '0' || rhs.text === '∞')) ||
            ((rhs instanceof L.LeanPlus || rhs instanceof L.LeanNeg) && rhs.arg instanceof L.LeanToken && rhs.arg.text === '∞') ||
            ((rhs instanceof L.LeanPosPart || rhs instanceof L.LeanNegPart) && rhs.arg instanceof L.LeanToken && rhs.arg.text === '0'))
            return true;
        const lhs = this.lhs;
        const lhsOk =
            (lhs instanceof L.LeanToken && (vars[lhs.text] ?? 'Prop') === 'Prop') ||
            (!(lhs instanceof L.LeanToken) && lhs.isProp(vars));
        const rhsOk =
            (rhs instanceof L.LeanToken && (vars[rhs.text] ?? 'Prop') === 'Prop') ||
            (!(rhs instanceof L.LeanToken) && rhs.isProp(vars));
        return Boolean(lhsOk && rhsOk);
    }

    sep() {
        const {rhs} = this;
        if (rhs instanceof L.LeanStatements) return '\n';
        if (rhs instanceof L.LeanCaret) return '';
        return ' ';
    }

    strFormat() {
        const sep = this.sep();
        const arrow = this.arrowStr() + (this.modifier ? `[${this.modifier}]` : '');
        return `%s ${arrow}${sep}%s`;
    }

    latexFormat() {
        const sep = this.sep();
        return `{%s} ${this.arrowLatex()}${sep}{%s}`;
    }
}

export class Lean_mapsto extends LeanBinary {
    static { this.register(); }

    get stack_priority() {
        return 23;
    }

    get operator() {
        return '↦';
    }

    insert(caret, func, type) {
        // `fun x ↦ by …` — the term-level `by` fills the lambda body caret,
        // mirroring `LeanRightarrow.insert` for `fun x => by …`.
        if (this.rhs === caret && caret instanceof L.LeanCaret) {
            const Ctor = typeof func === 'string' ? L[func] : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.rhs) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            const stmts = new L.LeanStatements([caret], indent, caret.level);
            this.replace(caret, stmts);
            for (let i = 1; i < newline_count; i++) {
                const c = new L.LeanCaret(indent, caret.level);
                stmts.push(c);
            }
            return stmts.args[stmts.args.length - 1];
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        return false;
    }

    sep() {
        const {rhs} = this;
        if (rhs instanceof L.LeanStatements) return '\n';
        if (rhs instanceof L.LeanCaret) return '';
        return ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

/** Unary `←`. */
export class Lean_leftarrow extends LeanUnary {
    static { this.register(); }

    get operator() {
        return '←';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}
