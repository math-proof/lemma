/**
 * If-then-else: `LeanIte` (`if` / `then` / `else`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanArgs } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanIte extends LeanArgs {
    static { this.register(); }

    static input_priority = 60;

    constructor(args, indent, level, parent = null) {
        super(args, indent, level, parent);
        /** `true` until a newline or a non-one-line `else` is parsed. */
        this.inline = true;
    }

    get stack_priority() {
        return 23;
    }

    get if() {
        return this.args[0];
    }
    set if(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get then() {
        return this.args[1] ?? null;
    }
    set then(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
        if (v && !(v instanceof L.LeanCaret) && !LeanIte.is_oneliner(v)) this.not_inline();
    }

    get else() {
        return this.args[2] ?? null;
    }
    set else(v) {
        while (this.args.length < 3) this.args.push(undefined);
        this.args[2] = v;
        if (v != null && typeof v === 'object') v.parent = this;
        if (!LeanIte.is_oneliner(v)) this.not_inline();
    }

    echo() {
        const [$if, then, $else] = this.args;
        let token = null;
        if ($if instanceof L.LeanColon) {
            token = $if.args[0];
        }
        if (then) this.echo_then(token);
        if ($else) this.echo_else(token);
    }

    /** @param {Lean | null} token */
    echo_else(token) {
        const part = this.else;
        part.echo();
        if (token) {
            if (part instanceof LeanIte) LeanIte.echo_part(part.then, token);
            else LeanIte.echo_part(part, token);
        }
    }

    /** @param {Lean | null} token */
    echo_then(token) {
        const part = this.then;
        part.echo();
        if (token) LeanIte.echo_part(part, token);
    }

    insert_colon(caret) {
        if (caret === this.if) {
            const c = new L.LeanCaret(caret.indent, caret.level);
            this.replace(caret, new L.LeanColon(caret, c, caret.indent, caret.level));
            return c;
        }
        return caret.push_binary(L.LeanColon);
    }

    insert_else(caret) {
        if (!this.else) {
            const c = new L.LeanCaret(this.indent + 2, caret.level);
            this.else = c;
            this.newlineBehindElse = false;
            return c;
        }
        if (this.parent) return this.parent.insert_else(this);
    }

    insert_if(caret) {
        if (caret instanceof L.LeanCaret) {
            if (caret === this.else) {
                const indent = this.newlineBehindElse ? caret.indent : this.indent;
                this.else = new LeanIte([caret], indent, caret.level);
                return caret;
            }
            if (caret === this.then) {
                if (caret.indent < this.indent + 2) caret.indent = this.indent + 2;
                this.then = new LeanIte([caret], caret.indent, caret.level);
                return caret;
            }
        }
        throw new Error(`LeanIte.insert_if: unexpected for ${this.constructor.name}`);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.then) {
            if (caret instanceof L.LeanCaret || caret instanceof L.LeanTactic || caret instanceof L.Lean_let || next === 'else')
                this.not_inline();
            if (caret instanceof L.LeanTactic || caret instanceof L.Lean_let) {
                const stmt = new L.LeanStatements([caret], caret.indent, caret.level);
                this.then = stmt;
                for (let i = 0; i < newline_count; i++) {
                    caret = new L.LeanCaret(caret.indent, caret.level);
                    stmt.push(caret);
                }
            }
            return caret;
        }
        if (caret === this.else) {
            if (caret instanceof L.LeanCaret || caret instanceof L.LeanTactic || caret instanceof L.Lean_let) {
                this.not_inline();
                this.newlineBehindElse = true;
            }
            if (caret instanceof L.LeanCaret) return caret;
            if (indent > this.indent && (caret instanceof L.LeanTactic || caret instanceof L.Lean_let)) {
                const stmt = new L.LeanStatements([caret], caret.indent, caret.level);
                this.else = stmt;
                for (let i = 0; i < newline_count; i++) {
                    caret = new L.LeanCaret(caret.indent, caret.level);
                    stmt.push(caret);
                }
                return caret;
            }
        }
        if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
    }

    insert_tactic(caret, func) {
        if (caret instanceof L.LeanCaret) {
            this.replace(
                caret,
                new L.LeanTactic(func, caret, this.indent + 2, caret.level),
            );
            return caret;
        }
        const c = new L.LeanCaret(this.indent + 2, caret.level);
        this.replace(
            caret,
            new L.LeanStatements(
                [caret, new L.LeanTactic(func, c, this.indent + 2, caret.level)],
                this.indent + 2,
                caret.level,
            ),
        );
        return c;
    }

    insert_then(caret) {
        if (!this.then) {
            const c = new L.LeanCaret(this.indent + 2, caret.level);
            this.then = c;
            return c;
        }
        throw new Error(`LeanIte.insert_then: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        const p = this.parent;
        if (p instanceof LeanIte && p.inline) return false;
        return !p || p instanceof L.LeanStatements || p instanceof L.LeanArgsNewLineSeparated || (p instanceof LeanIte && (!p.then || this === p.then));
    }

    /** Branch is a one-liner (nested `LeanIte` only if that node is itself `inline`). */
    static is_oneliner(node) {
        if (node == null || typeof node !== 'object') return false;
        if (node instanceof L.LeanStatements || node instanceof L.LeanArgsNewLineSeparated) return false;
        if (node instanceof LeanIte) return node.inline;
        return true;
    }

    latexArgs(syntax) {
        const cases = [];
        let cur = this;
        while (true) {
            const [$if, then, els] = cur.strip_parenthesis();
            const ifL = $if.toLatex(syntax);
            const thenL = then.toLatex(syntax);
            cases.push(`{${thenL}} & {\\color{blue}\\text{if}}\\ ${ifL} `);
            if (!(els instanceof LeanIte)) {
                cases.push(els.toLatex(syntax));
                break;
            }
            cur = els;
        }
        return cases;
    }

    latexFormat() {
        let n = 0;
        let cur = this;
        while (true) {
            const [, , els] = cur.strip_parenthesis();
            n++;
            if (!(els instanceof LeanIte)) break;
            cur = els;
        }
        const rows = Array(n).fill('%s').join('\\\\');
        return `\\begin{cases} ${rows} \\\\ {%s} & {\\color{blue}\\text{else}} \\end{cases}`;
    }

    /** Mark this `ite` (and any enclosing `ite` that uses it as a branch) as not inline. */
    not_inline() {
        this.inline = false;
        const p = this.parent;
        if (p instanceof LeanIte && (p.then === this || p.else === this)) p.not_inline();
    }

    relocate_last_comment() {
        const els = this.else;
        if (els instanceof L.LeanStatements || els instanceof LeanIte) els.relocate_last_comment();
    }

    set_line(line) {
        this.line = line;
        const $if = this.args[0];
        const then = this.args[1];
        const $else = this.args[2];
        line = $if.set_line(line);
        if (this.inline) {
            line = then.set_line(line);
            return $else.set_line(line);
        }
        line++;
        line = then.set_line(line);
        line++;
        if (!($else instanceof LeanIte)) line++;
        return $else.set_line(line);
    }

    split(syntax) {
        const then = this.then;
        const $else = this.else;
        if (then && $else) {
            const self = this.clone();
            const sIf = self.args[0];
            const sThen = self.args[1];
            const sElse = self.args[2];
            self.args = [sIf];
            const statements = [self];
            if (sThen instanceof L.LeanStatements) sThen.swap_echo_star(syntax, statements);
            else statements.push(sThen);
            if (sElse instanceof LeanIte) {
                const sp = sElse.split(syntax);
                sp[0].args[2] = 0;
                statements.push(...sp);
            } else {
                statements.push(new LeanIte([], this.indent, $else.level));
                if (sElse instanceof L.LeanStatements) sElse.swap_echo_star(syntax, statements);
                else statements.push(...sElse.split(syntax));
            }
            return statements;
        }
        return [this];
    }

    strFormat() {
        const $if = this.args[0];
        const then = this.args[1];
        const $else = this.args[2];
        if (!then && !$else) {
            if ($if == null) return 'else';
            if ($else === 0) return 'else if %s then';
            return 'if %s then';
        }
        if (this.inline) return 'if %s then %s else %s';
        const indent_else = ' '.repeat(this.indent);
        const sep = $else instanceof LeanIte ? ' ' : '\n';
        const thenFmt = then == null ? '' : '%s';
        const elseFmt = $else == null ? '' : '%s';
        return `if %s then\n${thenFmt}\n${indent_else}else${sep}${elseFmt}`;
    }

    static echo_part(part, token) {
        const echo = new L.LeanTactic('echo', token.clone(), part.indent, part.level);
        if (part instanceof L.LeanStatements) part.unshift(echo);
        else if (part.parent)
            part.parent.replace(part, new L.LeanStatements([echo, part], part.indent, part.level));
    }
}
