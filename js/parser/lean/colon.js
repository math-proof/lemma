/**
 * Type ascription and declaration colon (`LeanColon`, `a : T`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { leanIsInfixContinue } from './utility.js';
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** Type ascription / declaration colon. */
export class LeanColon extends LeanBinary {
    static { this.register(); }

    static input_priority = 19;

    get operator() {
        return ':';
    }

    get command() {
        return ':';
    }

    insert(caret, func, type) {
        if (this.rhs === caret && !(caret instanceof L.LeanCaret) && type !== 'modifier') {
            const c = new L.LeanCaret(this.indent, caret.level);
            const Ctor = typeof func === 'string' ? L[func] : func;
            this.rhs = new L.LeanArgsSpaceSeparated(
                [caret, new Ctor(c, this.indent, caret.level)],
                this.indent,
                caret.level,
            );
            return c;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    /**
     * `(h : P) : -- note` at the end of a signature: like `LeanBy.insert_line_comment`, keep the
     * comment until `insert_newline` opens the statements block, then make it the block's first line.
     */
    insert_line_comment(caret, comment) {
        if (caret instanceof L.LeanCaret && this.rhs === caret && this.pendingComment === undefined) {
            this.pendingComment = comment;
            return caret;
        }
        return super.insert_line_comment(caret, comment);
    }

    insert_newline(caret, newline_count, indent, next) {
        const {pendingComment} = this;
        delete this.pendingComment;
        if (this.rhs === caret) {
            if (!(caret instanceof L.LeanCaret) && indent > this.indent && leanIsInfixContinue(next)) {
                return caret;
            }
            if (caret instanceof L.LeanCaret && indent >= this.indent) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const stmts = new L.LeanStatements([caret], indent, caret.level);
                if (pendingComment !== undefined) stmts.unshift(new L.LeanLineComment(pendingComment, indent, caret.level));
                this.replace(caret, stmts);
                return caret;
            }
            if (caret instanceof L.LeanStatements && indent === this.indent && this.parent instanceof L.LeanParenthesis)
                return caret;
            // `have h : Tendsto (f)\n      atTop (𝓝 0) := …` — a deeper line continues a complete type;
            // without this the line escapes to the enclosing statements and `:=` binds outside the `have`.
            if (
                this.parent instanceof L.Lean_let && indent > this.indent && next !== ':' &&
                (caret instanceof L.LeanArgsSpaceSeparated || caret instanceof L.LeanToken ||
                    caret instanceof L.LeanProperty || caret instanceof L.LeanParenthesis)
            ) {
                const $new = new L.LeanCaret(indent, caret.level);
                const nl = new L.LeanArgsNewLineSeparated([$new], indent, $new.level);
                const c = nl.push_newlines(newline_count - 1);
                this.replace(caret, new L.LeanArgsIndented(caret, nl, caret.indent, c.level));
                return c;
            }
        }
        if (pendingComment !== undefined && this.rhs === caret) caret = caret.push_line_comment(pendingComment);
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        return false;
    }

    peelLatexCoe() {
        return this.lhs.peelLatexCoe();
    }

    /**
     * `(0 : Tensor α [n, m])` / `(1 : Tensor α [n, m])` → shape cells for `\mathbf{0}_{n,m}`.
     * @returns {Lean[] | null}
     */
    tensorTypeShape() {
        let ty = this.rhs;
        if (ty instanceof L.LeanParenthesis) ty = ty.arg;
        if (!(ty instanceof L.LeanArgsSpaceSeparated)) return null;
        const args = ty.args.filter((a) => !(a instanceof L.LeanCaret));
        if (args.length < 2) return null;
        const head = args[0];
        if (!(head instanceof L.LeanToken) || head.text !== 'Tensor') return null;
        const shape = args[args.length - 1];
        if (shape instanceof L.LeanBracket) {
            const inner = shape.arg;
            if (!inner || inner instanceof L.LeanCaret) return [];
            if (inner instanceof L.LeanArgsCommaSeparated)
                return inner.args.filter((a) => !(a instanceof L.LeanCaret));
            return [inner];
        }
        return [shape];
    }

    isZeroOneTensor() {
        const lhs = this.lhs;
        return (
            lhs instanceof L.LeanToken &&
            (lhs.text === '0' || lhs.text === '1') &&
            this.tensorTypeShape() != null
        );
    }

    latexFormat() {
        if (this.isZeroOneTensor()) return `\\mathbf{${this.lhs.text}}_{%s}`;
        return super.latexFormat();
    }

    latexArgs(syntax) {
        if (this.isZeroOneTensor()) {
            const dims = this.tensorTypeShape();
            return [dims.map((d) => d.toLatex(syntax)).join(',')];
        }
        return super.latexArgs(syntax);
    }

    sep() {
        const rhs = this.rhs;
        return rhs instanceof L.LeanStatements ? '\n' : (rhs instanceof L.LeanCaret || this.parent instanceof L.LeanGetElem ? '' : ' ');
    }

    strArgs() {
        let lhs = this.lhs;
        const rhs = this.rhs;
        if (lhs instanceof L.LeanArgsNewLineSeparated) {
            const la = lhs.args;
            const tail = la.slice(1).map((arg) => String(arg));
            lhs = [String(la[0]), ...tail].join('\n');
        }
        return [lhs, rhs];
    }

    strFormat() {
        const sep = this.sep();
        let first = '%s';
        if (!(this.parent instanceof L.LeanGetElem)) {
            if (sep === ' ') {
                first += ' ';
            } else if (sep === '\n') {
                const lhsNode = this.lhs;
                // `lemma main:\n-- imply` stays tight; `{binders} :\n-- imply` and indented binder blocks
                // `  (h : …) :\n-- imply` keep a space before `:`.
                if (lhsNode instanceof L.LeanBrace || lhsNode instanceof L.LeanParenthesis || lhsNode instanceof L.LeanArgsIndented)
                    first += ' ';
            }
        }
        return `${first}${this.operator}${sep}%s`;
    }
}
