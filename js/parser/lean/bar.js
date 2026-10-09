/**
 * Match and tactic bar (`LeanBar`, `|`).
 *
 * PHP `is_indented` always returns true, PHP has no `insert_bar`, PHP
 * `insert_comma` tests `end($this->args)`, and PHP `split` uses the arrow's
 * level.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** Bar, then `=>` and related arrow nodes. */
export class LeanBar extends LeanUnary {
    static { this.register(); }

    get stack_priority() {
        return L.LeanAssign.input_priority ?? 20;
    }

    get operator() {
        return '|';
    }

    get command() {
        return '|';
    }

    echo() {
        this.arg.echo();
    }

    insert_bar(caret, prevToken, next) {
        const p = this.parent;
        if (p instanceof L.LeanTactic) {
            const c = new L.LeanCaret(this.indent, caret.level);
            p.push(new LeanBar(c, this.indent, c.level));
            return c;
        }
        return super.insert_bar(caret, prevToken, next);
    }

    insert_comma(caret) {
        if (caret === this.arg) {
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.replace(caret, new L.LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
            return $new;
        }
        throw new Error(`LeanBar.insert_comma: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    is_indented() {
        return !(this.parent instanceof L.LeanTactic);
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    split(syntax) {
        const arrow = this.arg;
        if (arrow instanceof L.LeanRightarrow) {
            const self = this.clone();
            const statements = [self];
            const clonedArrow = /** @type {LeanRightarrow} */ (self.arg);
            const stmts = clonedArrow.rhs;
            if (stmts instanceof L.LeanStatements) {
                clonedArrow.rhs = new L.LeanCaret(clonedArrow.indent, stmts.level);
                stmts.swap_echo_star(syntax, statements);
            }
            return statements;
        }
        return [this];
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}
