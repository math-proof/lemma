/**
 * Match and tactic bar (`LeanBar`, `|`).
 *
 * `LeanUnary`, `LeanAssign`, `LeanCaret`, and `LeanStatements` already exist
 * and are passed in. `LeanArgsCommaSeparated`, `LeanRightarrow`, and
 * `LeanTactic` are filled on `barLate`. This factory does not import `lean.js`.
 * PHP `is_indented` always returns true, PHP has no `insert_bar`, PHP
 * `insert_comma` tests `end($this->args)`, and PHP `split` uses the arrow's
 * level.
 *
 * @param {object} deps
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.LeanAssign
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanStatements
 * @param {object} deps.barLate
 */
export function createBarFamily(deps) {
    const {
        LeanUnary,
        LeanAssign,
        LeanCaret,
        LeanStatements,
        barLate,
    } = deps;

    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = barLate[name];
                if (real == null) throw new Error(`${name} used before bar registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = barLate[name];
                if (real == null) throw new Error(`${name} used before bar registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsCommaSeparated = lateCtor('LeanArgsCommaSeparated');
    const LeanRightarrow = lateCtor('LeanRightarrow');
    const LeanTactic = lateCtor('LeanTactic');

    /** Bar, then `=>` and related arrow nodes. */
    class LeanBar extends LeanUnary {
        get stack_priority() {
            return LeanAssign.input_priority ?? 20;
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
            if (p instanceof LeanTactic) {
                const c = new LeanCaret(this.indent, caret.level);
                p.push(new LeanBar(c, this.indent, c.level));
                return c;
            }
            return super.insert_bar(caret, prevToken, next);
        }

        insert_comma(caret) {
            if (caret === this.arg) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            throw new Error(`LeanBar.insert_comma: unexpected for ${this.constructor.name}`);
        }

        insert_tactic(caret, token) {
            return this.insert_word(caret, token);
        }

        is_indented() {
            return !(this.parent instanceof LeanTactic);
        }

        latexFormat() {
            return `${this.command} %s`;
        }

        split(syntax) {
            const arrow = this.arg;
            if (arrow instanceof LeanRightarrow) {
                const self = this.clone();
                const statements = [self];
                const clonedArrow = /** @type {LeanRightarrow} */ (self.arg);
                const stmts = clonedArrow.rhs;
                if (stmts instanceof LeanStatements) {
                    clonedArrow.rhs = new LeanCaret(clonedArrow.indent, stmts.level);
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

    return {
        LeanBar,
    };
}
