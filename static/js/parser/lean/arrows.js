/**
 * Arrows: `LeanRightarrow` (`=>`), `Lean_rightarrow` (`→`), `Lean_mapsto` (`↦`),
 * and `Lean_leftarrow` (`←`).
 *
 * `LeanBinary` / `LeanUnary` stay in `lean.js` and are passed in. `LeanWith`,
 * `Lean_match`, `LeanTactic`, `LeanArgsCommaSeparated`, `LeanArgsSpaceSeparated`,
 * `LeanAngleBracket`, `LeanPlus`, `LeanNeg`, `LeanPosPart`, and `LeanNegPart`
 * are filled on `arrowsLate` after those classes exist; methods only use them
 * via `instanceof` or `new`. `LEAN_CLASSES` is the shared registry filled after
 * this returns. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.LeanToken
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanColon
 * @param {Function} deps.LeanProperty
 * @param {Function} deps.LeanBar
 * @param {Function} deps.LeanStatements
 * @param {Function} deps.LeanLineComment
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.arrowsLate
 */
export function createArrowsFamily(deps) {
    const {
        LeanBinary,
        LeanUnary,
        LeanToken,
        LeanCaret,
        LeanColon,
        LeanProperty,
        LeanBar,
        LeanStatements,
        LeanLineComment,
        classRegistry,
        arrowsLate,
    } = deps;

    function lateCtor(name) {
        function Ctor(...args) {
            const real = arrowsLate[name];
            if (real == null) throw new Error(`${name} used before arrows registration`);
            return new real(...args);
        }
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = arrowsLate[name];
                if (real == null) throw new Error(`${name} used before arrows registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanWith = lateCtor('LeanWith');
    const Lean_match = lateCtor('Lean_match');
    const LeanTactic = lateCtor('LeanTactic');
    const LeanArgsCommaSeparated = lateCtor('LeanArgsCommaSeparated');
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LeanAngleBracket = lateCtor('LeanAngleBracket');
    const LeanPlus = lateCtor('LeanPlus');
    const LeanNeg = lateCtor('LeanNeg');
    const LeanPosPart = lateCtor('LeanPosPart');
    const LeanNegPart = lateCtor('LeanNegPart');
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before arrows registration');
            return map[key];
        },
    });

    class LeanRightarrow extends LeanBinary {
        static input_priority = 19;

        get operator() {
            return '=>';
        }

        echo() {
            const token = [];
            var {parent} = this;
            if (parent instanceof LeanBar && (parent = parent.parent) instanceof LeanWith && ((parent = parent.parent) instanceof Lean_match || (parent instanceof LeanTactic && parent.tacticName === 'induction'))) {
                token.push(new LeanToken('⊢', this.rhs.indent, this.rhs.level));
                const subject = parent.args[0];
                if (subject instanceof LeanArgsCommaSeparated) {
                    for (const sujet of subject.args) {
                        if (sujet instanceof LeanColon) token.push(sujet.lhs);
                    }
                } else if (subject instanceof LeanColon) {
                    token.push(subject.lhs);
                }
            }
            const expr = this.lhs;
            if (expr instanceof LeanArgsSpaceSeparated) {
                let func;
                if (expr.args[0] instanceof LeanToken) func = expr.args[0].text;
                else if (
                    expr.args[0] instanceof LeanProperty &&
                    expr.args[0].lhs instanceof LeanCaret &&
                    expr.args[0].rhs instanceof LeanToken
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
            } else if (expr instanceof LeanAngleBracket) {
                if (expr.arg instanceof LeanArgsCommaSeparated) {
                    // | ⟨v, property⟩ =>
                    token.push(...expr.arg.args.slice(1));
                }
            } else if (expr instanceof LeanArgsCommaSeparated) {
                // | ⟨x, xProperty⟩, ⟨y, yProperty⟩ =>
                for (const arg of expr.args) {
                    if (arg instanceof LeanAngleBracket && arg.arg instanceof LeanArgsCommaSeparated) {
                        token.push(arg.arg.args[1]);
                    }
                }
            }
            const stmt = this.rhs;
            stmt.echo();
            if (token.length && stmt instanceof LeanStatements) {
                const {indent, level} = stmt.args[0];
                let payload;
                if (token.length > 1) {
                    payload = new LeanArgsCommaSeparated(
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
                stmt.unshift(new LeanTactic('echo', payload, indent, level));
            }
        }

        insert(caret, func, type) {
            if (this.rhs === caret && caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                return caret;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret === this.rhs) {
                if (caret instanceof LeanCaret || caret instanceof LeanLineComment) {
                    if (indent === this.indent) indent = this.indent + 2;
                    caret.indent = indent;
                    const stmts = new LeanStatements([caret], indent, caret.level);
                    this.replace(caret, stmts);
                    let nl = newline_count;
                    if (!(caret instanceof LeanCaret)) nl++;
                    let last = caret;
                    for (let i = 1; i < nl; i++) {
                        last = new LeanCaret(indent, caret.level);
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
            return this.rhs instanceof LeanStatements ? '\n' : this.rhs instanceof LeanCaret ? '' : ' ';
        }

        strFormat() {
            const sep = this.sep();
            let lhs = '%s';
            if (!(this.lhs instanceof LeanCaret)) lhs += ' ';
            return `${lhs}${this.operator}${sep}%s`;
        }
    }

    class Lean_rightarrow extends LeanBinary {
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
                const map = LeanToken.subscript;
                const inner = [...this.subscript]
                    .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                    .join('');
                op += `_{${inner}}`;
            }
            if (this.modifier) op += `[${this.modifier}]`;
            return op;
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.rhs) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const stmts = new LeanStatements([caret], indent, caret.level);
                this.replace(caret, stmts);
                for (let i = 1; i < newline_count; i++) {
                    const c = new LeanCaret(indent, caret.level);
                    stmts.push(c);
                }
                return stmts.args[stmts.args.length - 1];
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        is_indented() {
            return this.parent instanceof LeanStatements;
        }

        /**
         * @param {Record<string, unknown>} [vars]
         */
        isProp(vars) {
            const rhs = this.rhs;
            if ((rhs instanceof LeanToken && (rhs.text === '0' || rhs.text === '∞')) ||
                ((rhs instanceof LeanPlus || rhs instanceof LeanNeg) && rhs.arg instanceof LeanToken && rhs.arg.text === '∞') ||
                ((rhs instanceof LeanPosPart || rhs instanceof LeanNegPart) && rhs.arg instanceof LeanToken && rhs.arg.text === '0'))
                return true;
            const lhs = this.lhs;
            const lhsOk =
                (lhs instanceof LeanToken && (vars[lhs.text] ?? 'Prop') === 'Prop') ||
                (!(lhs instanceof LeanToken) && lhs.isProp(vars));
            const rhsOk =
                (rhs instanceof LeanToken && (vars[rhs.text] ?? 'Prop') === 'Prop') ||
                (!(rhs instanceof LeanToken) && rhs.isProp(vars));
            return Boolean(lhsOk && rhsOk);
        }

        sep() {
            const {rhs} = this;
            if (rhs instanceof LeanStatements) return '\n';
            if (rhs instanceof LeanCaret) return '';
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

    class Lean_mapsto extends LeanBinary {
        get stack_priority() {
            return 23;
        }

        get operator() {
            return '↦';
        }

        insert(caret, func, type) {
            // `fun x ↦ by …` — the term-level `by` fills the lambda body caret,
            // mirroring `LeanRightarrow.insert` for `fun x => by …`.
            if (this.rhs === caret && caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                return caret;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.rhs) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const stmts = new LeanStatements([caret], indent, caret.level);
                this.replace(caret, stmts);
                for (let i = 1; i < newline_count; i++) {
                    const c = new LeanCaret(indent, caret.level);
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
            if (rhs instanceof LeanStatements) return '\n';
            if (rhs instanceof LeanCaret) return '';
            return ' ';
        }

        strFormat() {
            const sep = this.sep();
            return `%s ${this.operator}${sep}%s`;
        }
    }

    /** Unary `←`. */
    class Lean_leftarrow extends LeanUnary {
        get operator() {
            return '←';
        }
        strFormat() {
            return `${this.operator} %s`;
        }
    }

    return {
        LeanRightarrow,
        Lean_rightarrow,
        Lean_mapsto,
        Lean_leftarrow,
    };
}
