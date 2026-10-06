/**
 * Type ascription and declaration colon (`LeanColon`, `a : T`).
 *
 * `LeanBinary`, `LeanCaret`, `LeanToken`, `LeanProperty`, and
 * `leanIsInfixContinue` already exist and are passed in. Later classes
 * (argument lists, `LeanStatements`, `LeanParenthesis`, `LeanGetElem`,
 * `LeanBrace`, `LeanBracket`, `Lean_let`) are filled on `colonLate`.
 * This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanToken
 * @param {Function} deps.LeanProperty
 * @param {Function} deps.leanIsInfixContinue
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.colonLate
 */
export function createColonFamily(deps) {
    const {
        LeanBinary,
        LeanCaret,
        LeanToken,
        LeanProperty,
        leanIsInfixContinue,
        classRegistry,
        colonLate,
    } = deps;
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before colon registration');
            return map[key];
        },
    });
    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = colonLate[name];
                if (real == null) throw new Error(`${name} used before colon registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = colonLate[name];
                if (real == null) throw new Error(`${name} used before colon registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsCommaSeparated = lateCtor('LeanArgsCommaSeparated');
    const LeanArgsIndented = lateCtor('LeanArgsIndented');
    const LeanArgsNewLineSeparated = lateCtor('LeanArgsNewLineSeparated');
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LeanBrace = lateCtor('LeanBrace');
    const LeanBracket = lateCtor('LeanBracket');
    const LeanGetElem = lateCtor('LeanGetElem');
    const LeanParenthesis = lateCtor('LeanParenthesis');
    const LeanStatements = lateCtor('LeanStatements');
    const Lean_let = lateCtor('Lean_let');

    /** Type ascription / declaration colon. */
    class LeanColon extends LeanBinary {
        static input_priority = 19;

        get operator() {
            return ':';
        }

        get command() {
            return ':';
        }

        insert(caret, func, type) {
            if (this.rhs === caret && !(caret instanceof LeanCaret) && type !== 'modifier') {
                const c = new LeanCaret(this.indent, caret.level);
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                this.rhs = new LeanArgsSpaceSeparated(
                    [caret, new Ctor(c, this.indent, caret.level)],
                    this.indent,
                    caret.level,
                );
                return c;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.rhs === caret) {
                if (!(caret instanceof LeanCaret) && indent > this.indent && leanIsInfixContinue(next)) {
                    return caret;
                }
                if (caret instanceof LeanCaret && indent >= this.indent) {
                    if (indent === this.indent) indent = this.indent + 2;
                    caret.indent = indent;
                    const stmts = new LeanStatements([caret], indent, caret.level);
                    this.replace(caret, stmts);
                    return caret;
                }
                if (caret instanceof LeanStatements && indent === this.indent && this.parent instanceof LeanParenthesis)
                    return caret;
                // `have h : Tendsto (f)\n      atTop (𝓝 0) := …` — a deeper line continues a complete type;
                // without this the line escapes to the enclosing statements and `:=` binds outside the `have`.
                if (
                    this.parent instanceof Lean_let && indent > this.indent && next !== ':' &&
                    (caret instanceof LeanArgsSpaceSeparated || caret instanceof LeanToken ||
                        caret instanceof LeanProperty || caret instanceof LeanParenthesis)
                ) {
                    const $new = new LeanCaret(indent, caret.level);
                    const nl = new LeanArgsNewLineSeparated([$new], indent, $new.level);
                    const c = nl.push_newlines(newline_count - 1);
                    this.replace(caret, new LeanArgsIndented(caret, nl, caret.indent, c.level));
                    return c;
                }
            }
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
            if (ty instanceof LeanParenthesis) ty = ty.arg;
            if (!(ty instanceof LeanArgsSpaceSeparated)) return null;
            const args = ty.args.filter((a) => !(a instanceof LeanCaret));
            if (args.length < 2) return null;
            const head = args[0];
            if (!(head instanceof LeanToken) || head.text !== 'Tensor') return null;
            const shape = args[args.length - 1];
            if (shape instanceof LeanBracket) {
                const inner = shape.arg;
                if (!inner || inner instanceof LeanCaret) return [];
                if (inner instanceof LeanArgsCommaSeparated)
                    return inner.args.filter((a) => !(a instanceof LeanCaret));
                return [inner];
            }
            return [shape];
        }

        isZeroOneTensor() {
            const lhs = this.lhs;
            return (
                lhs instanceof LeanToken &&
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
            return rhs instanceof LeanStatements ? '\n' : (rhs instanceof LeanCaret || this.parent instanceof LeanGetElem ? '' : ' ');
        }

        strArgs() {
            let lhs = this.lhs;
            const rhs = this.rhs;
            if (lhs instanceof LeanArgsNewLineSeparated) {
                const la = lhs.args;
                const tail = la.slice(1).map((arg) => String(arg));
                lhs = [String(la[0]), ...tail].join('\n');
            }
            return [lhs, rhs];
        }

        strFormat() {
            const sep = this.sep();
            let first = '%s';
            if (!(this.parent instanceof LeanGetElem)) {
                if (sep === ' ') {
                    first += ' ';
                } else if (sep === '\n') {
                    const L = this.lhs;
                    // `lemma main:\n-- imply` stays tight; `{binders} :\n-- imply` and indented binder blocks
                    // `  (h : …) :\n-- imply` keep a space before `:`.
                    if (L instanceof LeanBrace || L instanceof LeanParenthesis || L instanceof LeanArgsIndented)
                        first += ' ';
                }
            }
            return `${first}${this.operator}${sep}%s`;
        }
    }

    return {
        LeanColon,
    };
}
