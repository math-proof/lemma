/**
 * Assignment `:=` (`LeanAssign`).
 *
 * `LeanBinary`, `LeanCaret`, and `LeanLineComment` already exist and are
 * passed in. Later classes (argument lists, `LeanStatements`, `LeanBrace`,
 * `LeanBy`, `LeanCalc`, `Lean_blacktriangleright`) are filled on `assignLate`.
 * This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanLineComment
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.assignLate
 */
export function createAssignFamily(deps) {
    const {
        LeanBinary,
        LeanCaret,
        LeanLineComment,
        classRegistry,
        assignLate,
    } = deps;
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before assign registration');
            return map[key];
        },
    });
    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = assignLate[name];
                if (real == null) throw new Error(`${name} used before assign registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = assignLate[name];
                if (real == null) throw new Error(`${name} used before assign registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsIndented = lateCtor('LeanArgsIndented');
    const LeanArgsNewLineSeparated = lateCtor('LeanArgsNewLineSeparated');
    const LeanBrace = lateCtor('LeanBrace');
    const LeanBy = lateCtor('LeanBy');
    const LeanCalc = lateCtor('LeanCalc');
    const LeanStatements = lateCtor('LeanStatements');
    const Lean_blacktriangleright = lateCtor('Lean_blacktriangleright');

    class LeanAssign extends LeanBinary {
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
            if (this.rhs === caret && caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
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
                    if (caret instanceof LeanCaret) {
                        caret.indent = indent;
                        this.rhs = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                        out = this.rhs.push_newlines(newline_count - 1);
                    } else if (caret instanceof LeanArgsNewLineSeparated) {
                        if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
                    } else {
                        if (this.parent instanceof LeanCalc)
                            return this.parent.insert_newline(this, newline_count, indent, next);
                        const p = this.parent;
                        const brace = p instanceof LeanBrace ? p
                            : (p instanceof LeanStatements && p.parent instanceof LeanBrace) ? p.parent
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
            if (!p || p instanceof LeanArgsNewLineSeparated) return true;
            if (p instanceof LeanArgsIndented && p.rhs === this) return true;
            // Structure-instance fields inside a brace: `{ toFun := …, map_add' := … }`
            if (p instanceof LeanStatements && p.parent instanceof LeanBrace) return true;
            return false;
        }

        relocate_last_comment() {
            this.rhs.relocate_last_comment();
        }

        sep() {
            const rhs = this.rhs;
            if (rhs instanceof LeanArgsNewLineSeparated) {
                const lines = rhs.args;
                const l0 = lines[0];
                const l1 = lines[1];
                if (lines.length > 2 || !(l1 instanceof LeanArgsNewLineSeparated) || l0 instanceof LeanLineComment) {
                    return '\n';
                }
            }
            if (rhs instanceof LeanArgsIndented) {
                return '\n';
            }
            if (
                rhs instanceof Lean_blacktriangleright &&
                rhs.lhs instanceof LeanArgsNewLineSeparated &&
                rhs.lhs.args[0] instanceof LeanLineComment
            ) {
                return '\n';
            }
            return ' ';
        }

        split(syntax) {
            const {rhs} = this;
            if (rhs instanceof LeanBy && rhs.arg instanceof LeanStatements) {
                const self = this.clone();
                const stmts = rhs.arg;
                self.rhs.arg = new LeanCaret(rhs.indent, rhs.level);
                const statements = [self];
                stmts.swap_echo_star(syntax, statements);
                return statements;
            }
            if (rhs instanceof LeanCalc) {
                if (syntax) syntax.calc = true;
                const self = this.clone();
                const calc = self.rhs;
                const statements = calc.split(syntax);
                calc.arg = new LeanCaret(calc.indent, calc.level);
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

    return {
        LeanAssign,
    };
}
