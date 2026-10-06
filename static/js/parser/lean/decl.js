/**
 * Declarations and binders: `Lean_def`, `theorem` / `abbrev` / `lemma`,
 * `let` / `have` / `set` / `replace` / `show`. JS also has `where`, `class`,
 * `instance`, `macro`, and `syntax` in this cluster; PHP does not.
 *
 * `Lean`, `LeanArgs`, `LeanSyntax`, `LeanBinary`, and the classes already
 * declared above this factory stay in `lean.js` and are passed in.
 * `LeanAngleBracket` is filled on `declLate` after the paired-delimiter
 * family exists; methods only use it via `instanceof`. This factory does
 * not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.Lean
 * @param {Function} deps.LeanArgs
 * @param {Function} deps.LeanArgsCommaSeparated
 * @param {Function} deps.LeanArgsNewLineSeparated
 * @param {Function} deps.LeanArgsSemicolonSeparated
 * @param {Function} deps.LeanArgsSpaceSeparated
 * @param {Function} deps.LeanAssign
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanBy
 * @param {Function} deps.LeanCalc
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanColon
 * @param {Function} deps.LeanSequentialTacticCombinator
 * @param {Function} deps.LeanStatements
 * @param {Function} deps.LeanSyntax
 * @param {Function} deps.LeanTactic
 * @param {Function} deps.LeanTacticBlock
 * @param {Function} deps.LeanToken
 * @param {object} deps.declLate
 */
export function createDeclFamily(deps) {
    const {
        Lean,
        LeanArgs,
        LeanArgsCommaSeparated,
        LeanArgsNewLineSeparated,
        LeanArgsSemicolonSeparated,
        LeanArgsSpaceSeparated,
        LeanAssign,
        LeanBinary,
        LeanBy,
        LeanCalc,
        LeanCaret,
        LeanColon,
        LeanSequentialTacticCombinator,
        LeanStatements,
        LeanSyntax,
        LeanTactic,
        LeanTacticBlock,
        LeanToken,
        declLate,
    } = deps;

    function lateCtor(name) {
        function Ctor(...args) {
            const real = declLate[name];
            if (real == null) throw new Error(`${name} used before decl registration`);
            return new real(...args);
        }
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = declLate[name];
                if (real == null) throw new Error(`${name} used before decl registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanAngleBracket = lateCtor('LeanAngleBracket');

    class Lean_def extends LeanArgs {
        get stack_priority() {
            return 7;
        }

        get operator() {
            return 'def';
        }

        /**
         * @param {string|Lean} accessibility
         * @param {Lean|number} name
         * @param {number} [indent]
         * @param {number} [level]
         * @param {import('./node.js').Node | null} [parent]
         */
        constructor(accessibility, name, indent, level, parent = null) {
            if (level === null || level === undefined) {
                indent = name;
                name = accessibility;
                accessibility = 'public';
                level = name instanceof Lean ? name.level : 0;
            }
            super([name], indent, level, parent);
            this.args.unshift(null);
            this.kwargs.accessibility = accessibility;
        }

        get accessibility() {
            return this.kwargs.accessibility;
        }

        set accessibility(v) {
            this.kwargs.accessibility = v;
        }

        get attribute() {
            return this.args[0];
        }

        set attribute(v) {
            this.args[0] = v;
            if (v) v.parent = this;
        }

        get assignment() {
            return this.args[1];
        }

        set assignment(v) {
            this.args[1] = v;
            if (v) v.parent = this;
        }

        strArgs() {
            const [attr, assignment] = this.args;
            if (attr == null) return [assignment];
            return this.args;
        }

        strFormat() {
            const acc = this.accessibility === 'public' ? '' : `${this.accessibility} `;
            let def = `${acc}${this.func} %s`;
            if (this.attribute) def = `%s\n${def}`;
            return def;
        }

        latexFormat() {
            return this.strFormat();
        }

        toJSON() {
            const json = {
                [this.operator]: super.toJSON(),
                accessibility: this.accessibility,
            };
            if (this.attribute) json.attribute = this.attribute.toJSON();
            return json;
        }

        insert_tactic(caret, token) {
            return this.insert_word(caret, token);
        }

        is_indented() {
            return false;
        }

        set_line(line) {
            this.line = line;
            let L = line;
            const attr = this.attribute;
            if (attr) L = attr.set_line(L) + 1;
            return this.assignment.set_line(L);
        }

        relocate_last_comment() {
            const assignment = this.assignment;
            if (assignment instanceof LeanAssign) assignment.relocate_last_comment();
        }

        /**
         * Port of `Lean_def::insert_newline`.
         * Stops indented proof lines from bubbling to `LeanModule` (which would throw).
         */
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent < indent) {
                if (caret === this.assignment) {
                    const $new = this.push_args_indented(indent, newline_count);
                    if ($new) return $new;
                    if (caret instanceof LeanColon) {
                        if (caret.rhs instanceof LeanCaret) {
                            caret = caret.rhs;
                            caret.indent = indent;
                            this.assignment.rhs = new LeanStatements([caret], indent, caret.level);
                            return caret;
                        }
                    } else if (caret instanceof LeanAssign) {
                        const {rhs} = this.assignment;
                        if (rhs instanceof LeanCaret) {
                            rhs.indent = indent;
                            this.assignment.rhs = new LeanStatements([rhs], indent, rhs.level);
                            return rhs;
                        }
                        if (rhs instanceof LeanArgsNewLineSeparated || rhs instanceof LeanStatements) {
                            const c = new LeanCaret(indent, rhs.level);
                            rhs.push(c);
                            return c;
                        }
                    }
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
    }

    class Lean_theorem extends Lean_def {}

    class Lean_abbrev extends Lean_def {}

    class Lean_where extends LeanBinary {
        static input_priority = 18;

        get operator() {
            return 'where';
        }

        get command() {
            return 'where';
        }

        sep() {
            return this.rhs instanceof LeanCaret ? ' ' : '\n';
        }

        /**
         * Capture the indented field block after `where` (mirrors `Lean_def::insert_newline`
         * wrapping the `:=` rhs into a `LeanStatements`).
         */
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent < indent && caret === this.rhs && this.rhs instanceof LeanCaret) {
                const rhs = this.rhs;
                rhs.indent = indent;
                this.rhs = new LeanStatements([rhs], indent, rhs.level);
                return rhs;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
    }

    class Lean_class extends Lean_def {}

    class Lean_instance extends Lean_def {}

    class Lean_macro extends Lean_def {}

    class Lean_syntax extends Lean_def {}

    class Lean_lemma extends Lean_def {
        echo() {
            this.assignment.echo();
            const asn = this.assignment;
            if (asn instanceof LeanAssign && asn.rhs instanceof LeanBy) {
                const statement = asn.rhs.arg;
                if (statement instanceof LeanStatements) {
                    const stmts = statement.args;
                    for (let i = stmts.length - 1; i >= 0; i--) {
                        const stmt = stmts[i];
                        if (stmt.is_comment()) continue;
                        if (stmt instanceof LeanTactic || stmt instanceof Lean_let) {
                            const token = stmt.get_echo_token();
                            // try echo ⊢
                            if (token) {
                                const {indent, level} = statement;
                                statement.push(
                                    new LeanTactic(
                                        'try',
                                        new LeanTactic('echo', token, indent, level),
                                        indent,
                                        level,
                                    ),
                                );
                            }
                            break;
                        }
                    }
                }
            }
        }
    }

    // binding tactic
    class Lean_let extends LeanSyntax {
        static input_priority = 7;

        /**
         * @param {Lean} arg
         * @param {number} indent
         * @param {number} level
         * @param {import('./node.js').Node | null} [parent]
         */
        constructor(arg, indent, level, parent = null) {
            super([arg], indent, level, parent);
        }

        get command() {
            return 'let';
        }

        echo() {
            const token = this.get_echo_token();
            const proof = this.args[0]?.rhs;
            if (proof instanceof LeanBy) {
                const stmt = proof.arg;
                if (stmt instanceof LeanStatements) stmt.echo();
            } else if (proof instanceof LeanCalc) {
                proof.echo();
            }
            if (token) {
                return [1, this, new LeanTactic('echo', token, this.indent, token.level)];
            }
        }

        get_echo_token() {
            const assign = this.args[0];
            if (assign instanceof LeanAssign) {
                const lhs = assign.lhs;
                if (lhs instanceof LeanAngleBracket) {
                    const token = lhs.tokens_comma_separated();
                    if (token.length === 1) return token[0];
                    return new LeanArgsCommaSeparated(token, this.indent, lhs.level);
                }
                if (lhs instanceof LeanToken) return lhs;
                if (lhs instanceof LeanColon && lhs.lhs instanceof LeanToken) return lhs.lhs;
                if (lhs instanceof LeanArgsSpaceSeparated && lhs.args[0] instanceof LeanToken) return lhs.args[0];
            }
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.args[0]) {
                if (next === '<' && this.parent instanceof LeanSequentialTacticCombinator) {
                    const c = new LeanCaret(indent, caret.level);
                    this.push(c);
                    return c;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_sequential_tactic_combinator(caret, prevToken, nextToken) {
            const last = this.args[this.args.length - 1];
            if (caret === last) {
                if (caret instanceof LeanCaret) {
                    this.replace(
                        caret,
                        new LeanSequentialTacticCombinator(
                            caret,
                            prevToken == '\n' ? caret.indent : this.indent,
                            caret.level,
                            prevToken == '\n',
                            nextToken == '\n'
                        ),
                    );
                } else {
                    const c = new LeanCaret(0, 0);
                    this.push(new LeanSequentialTacticCombinator(c, this.indent, c.level, false, true));
                }
                return caret;
            }
            throw new Error(`insert_sequential_tactic_combinator is unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            const parent = this.parent;
            if (parent instanceof LeanSequentialTacticCombinator) return this.indent > 0;
            if (parent instanceof LeanTacticBlock) return this.indent > parent.indent;
            return !(parent instanceof LeanArgsSemicolonSeparated);
        }

        toJSON() {
            return {
                [this.operator]: this.args[0].toJSON(),
            };
        }

        latexFormat() {
            return `{\\color{#00f}${this.command}}\\ ` + Array(this.args.length).fill('%s').join('\\ ');
        }

        get operator() {
            return 'let';
        }

        split(syntax) {
            const assign = this.args[0];
            if (assign instanceof LeanAssign) {
                const proof = assign.rhs;
                if (
                    (proof instanceof LeanBy && proof.arg instanceof LeanStatements) ||
                    proof instanceof LeanCalc
                ) {
                    const statements = assign.split(syntax);
                    const Ctor = this.constructor;
                    statements[0] = new Ctor(statements[0], this.indent, assign.level);
                    return statements;
                }
            }
            return [this];
        }

        get stack_priority() {
            return 7;
        }

        strFormat() {
            const func = this.operator;
            const parts = [];
            for (const arg of this.args) {
                if (arg instanceof LeanCaret);
                else if (
                    arg instanceof LeanSequentialTacticCombinator &&
                    (arg.newlineBehind || arg.newlineBefore)
                ) {
                    parts.push('\n');
                } else parts.push(' ');
                parts.push('%s');
            }
            return func + parts.join('');
        }
    }

    class Lean_have extends Lean_let {
        get command() {
            return 'have';
        }

        get operator() {
            return 'have';
        }

        get_echo_token() {
            const assign = this.args[0];
            if (!(assign instanceof LeanAssign)) return;
            let token = assign.lhs;
            if (token instanceof LeanColon)
                token = token.lhs;
            if (token instanceof LeanCaret)
                token = new LeanToken('this', this.indent, token.level);
            if (token instanceof LeanArgsSpaceSeparated && token.args[0] instanceof LeanToken)
                token = token.args[0];
            if (
                token instanceof LeanAngleBracket &&
                token.arg instanceof LeanArgsCommaSeparated &&
                token.arg.args.every((arg) => arg instanceof LeanToken)
            ) {
                token = token.arg;
            }
            if (token instanceof LeanToken || token instanceof LeanArgsCommaSeparated) return token;
        }

        sep() {
            const assign = this.args[0];
            if (assign instanceof LeanAssign) {
                const lhs = assign.lhs;
                if (lhs instanceof LeanCaret) return '';
                if (lhs instanceof LeanColon && lhs.lhs instanceof LeanCaret) return '';
            }
            return ' ';
        }

        strFormat() {
            const parts = [];
            for (let i = 0; i < this.args.length; i++) {
                const arg = this.args[i];
                if (i === 0) parts.push(this.sep());
                else if (arg instanceof LeanCaret);
                else if (
                    arg instanceof LeanSequentialTacticCombinator &&
                    (arg.newlineBehind || arg.newlineBefore)
                ) {
                    parts.push('\n');
                } else parts.push(' ');
                parts.push('%s');
            }
            return this.operator + parts.join('');
        }
    }

    class Lean_set extends Lean_let {
        get command() {
            return 'set';
        }

        get operator() {
            return 'set';
        }
    }

    /** `replace h : T := proof` — same shape as `have`, but replaces the hypothesis `h`. */
    class Lean_replace extends Lean_have {
        get command() {
            return 'replace';
        }

        get operator() {
            return 'replace';
        }
    }

    class Lean_show extends LeanSyntax {
        constructor(arg, indent, level, parent = null) {
            super([arg], indent, level, parent);
        }

        get stack_priority() {
            return 7;
        }

        get operator() {
            return 'show';
        }

        is_indented() {
            const parent = this.parent;
            return parent instanceof LeanStatements || parent instanceof LeanArgsNewLineSeparated;
        }

        toJSON() {
            return {
                [this.operator]: super.toJSON(),
            };
        }

        latexFormat() {
            const f = `{\\color{#00f}${this.func}}`;
            return `${f}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
        }

        strFormat() {
            return `${this.func} ${Array(this.args.length).fill('%s').join(' ')}`;
        }
    }

    return {
        Lean_def,
        Lean_theorem,
        Lean_abbrev,
        Lean_where,
        Lean_class,
        Lean_instance,
        Lean_macro,
        Lean_syntax,
        Lean_lemma,
        Lean_let,
        Lean_have,
        Lean_set,
        Lean_replace,
        Lean_show,
    };
}
