/**
 * Statement lists (`LeanStatements`).
 *
 * Multiline blocks: proof scripts after `by`, and proposition text after `:`.
 * `LeanArgs` and `LeanMultipleLine` already exist and are passed in, with the
 * other classes defined earlier. Classes defined later (`LeanBrace`, tactics,
 * `by` / `calc`, and the rest) are filled on `statementsLate`.
 * `leanStatementsPreferWordOverTactic` lives here because only `insert_tactic`
 * uses it. This factory does not import `lean.js`. PHP keeps its shorter
 * `echo`, `insert_newline`, and `latexFormat`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanMultipleLine
 * @param {Function} deps.LeanArgs
 * @param {Function} deps.LeanColon
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanLineComment
 * @param {Function} deps.LeanBlockComment
 * @param {Function} deps.LeanAssign
 * @param {Function} deps.LeanRelational
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanToken
 * @param {Function} deps.leanIsInfixContinue
 * @param {object} deps.statementsLate
 */
export function createStatementsFamily(deps) {
    const {
        LeanMultipleLine,
        LeanArgs,
        LeanColon,
        LeanCaret,
        LeanLineComment,
        LeanBlockComment,
        LeanAssign,
        LeanRelational,
        LeanBinary,
        LeanToken,
        leanIsInfixContinue,
        statementsLate,
    } = deps;
    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = statementsLate[name];
                if (real == null) throw new Error(`${name} used before statements registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = statementsLate[name];
                if (real == null) throw new Error(`${name} used before statements registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsNewLineSeparated = lateCtor('LeanArgsNewLineSeparated');
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LeanBitOr = lateCtor('LeanBitOr');
    const LeanBrace = lateCtor('LeanBrace');
    const LeanBy = lateCtor('LeanBy');
    const LeanCalc = lateCtor('LeanCalc');
    const LeanFrom = lateCtor('LeanFrom');
    const LeanIte = lateCtor('LeanIte');
    const LeanStack = lateCtor('LeanStack');
    const LeanTactic = lateCtor('LeanTactic');
    const LeanTacticBlock = lateCtor('LeanTacticBlock');
    const Lean_lemma = lateCtor('Lean_lemma');
    const Lean_mapsto = lateCtor('Lean_mapsto');
    const Lean_match = lateCtor('Lean_match');
    const Lean_rightarrow = lateCtor('Lean_rightarrow');

    /**
     * Multiline `LeanStatements` is used both for proof scripts (`by …`) and for proposition/type text after `:`.
     * Tactic names that overlap with term names (e.g. `arg`) must parse as words in the latter case.
     * @param {LeanStatements} stmts
     */
    function leanStatementsPreferWordOverTactic(stmts) {
        for (let p = stmts.parent; p; p = p.parent) {
            if (p instanceof LeanBy || p instanceof LeanFrom) {
                return false;
            }
            let ch = stmts;
            while (ch.parent !== p) {
                if (!ch.parent) break;
                ch = ch.parent;
            }
            if (ch.parent !== p) continue;
            if (p instanceof LeanColon && p.rhs === ch) return true;
            if (p instanceof LeanBrace && p.arg === ch) {
                /** `repeat { simp only … }` / `try { … }` — tactic block, not a term `{ … }`. */
                let q = p.parent;
                while (q instanceof LeanArgsSpaceSeparated) q = q.parent;
                return !(q instanceof LeanTactic && q.is_inline_tactic_block());
            }
            if ((p instanceof Lean_rightarrow || p instanceof Lean_mapsto) && p.rhs === ch) return true;
        }
        return false;
    }



    class LeanStatements extends LeanMultipleLine(LeanArgs) {
        get stack_priority() {
            return LeanColon.input_priority;
        }

        push_binary(Ctor) {
            const parent = this.parent;
            if (!parent) return undefined;
            let idx = this.args.length - 1;
            while (idx >= 0) {
                const c = this.args[idx];
                if (c instanceof LeanCaret || c instanceof LeanLineComment || c instanceof LeanBlockComment) {
                    idx--;
                    continue;
                }
                break;
            }

            if (Ctor.input_priority > this.stack_priority) {
                if (idx >= 0) {
                    const origin = this.args[idx];
                    while (
                        this.args.length - 1 > idx &&
                        this.args[this.args.length - 1] instanceof LeanCaret
                    ) {
                        this.args.pop();
                    }
                    const caret = new LeanCaret(origin.indent, origin.level);
                    this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
                    return caret;
                }
                return super.push_binary(Ctor);
            }

            if ((Ctor !== LeanAssign && Ctor !== LeanColon) || !(parent instanceof LeanBrace))
                return super.push_binary(Ctor);
            if (idx < 0) return super.push_binary(Ctor);
            const origin = this.args[idx];
            const caret = new LeanCaret(origin.indent, origin.level);
            this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
            return caret;
        }

        insert_tactic(caret, token) {
            if (caret instanceof LeanCaret && leanStatementsPreferWordOverTactic(this)) {
                return this.insert_word(caret, token);
            }
            return super.insert_tactic(caret, token);
        }

        insert_semicolon(caret) {
            if (caret instanceof LeanTactic) return caret.insert_semicolon(caret.arg);
            return super.insert_semicolon(caret);
        }

        echo() {
            const {args} = this;
            let count = args.length;
            let void_lines = 0;
            while (count > 0) {
                const last = args[count - 1];
                if (last instanceof LeanCaret || last instanceof LeanLineComment || last instanceof LeanBlockComment) {
                    count--;
                    void_lines++;
                } else break;
            }
            let index = 0;
            for (; index < args.length - void_lines - 1; ++index) {
                const result = args[index].echo();
                if (Array.isArray(result)) {
                    const length = result.shift();
                    if (
                        index + 1 < args.length - void_lines &&
                        args[index + 1] instanceof LeanTactic &&
                        args[index + 1].tacticName === 'try' &&
                        result.length === 2 &&
                        result[0] === args[index] &&
                        result[1] instanceof LeanTactic &&
                        result[1].tacticName === 'echo'
                    ) {
                        const e = result[1];
                        result[1] = new LeanTactic('try', e, e.indent, e.level);
                    }
                    for (const echo of result) echo.parent = this;
                    // A head tactic followed by statement-level `LeanBitOr` lines
                    // forms one multi-line alternative group (`first | …`,
                    // `rcases … | …`): trailing `echo` placeholders must stay after
                    // the whole group, never between the head and its `|` branches
                    // (the latter generates invalid Lean: `first echo ⊢ | …`).
                    let barRun = 0;
                    for (let j = index + length; j < args.length - void_lines && args[j] instanceof LeanBitOr; j++) barRun++;
                    const trailingEchoes = [];
                    if (barRun) {
                        while (result.length > 1 && result[result.length - 1] instanceof LeanTactic && result[result.length - 1].tacticName === 'echo') {
                            trailingEchoes.unshift(result.pop());
                        }
                    }
                    const increment = result.indexOf(args[index]);
                    args.splice(index, length, ...result);
                    if (trailingEchoes.length) {
                        args.splice(index + result.length + barRun, 0, ...trailingEchoes);
                    }
                    index += increment;
                }
            }
            const tactic = args[index];
            if (tactic instanceof LeanTactic || tactic instanceof Lean_match) {
                const result = tactic.echo();
                if (Array.isArray(result)) {
                    const length = result.shift();
                    const pos = result.indexOf(tactic);
                    if (pos >= 0) {
                        while (result.length > pos + 1) {
                            const tail = result[result.length - 1];
                            if (tail instanceof LeanTactic && tail.tacticName === 'echo') result.pop();
                            else break;
                        }
                    }
                    for (const echo of result) echo.parent = this;
                    args.splice(index, length, ...result);
                } else if (tactic.tacticName === 'case') {
                    const arrow = tactic.arrow;
                    if (arrow && arrow.rhs instanceof LeanStatements) arrow.rhs.echo();
                } else {
                    const w = tactic.with;
                    if (w) {
                        if (w.sep() === '\n') {
                            for (const c of w.args) c.echo();
                        } else if (tactic.sequential_tactic_combinator) {
                            const block = tactic.sequential_tactic_combinator.arg;
                            if (block instanceof LeanTacticBlock) block.echo();
                            else tactic.sequential_tactic_combinator.echo();
                        }
                    } else if (tactic.sequential_tactic_combinator) {
                        tactic.sequential_tactic_combinator.echo();
                    } else {
                        const rb = tactic.repeat_block();
                        if (rb) rb.echo();
                        const {using} = tactic;
                        if (using) using.echo();
                    }
                }
            } else if (tactic instanceof LeanTacticBlock || tactic instanceof LeanIte || tactic instanceof LeanCalc) {
                tactic.echo();
            }
        }

        insert_if(caret) {
            if (!(caret instanceof LeanCaret)) return undefined;
            const last = this.args[this.args.length - 1];
            if (last !== caret) return undefined;
            this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
            return caret;
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent > indent) return super.insert_newline(caret, newline_count, indent, next);
            if (this.indent < indent) {
                if (!leanIsInfixContinue(next)) {
                    const c = this.push_args_indented(indent, newline_count);
                    if (c) return c;
                }
                // See `LeanModule.insert_newline` — fall through when last arg cannot be wrapped.
            }
            for (let k = 0; k < newline_count; ++k) {
                caret = new LeanCaret(indent, caret.level);
                this.push(caret);
            }
            return caret;
        }

        is_indented() {
            return false;
        }

        isProp(vars) {
            const args = this.args;
            if (args.length === 1) return args[0].isProp(vars);
        }

        toJSON() {
            let args = super.toJSON();
            if (this.args.length && this.args[this.args.length - 1] instanceof LeanCaret) {
                args = args.slice(0, -1);
            }
            if (args.length === 1) return args[0];
            return args;
        }

        latexFormat() {
            const n = this.args.length;
            if (n === 0) return '';
            if (n === 1) return '%s';
            const stmt = Array(n).fill('&{%s}&& ').join('\\\\\n');
            const p = this.parent;
            if (p && p instanceof LeanBy) return stmt;
            let align =  (p instanceof LeanRelational || p instanceof LeanBinary || p instanceof LeanStack || p instanceof LeanIte) ? 'aligned': 'align*';
            return `\\begin{${align}}\n${stmt}\n\\end{${align}}`;
        }

        relocate_last_comment() {
            for (let index = this.args.length - 1; index >= 0; --index) {
                const end = this.args[index];
                if (end.is_outsider()) {
                    let self = this;
                    let parent = null;
                    while (self) {
                        parent = self.parent;
                        if (parent instanceof LeanStatements) break;
                        self = parent;
                    }
                    if (parent) {
                        const last = this.args.pop();
                        const index = parent.args.indexOf(self);
                        parent.args.splice(index + 1, 0, last);
                        last.parent = parent;
                        last.indent = parent.indent;
                        parent.relocate_last_comment();
                        break;
                    }
                } else {
                    if (end.is_comment()) {
                        let lemma = null;
                        let j = 0;
                        for (j = index - 1; j >= 0; --j) {
                            const stmt = this.args[j];
                            if (stmt instanceof Lean_lemma) {
                                lemma = stmt;
                                break;
                            }
                            if (stmt.is_comment()) continue;
                            break;
                        }
                        if (lemma) {
                            const assignment = lemma.assignment;
                            if (assignment instanceof LeanAssign) {
                                let proof = assignment.rhs;
                                if (proof instanceof LeanBy || proof instanceof LeanCalc) {
                                    proof = proof.arg;
                                    if (proof instanceof LeanStatements) {
                                        for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                        this.args.splice(j + 1, index - j);
                                        break;
                                    }
                                } else if (proof instanceof LeanArgsNewLineSeparated) {
                                    for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                    this.args.splice(j + 1, index - j);
                                    break;
                                }
                            }
                        }
                    }
                    end.relocate_last_comment();
                    break;
                }
            }
        }

        strFormat() {
            const n = this.args.length;
            if (n === 0) return '';
            let format = Array(n).fill('%s').join('\n');
            if (this.parent instanceof LeanBrace) {
                format = `\n${format}\n${' '.repeat(this.parent.indent)}`;
            }
            return format;
        }

        swap_echo_star(syntax, statements) {
            const args = this.args;
            for (let i = 0; i < args.length; ++i) {
                const echo = args[i];
                if (
                    echo instanceof LeanTactic &&
                    echo.tacticName === 'echo' &&
                    echo.arg instanceof LeanToken &&
                    echo.arg.text === '*'
                ) {
                    [args[i], args[i + 1]] = [args[i + 1], args[i]];
                    i++;
                }
            }
            for (const stmt of this.args) statements.push(...stmt.split(syntax));
        }

        /** Port of LeanStatements::push_line_comment. Stops bubbling to root. */
        push_line_comment(comment) {
            const line = new LeanLineComment(comment, this.indent, this.level);
            this.push(line);
            return line;
        }
    }

    return {
        LeanStatements,
    };
}
