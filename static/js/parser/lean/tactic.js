/**
 * Syntax and tactics: `LeanSyntax`, `LeanTactic`, and the wrappers that
 * follow them through `LeanAttribute` (`by`, `from`, `calc`, `at`, `<;>`,
 * tactic blocks, `with`, attributes).
 *
 * `LeanArgs`, `LeanUnary`, the argument-list classes, and the other classes
 * already declared above this factory stay in `lean.js` and are passed in,
 * along with `leanIsInfixContinue`, `leanSubtreeContains`, and
 * `escapeSpecialsForLatex`. Classes created later (`Lean_def`, `Lean_let`,
 * `Lean_have`, paired delimiters, and the rest) are filled on `tacticLate`;
 * methods only use them via `instanceof` or `new`. `LEAN_CLASSES` is the
 * shared registry filled after this returns. This factory does not import
 * `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanArgs
 * @param {Function} deps.LeanArgsCommaNewLineSeparated
 * @param {Function} deps.LeanArgsCommaSeparated
 * @param {Function} deps.LeanArgsIndented
 * @param {Function} deps.LeanArgsNewLineSeparated
 * @param {Function} deps.LeanArgsSemicolonSeparated
 * @param {Function} deps.LeanArgsSpaceSeparated
 * @param {Function} deps.LeanAssign
 * @param {Function} deps.LeanBar
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanColon
 * @param {Function} deps.LeanIte
 * @param {Function} deps.LeanLineComment
 * @param {Function} deps.LeanModule
 * @param {Function} deps.LeanProperty
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.Lean_match
 * @param {Function} deps.LeanRightarrow
 * @param {Function} deps.LeanStatements
 * @param {Function} deps.LeanToken
 * @param {Function} deps.escapeSpecialsForLatex
 * @param {Function} deps.leanIsInfixContinue
 * @param {Function} deps.leanSubtreeContains
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.tacticLate
 */
export function createTacticFamily(deps) {
    const {
        LeanArgs,
        LeanArgsCommaNewLineSeparated,
        LeanArgsCommaSeparated,
        LeanArgsIndented,
        LeanArgsNewLineSeparated,
        LeanArgsSemicolonSeparated,
        LeanArgsSpaceSeparated,
        LeanAssign,
        LeanBar,
        LeanBinary,
        LeanCaret,
        LeanColon,
        LeanIte,
        LeanLineComment,
        LeanModule,
        LeanProperty,
        LeanUnary,
        Lean_match,
        LeanRightarrow,
        LeanStatements,
        LeanToken,
        escapeSpecialsForLatex,
        leanIsInfixContinue,
        leanSubtreeContains,
        classRegistry,
        tacticLate,
    } = deps;

    function lateCtor(name) {
        function Ctor(...args) {
            const real = tacticLate[name];
            if (real == null) throw new Error(`${name} used before tactic registration`);
            return new real(...args);
        }
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = tacticLate[name];
                if (real == null) throw new Error(`${name} used before tactic registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanAngleBracket = lateCtor('LeanAngleBracket');
    const LeanBitOr = lateCtor('LeanBitOr');
    const LeanBrace = lateCtor('LeanBrace');
    const LeanPairedGroup = lateCtor('LeanPairedGroup');
    const LeanParenthesis = lateCtor('LeanParenthesis');
    const Lean_def = lateCtor('Lean_def');
    const Lean_have = lateCtor('Lean_have');
    const Lean_let = lateCtor('Lean_let');
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before tactic registration');
            return map[key];
        },
    });

    class LeanSyntax extends LeanArgs {
        get arg() {
            return this.args[0];
        }

        set arg(v) {
            this.args[0] = v;
            v.parent = this;
        }

        set sequential_tactic_combinator(val) {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanSequentialTacticCombinator) {
                    this.args[i] = val;
                    val.parent = this;
                    return;
                }
            }
        }

        get sequential_tactic_combinator() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanSequentialTacticCombinator) return this.args[i];
            }
        }

        insert(caret, func, type) {
            const last = this.args[this.args.length - 1];
            if (caret === last) {
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                const newCaret = new LeanCaret(this.indent, caret.level);
                this.push(new Ctor(newCaret, this.indent, caret.level));
                return newCaret;
            }
            throw new Error(`insert is unexpected for ${this.constructor.name}`);
        }

        insert_if(caret) {
            if (this.arg === caret || (this.arg != null && leanSubtreeContains(this.arg, caret))) {
                return caret.parent.insert_ite(caret);
            }
            if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
            throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.arg && this.indent < indent && caret instanceof LeanArgsSpaceSeparated) {
                const $new = new LeanCaret(indent, caret.level);
                caret.push($new);
                return $new;
            }
            // Bare keyword whose operand starts on the following, deeper-indented line
            // (a `show` followed by a deeper-indented operand line): the operand belongs to this node, not to a new statement.
            if (caret === this.arg && caret instanceof LeanCaret && this.indent < indent && !leanIsInfixContinue(next)) {
                const $new = new LeanCaret(indent, caret.level);
                this.replace(caret, $new);
                return $new;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
    }

    class LeanTactic extends LeanSyntax {
        constructor(name, arg, indent, level) {
            super([arg], indent, level);
            this.tacticName = name;
            this.only = undefined;
        }

        static continueSequentialTacticCombinator(node, indent) {
            for (let p = node.parent, c = node; p; c = p, p = p.parent) {
                if (p instanceof Lean_def || p instanceof LeanModule) return null;
                if (!(p instanceof LeanTactic || p instanceof Lean_let)) continue;
                if (p.indent > indent) continue;
                if (c !== p.args[p.args.length - 1]) return null;
                const caret = new LeanCaret(indent, c.level);
                p.push(caret);
                return caret;
            }
            return null;
        }

        get stack_priority() {
            if (this.parent instanceof LeanBy) return LeanColon.input_priority;
            if (this.tacticName === 'obtain') return LeanAssign.input_priority - 1;
            return LeanAssign.input_priority;
        }

        get modifiers() {
            return this.args.slice(1);
        }

        get at() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanAt) return this.args[i];
            }
        }

        get with() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanWith) return this.args[i];
            }
        }

        get using() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanUsing) return this.args[i];
            }
        }

        get by() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanBy) return this.args[i];
            }
            let a = this.arg;
            if (a instanceof LeanColon && a.rhs instanceof LeanAssign) a = a.rhs;
            if (a instanceof LeanAssign && a.rhs instanceof LeanBy) return a.rhs;
        }

        get arrow() {
            for (let i = this.args.length - 1; i >= 0; i--) {
                if (this.args[i] instanceof LeanRightarrow) return this.args[i];
            }
        }

        echo() {
            const token = this.get_echo_token();
            const {sequential_tactic_combinator} = this;
            const has_sequential_tactic_combinator = sequential_tactic_combinator && sequential_tactic_combinator.arg.indent;
            if (token) {
                const echo = new LeanTactic('echo', token, this.indent, this.level);
                if (token instanceof LeanToken && token.text === '*') 
                    // echo * simp at *
                    return [1, echo, this];
                const {by, with: $with} = this;
                if (by && by.arg instanceof LeanStatements) by.echo();
                if ($with && $with.args.length) $with.echo();
                if (this.tacticName === 'case') {
                    const arrow = this.arrow;
                    if (arrow && arrow.rhs instanceof LeanStatements) arrow.rhs.echo();
                }
                if (has_sequential_tactic_combinator && !sequential_tactic_combinator.newlineBehind) {
                    echo.push(sequential_tactic_combinator);
                    this.sequential_tactic_combinator = new LeanSequentialTacticCombinator(echo, this.indent, this.level, false, false);
                    sequential_tactic_combinator.echo();
                    return;
                }
                return [1, this, echo];
            }
            if (has_sequential_tactic_combinator) sequential_tactic_combinator.echo();
            else {
                const block = this.repeat_block();
                if (block) block.echo();
            }
        }

        /**
         * Port of `LeanTactic::getEcho`.
         * @returns {LeanTactic | undefined}
         */
        getEcho() {
            if (this.tacticName === 'echo') return this;
            if (this.tacticName === 'try' && this.arg instanceof LeanTactic && this.arg.tacticName === 'echo') return this.arg;
        }

        get_echo_token() {
            const at = this.at;
            if (at) {
                let token = at.arg;
                if (this.tacticName === 'split') {
                    if (this.has_tactic_block_followed()) return;
                } else {
                    if (token instanceof LeanArgsSpaceSeparated) {
                        token = new LeanArgsCommaSeparated(
                            token.args.map((a) => a.clone()),
                            this.indent,
                            token.level,
                        );
                    }
                }
                return token;
            }
            let token = [];
            let turnstile = '⊢';
            const arg = this.arg;
            switch (this.tacticName) {
                case 'intro':
                case 'by_contra':
                    if (arg instanceof LeanToken) token.push(arg.clone());
                    else if (arg instanceof LeanArgsSpaceSeparated) {
                        for (const a of arg.tokens_space_separated()) {
                            if (a instanceof LeanToken) token.push(a.clone());
                            else if (Array.isArray(a)) for (const x of a) token.push(x.clone());
                        }
                    } else if (arg instanceof LeanAngleBracket) {
                        const inner = arg.arg;
                        if (inner instanceof LeanToken) token.push(inner.clone());
                        else if (inner instanceof LeanArgsCommaSeparated)
                            token = inner.args.map((x) => x.clone());
                    }
                    break;
                case 'denote':
                case "denote'":
                    if (arg instanceof LeanColon) {
                        const v = arg.lhs;
                        if (v instanceof LeanToken) token.push(v.clone());
                    }
                    turnstile = null;
                    break;
                case 'by_cases':
                    if (arg instanceof LeanColon) {
                        const v = arg.lhs;
                        if (v instanceof LeanToken) {
                            if (this.has_tactic_block_followed()) return;
                            token.push(v.clone());
                        }
                    }
                    break;
                case 'split_ifs': {
                    const w = this.with;
                    if (w && w.sep() === ' ') {
                        if (this.has_tactic_block_followed()) return;
                        const tokens = w.tokens_space_separated();
                        if (tokens.length) token.push(tokens[0].clone());
                    }
                    break;
                }
                case "cases'": {
                    const w = this.with;
                    if (w && w.sep() === ' ' && this.sequential_tactic_combinator) {
                        const ut = w.unique_token(this.indent);
                        if (ut) token.push(ut);
                    }
                    break;
                }
                case 'injection': {
                    const w = this.with;
                    if (w && w.sep() === ' ') {
                        let v = w.args[0];
                        if (v instanceof LeanArgsSpaceSeparated) token = v.args;
                        else token = [v];
                        turnstile = null;
                    }
                    break;
                }
                case 'rcases': {
                    const w = this.with;
                    const bars = w.tokens_bar_separated();
                    if (w && bars.length) {
                        if (this.has_tactic_block_followed()) return;
                        for (const br of bars) {
                            if (Array.isArray(br))
                                token.push(...br.filter((t) => t.text !== 'rfl'));
                            else if (br.text !== 'rfl') token.push(br);
                            break;
                        }
                    }
                    break;
                }
                case 'obtain': {
                    const assign = arg;
                    if (assign instanceof LeanAssign) {
                        let {lhs} = assign;
                        if (lhs instanceof LeanColon) lhs = lhs.lhs;
                        if (lhs instanceof LeanAngleBracket) {
                            for (const t of lhs.tokens_comma_separated()) {
                                if (t.text !== 'rfl') token.push(t);
                            }
                        } else if (lhs instanceof LeanBitOr) {
                            if (this.has_tactic_block_followed()) return;
                            for (const br of lhs.tokens_bar_separated()) {
                                if (Array.isArray(br))
                                    token.push(...br.filter((t) => t.text !== 'rfl'));
                                else if (br.text !== 'rfl') token.push(br);
                                break;
                            }
                        }
                    }
                    break;
                }
                case 'specialize': {
                    let a = arg;
                    if (a instanceof LeanArgsSpaceSeparated && (a = a.args[0]) instanceof LeanToken) token.push(a.clone());
                    turnstile = null;
                    break;
                }
                case 'contrapose':
                case 'contrapose!':
                    if (arg instanceof LeanToken) token.push(arg.clone());
                    break;
                case 'sorry':
                case 'echo':
                    return;
                case 'try':
                    if (arg instanceof LeanTactic && arg.tacticName === 'echo') return;
                    break;
                default:
                    break;
            }
            if (this.has_tactic_block_followed() || this.parent instanceof LeanSequentialTacticCombinator);
            else if (turnstile) token.push(new LeanToken(turnstile, this.indent, this.level));
            if (token.length === 0) return;
            if (token.length === 1) return token[0];
            return new LeanArgsCommaSeparated(token, this.indent, this.level);
        }

        has_tactic_block_followed() {
            const p = this.parent;
            if (!(p instanceof LeanStatements)) return;
            const stmts = p.args;
            const idx = stmts.indexOf(this);
            if (idx < 0) return;
            for (let i = idx + 1; i < stmts.length; i++) {
                const stmt = stmts[i];
                if (stmt instanceof LeanTacticBlock) return true;
                if (!stmt.is_comment()) break;
            }
        }

        insert_bar(caret, prevToken, next) {
            // Lean opener is `first | tac | …`. Later `|`s are extra LeanBar args (see LeanBar.insert_bar).
            if (this.tacticName === 'first' && caret === this.arg && caret instanceof LeanCaret) {
                this.replace(caret, new LeanBar(caret, this.indent, caret.level));
                return caret;
            }
            return super.insert_bar(caret, prevToken, next);
        }

        insert_comma(caret) {
            if (caret === this.arg) {
                if (
                    caret instanceof LeanToken ||
                    caret instanceof LeanBinary ||
                    caret instanceof LeanPairedGroup
                ) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                    return $new;
                }
                if (caret instanceof LeanArgsCommaSeparated) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    caret.push($new);
                    return $new;
                }
            }
            const arg = this.arg;
            if (arg instanceof LeanArgsSpaceSeparated) {
                const index = arg.args.indexOf(caret);
                if (index >= 0) {
                    if (
                        caret instanceof LeanToken ||
                        caret instanceof LeanBinary ||
                        caret instanceof LeanPairedGroup
                    ) {
                        const $new = new LeanCaret(this.indent, caret.level);
                        arg.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                        return $new;
                    }
                    if (caret instanceof LeanArgsCommaSeparated) {
                        const $new = new LeanCaret(this.indent, caret.level);
                        caret.push($new);
                        return $new;
                    }
                }
            }
            return super.insert_comma(caret);
        }

        insert_line_comment(_caret, comment) {
            return this.push_line_comment(comment);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.arg) {
                if (this.indent < indent && caret instanceof LeanArgsSpaceSeparated) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    caret.push($new);
                    return $new;
                }
                if (this.indent < indent && (caret instanceof LeanToken || caret instanceof LeanProperty || caret instanceof LeanParenthesis)) {
                    const $new = new LeanCaret(indent, caret.level);
                    const nl = new LeanArgsNewLineSeparated([$new], indent, $new.level);
                    const c = nl.push_newlines(newline_count - 1);
                    this.replace(caret, new LeanArgsIndented(caret, nl, caret.indent, c.level));
                    return c;
                }
                if (caret instanceof LeanCaret && this.indent < indent) {
                    caret.indent = indent;
                    const nl = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                    this.replace(caret, nl);
                    return nl.push_newlines(newline_count - 1);
                }
                if (next === '<') {
                    const c = new LeanCaret(indent, caret.level);
                    this.push(c);
                    return c;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_only(caret) {
            if (caret !== this.args[this.args.length - 1]) {
                throw new Error(`LeanTactic.insert_only: unexpected for ${this.constructor.name}`);
            }
            this.only = true;
            return caret;
        }

        insert_semicolon(caret) {
            if (caret === this.arg) {
                if (this.is_inline_tactic_block()) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                    else this.replace(caret, new LeanArgsSemicolonSeparated([caret, $new], this.indent, caret.level));
                    return $new;
                }
                if (this.parent instanceof LeanStatements) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                    else this.parent.replace(this, new LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                    return $new;
                }
                if (this.parent instanceof LeanBy && this.parent.arg === this) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                    else this.parent.replace(this, new LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                    return $new;
                }
                if (this.parent instanceof LeanTacticBlock && this.parent.arg === this) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                    else this.parent.replace(this, new LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                    return $new;
                }
            }
            return super.insert_semicolon(caret);
        }

        insert_sequential_tactic_combinator(caret, prevToken, nextToken) {
            const last = this.args[this.args.length - 1];
            if (caret !== last)
                throw new Error(`LeanTactic.insert_sequential_tactic_combinator: unexpected for ${this.constructor.name}`);
            if (caret instanceof LeanCaret)
                this.replace(caret, new LeanSequentialTacticCombinator(caret, prevToken == '\n' ? caret.indent : this.indent, caret.level, prevToken == '\n', nextToken == '\n'));
            else {
                caret = new LeanCaret(this.indent, caret.level);
                // PHP constructs with default `newline=false` (multiline semantics);
                // promoted to a real indent by insert_newline when the rhs lands on a new line.
                this.push(new LeanSequentialTacticCombinator(caret, this.indent, caret.level, false, nextToken == '\n'));
            }
            return caret;
        }

        insert_tactic(caret, type) {
            const last = this.args[this.args.length - 1];
            if (last !== caret || !(caret instanceof LeanCaret)) {
                throw new Error(`LeanTactic.insert_tactic: unexpected for ${this.constructor.name}`);
            }
            if (this.is_inline_tactic_block()) {
                this.replace(caret, new LeanTactic(type, caret, this.indent, caret.level));
                return caret;
            }
            return this.insert_word(caret, type);
        }

        is_indented() {
            const p = this.parent;
            if (!p) return true;
            if (p instanceof LeanStatements || (p instanceof LeanIte && !p.inline)) return true;
            if (p instanceof LeanArgsNewLineSeparated) return true;
            if (p instanceof LeanArgsSpaceSeparated && p.parent instanceof LeanTactic) return true;
            if (p instanceof LeanSequentialTacticCombinator) return p.newlineBehind;
            return false;
        }

        is_inline_tactic_block() {
            return this.tacticName === 'repeat' || this.tacticName === 'try';
        }

        toJSON() {
            const name = this.tacticName;
            const arg = this.arg.toJSON();
            const modifiers = this.modifiers.map((m) => m.toJSON());
            /** Fixed key order so parse → print → parse matches JSON.stringify output. */
            return {
                modifiers,
                only: this.only,
                [name]: arg,
            };
        }

        latexFormat() {
            let func = escapeSpecialsForLatex(this.tacticName);
            if (this.only) func += '\\ only';
            const color = this.tacticName === 'sorry' ? '708' : '00f';
            func = `{\\color{#${color}}${func}}`;
            if (!(this.arg instanceof LeanCaret)) func += '\\ ';
            return func + Array(this.args.length).fill('%s').join('\\ ');
        }

        push_line_comment(comment) {
            const line = new LeanLineComment(comment, this.indent, this.level);
            this.push(line);
            return line;
        }

        relocate_last_comment() {
            const a = this.args[this.args.length - 1];
            if (a instanceof LeanRightarrow || a instanceof LeanWith) a.relocate_last_comment();
        }

        repeat_block() {
            if (this.tacticName === 'repeat') {
                const brace = this.arg;
                if (brace instanceof LeanBrace) {
                    const block = brace.arg;
                    if (block instanceof LeanStatements) return block;
                }
            }
        }

        split(syntax) {
            if (!syntax) syntax = {};
            syntax[this.tacticName] = true;
            const w = this.with;
            if (w && w.sep() === '\n') {
                const self = this.clone();
                if (self.with) self.with.args = [];
                const statements = [self];
                for (const stmt of w.args) statements.push(...stmt.split(syntax));
                return statements;
            }
            const {sequential_tactic_combinator} = this;
            if (sequential_tactic_combinator) {
                let block = sequential_tactic_combinator.arg;
                if (block instanceof LeanTacticBlock) {
                    if (block.arg instanceof LeanStatements) {
                        const self = this.clone();
                        const inner = self.sequential_tactic_combinator.arg;
                        const stmts = inner.arg;
                        inner.arg = new LeanCaret(0, 0);
                        const statements = [self];
                        stmts.swap_echo_star(syntax, statements);
                        return statements;
                    }
                } else if (
                    (block instanceof LeanTactic || block instanceof Lean_have || block instanceof Lean_let) &&
                    block.indent >= this.indent
                ) {
                    const self = this.clone();
                    const comb = self.sequential_tactic_combinator;
                    if (!comb.newlineBehind) {
                        // same-line `<;> rhs`: head stands alone, rhs splits into following steps
                        const la = self.args[self.args.length - 1];
                        if (la instanceof LeanSequentialTacticCombinator) self.args.pop();
                        const arr = [self];
                        arr.push(...comb.split(syntax));
                        return arr;
                    } else {
                        // newline after `<;>`: keep the operator with a hole, rhs follows indented
                        const cont = comb.arg;
                        comb.arg = new LeanCaret(0, 0);
                        const arr = [self];
                        arr.push(...cont.split(syntax));
                        return arr;
                    }
                }
            } else {
                const rb = this.repeat_block();
                if (rb) {
                    const self = this.clone();
                    self.arg = new LeanBrace(new LeanCaret(this.indent, this.level), this.indent, this.level);
                    const arr = [self];
                    for (const stmt of rb.args) arr.push(...stmt.split(syntax));
                    const rbrace = new LeanBrace(new LeanCaret(this.indent, this.level), this.indent, this.level);
                    rbrace.is_closed = false;
                    arr.push(rbrace);
                    return arr;
                }
            }
            const {by} = this;
            if (by && by.arg instanceof LeanStatements) {
                const self = this.clone();
                self.by.arg = new LeanCaret(by.indent, by.level);
                const statements = [self];
                by.arg.swap_echo_star(syntax, statements);
                return statements;
            }
            const {using} = this;
            if (using && using.arg instanceof LeanCalc) {
                const self = this.clone();
                let calc = self.using.arg;
                let statements = calc.split(syntax);
                calc.arg = new LeanCaret(using.indent, using.level);
                statements[0] = self;
                return statements;
            }
            if (this.tacticName === 'case') {
                const arrow = this.arrow;
                if (arrow && arrow.rhs instanceof LeanStatements) {
                    const self = this.clone();
                    const clonedArrow = self.arrow;
                    const stmts = clonedArrow.rhs;
                    clonedArrow.rhs = new LeanCaret(clonedArrow.indent, stmts.level);
                    const statements = [self];
                    stmts.swap_echo_star(syntax, statements);
                    return statements;
                }
            }
            return [this];
        }

        strFormat() {
            let func = this.tacticName;
            if (this.only) func += ' only';
            const parts = [];
            for (const arg of this.args) {
                if (arg instanceof LeanCaret);
                else if (arg instanceof LeanSequentialTacticCombinator && arg.newlineBefore) parts.push('\n');
                else if (arg instanceof LeanArgsNewLineSeparated) parts.push('\n');
                else parts.push(' ');
                parts.push('%s');
            }
            return func + parts.join('');
        }

        set_line(line) {
            this.line = line;
            let L = line;
            for (const arg of this.args) {
                if (arg == null) continue;
                if (arg instanceof LeanCaret);
                else if (arg instanceof LeanSequentialTacticCombinator && arg.newlineBefore) L++;
                else if (arg instanceof LeanArgsNewLineSeparated) L++;
                L = arg.set_line(L);
            }
            return L;
        }
    }

    class LeanBy extends LeanUnary {
        get operator() {
            return 'by';
        }

        get command() {
            return 'by';
        }

        echo() {
            this.arg.echo();
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                // When the next line is already deeper than `by`, use that indent; when it matches the assign
                // line (common after a column-0 `-- proof`), keep that indent so tactics stay inside the
                // proof block instead of bubbling to `LeanModule` (AST → string → AST).
                indent = indent >= this.indent ? indent : this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; ++i) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_semicolon(caret) {
            if (caret === this.arg) {
                const c = new LeanCaret(this.indent, caret.level);
                this.arg = new LeanArgsSemicolonSeparated([this.arg, c], this.indent, c.level);
                return c;
            }
            if (this.parent) return this.parent.insert_semicolon(this);
        }

        is_indented() {
            return this.parent instanceof LeanArgsCommaNewLineSeparated;
        }

        latexFormat() {
            const arg = this.arg;
            const command = '{\\color{#00f}by}';
            if (arg instanceof LeanStatements) return `\\begin{align*}\n${command} && \\\\\n%s\n\\end{align*}`;
            return `${command}\\ %s`;
        }

        relocate_last_comment() {
            this.arg.relocate_last_comment();
        }

        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }

        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }

        strFormat() {
            const s = this.sep();
            return `by${s}%s`;
        }
    }

    class LeanFrom extends LeanUnary {
        is_indented() {
            return this.parent instanceof LeanArgsCommaNewLineSeparated;
        }
        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }
        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }
        latexFormat() {
            const s = this.sep();
            return `${this.command}${s}%s`;
        }
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                indent = indent >= this.indent ? indent : this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; i++) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
        relocate_last_comment() {
            this.arg.relocate_last_comment();
        }
        echo() {
            this.arg.echo();
        }
        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }
        get operator() {
            return 'from';
        }
        get command() {
            return 'from';
        }
    }

    class LeanCalc extends LeanUnary {
        is_indented() {
            const p = this.parent;
            return !p || p instanceof LeanStatements || (p instanceof LeanIte && !p.inline) ||
                // `have h : a ≤ c :=\n    calc …` — term-mode calc on its own line keeps its column
                p instanceof LeanArgsNewLineSeparated;
        }

        sep() {
            const {arg} = this;
            if (arg instanceof LeanArgsNewLineSeparated) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }

        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }

        latexFormat() {
            const s = this.sep();
            return `${this.command}${s}%s`;
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret === this.arg) {
                if (caret instanceof LeanCaret) {
                    if (indent === this.indent) indent = this.indent + 2;
                    caret.indent = indent;
                    const nl = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                    this.replace(caret, nl);
                    return nl.push_newlines(newline_count - 1);
                }
                if (caret instanceof LeanAssign) {
                    const $new = this.push_args_indented(indent, newline_count, false);
                    if ($new) return $new;
                }
                if (caret instanceof LeanArgsNewLineSeparated) {
                    const c = new LeanCaret(indent, caret.level);
                    caret.push(c);
                    for (let i = 1; i < newline_count; ++i) {
                        caret.push(new LeanCaret(indent, caret.level));
                    }
                    return c;
                }
                if (leanIsInfixContinue(next))
                    return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        relocate_last_comment() {
            this.arg.relocate_last_comment();
        }

        /**
         * `calc a ≤ b := by gcongr; exact h\n    _ ≤ c := …` — a `_` line after a step whose proof is a
         * `by` block starts the next step of the innermost enclosing calc instead of continuing the tactic.
         * @returns {LeanCaret | null | undefined}
         */
        static continueStep(leaf, newline_count, indent) {
            let sawBy = false;
            for (let child = leaf, p = leaf.parent; p; child = p, p = p.parent) {
                if (p instanceof LeanBy) sawBy = true;
                if (p instanceof LeanCalc) {
                    if (child !== p.arg || !(child instanceof LeanAssign) || !sawBy || indent < p.indent) return null;
                    return p.insert_newline(child, newline_count, indent, '_');
                }
                const calc =
                    p instanceof LeanArgsIndented && p.parent instanceof LeanCalc ? p.parent
                    : p instanceof LeanArgsNewLineSeparated && p.parent instanceof LeanArgsIndented &&
                        p.parent.rhs === p && p.parent.parent instanceof LeanCalc ? p.parent.parent
                    : null;
                if (calc) {
                    if (!sawBy || indent < calc.indent || !(child instanceof LeanAssign)) return null;
                    if (p instanceof LeanArgsIndented && child !== p.lhs) return null;
                    return p.insert_newline(child, newline_count, indent, '_');
                }
            }
            return null;
        }

        get operator() {
            return 'calc';
        }

        get command() {
            return 'calc';
        }

        get stack_priority() {
            return LeanAssign.input_priority - 1;
        }

        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanArgsNewLineSeparated) L++;
            return this.arg.set_line(L);
        }

        echo() {
            const arg = this.arg;
            const echoStep = (stmt) => {
                if (stmt instanceof LeanAssign && stmt.rhs instanceof LeanBy) {
                    const byArg = stmt.rhs.arg;
                    if (byArg instanceof LeanStatements) {
                        const {indent, level} = byArg;
                        byArg.unshift(new LeanTactic('echo', new LeanToken('⊢', indent, level), indent, level));
                    }
                }
                stmt.echo();
            };
            if (arg instanceof LeanArgsNewLineSeparated) {
                for (const stmt of arg.args) echoStep(stmt);
            } else if (arg instanceof LeanArgsIndented) {
                echoStep(arg.rhs);
            }
        }

        split(syntax) {
            const arg = this.arg;
            if (arg instanceof LeanArgsNewLineSeparated) {
                if (syntax) syntax.calc = true;
                const self = this.clone();
                const stmts = self.arg.args;
                self.arg = new LeanCaret(this.indent, this.level);
                self.originalCalc = this;
                const statements = [self];
                for (const stmt of stmts) statements.push(...stmt.split(syntax));
                return statements;
            }
            if (arg instanceof LeanArgsIndented) {
                if (syntax) syntax.calc = true;
                const self = this.clone();
                const a = self.arg;
                const content = a.rhs;
                a.rhs = new LeanCaret(content.indent, content.level);
                self.originalCalc = this;
                const statements = [self];
                statements.push(...content.split(syntax));
                return statements;
            }
            return [this];
        }
    }

    class LeanMOD extends LeanUnary {
        is_indented() {
            return false;
        }
        sep() {
            return ' ';
        }
        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }
        latexFormat() {
            const s = this.sep();
            return `${this.command}\\${s}%s`;
        }
        get operator() {
            return 'MOD';
        }
        get command() {
            return '\\operatorname{MOD}';
        }
    }

    class LeanUsing extends LeanUnary {
        is_indented() {
            return false;
        }
        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }
        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }
        latexFormat() {
            const s = this.sep();
            return s === '\n' ? `${this.command}\n%s` : `${this.command}\\ %s`;
        }
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent < indent && caret === this.arg) {
                if (caret instanceof LeanArgsSpaceSeparated) {
                    const $new = new LeanCaret(indent, caret.level);
                    caret.push($new);
                    return $new;
                }
                if (
                    caret instanceof LeanToken ||
                    caret instanceof LeanProperty ||
                    caret instanceof LeanParenthesis
                ) {
                    const $new = new LeanCaret(indent, caret.level);
                    const nl = new LeanArgsNewLineSeparated([$new], indent, $new.level);
                    const c = nl.push_newlines(newline_count - 1);
                    this.arg = new LeanArgsIndented(caret, nl, caret.indent, c.level);
                    return c;
                }
                if (caret instanceof LeanArgsIndented) {
                    return caret.insert_newline(caret.rhs, newline_count, indent, next);
                }
            }
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; i++) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
        get operator() {
            return 'using';
        }
        get command() {
            return 'using';
        }

        echo() {
            this.arg.echo();
        }

        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }
    }

    class LeanAt extends LeanUnary {
        get operator() {
            return 'at';
        }

        get command() {
            return 'at';
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; i++) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        is_indented() {
            return false;
        }

        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }

        latexFormat() {
            const s = this.sep();
            return s === '\n' ? `{\\color{#00f}${this.command}}\n%s` : `{\\color{#00f}${this.command}}\\ %s`;
        }

        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }

        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }
    }

    class LeanIn extends LeanUnary {
        is_indented() {
            return false;
        }
        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }
        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }
        latexFormat() {
            const s = this.sep();
            return `${this.command}${s}%s`;
        }
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; i++) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
        get stack_priority() {
            return 18;
        }
        get operator() {
            return 'in';
        }
        get command() {
            return 'in';
        }
        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }
    }

    class LeanGeneralizing extends LeanUnary {
        is_indented() {
            return false;
        }
        sep() {
            const {arg} = this;
            if (arg instanceof LeanStatements) return '\n';
            if (arg instanceof LeanCaret) return '';
            return ' ';
        }
        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}%s`;
        }
        latexFormat() {
            const s = this.sep();
            return `${this.command}${s}%s`;
        }
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                for (let i = 1; i < newline_count; i++) {
                    caret = new LeanCaret(indent, caret.level);
                    this.arg.push(caret);
                }
                return caret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }
        get operator() {
            return 'generalizing';
        }
        get command() {
            return 'generalizing';
        }
        set_line(line) {
            this.line = line;
            let L = line;
            if (this.arg instanceof LeanStatements) L++;
            return this.arg.set_line(L);
        }
    }

    class LeanSequentialTacticCombinator extends LeanUnary {
        constructor(arg, indent, level, newlineBefore = false, newlineBehind = false) {
            super(arg, indent, level);
            this.newlineBefore = newlineBefore;
            this.newlineBehind = newlineBehind;
        }

        get operator() {
            return '<;>';
        }

        get command() {
            return '<;>';
        }

        echo() {
            let {arg} = this;
            if (arg instanceof LeanTacticBlock)
                arg.echo();
            else if (arg.indent > 0) {
                const {indent, level} = arg;
                const echo = new LeanTactic('echo', new LeanToken('⊢', indent, level), indent, level);
                const by_cases = this.parent;
                if (by_cases instanceof LeanTactic && by_cases.tacticName === 'by_cases' && by_cases.has_tactic_block_followed()) {
                    let sequential_tactic_combinator;
                    while ((sequential_tactic_combinator = arg.sequential_tactic_combinator) && sequential_tactic_combinator.arg.indent) arg = sequential_tactic_combinator;
                    // PHP passes newline=true (same-line): the echo boundary stays inline with the chain
                    arg.push(new LeanSequentialTacticCombinator(echo, indent, level, false, false));
                } else {
                    echo.push(new LeanSequentialTacticCombinator(arg, indent, level, false, this.newlineBehind));
                    this.arg = echo;
                    arg.echo();
                }
            }
        }

        getEcho() {
            if (!this.newlineBehind) {
                const e = this.arg;
                if (e instanceof LeanTactic && e.tacticName === 'echo') return e;
            }
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret instanceof LeanCaret && caret === this.arg) {
                if (next === '·' || next === '.') {
                    if (indent === this.indent) {
                        caret.indent = indent;
                        return caret;
                    }
                } else {
                    if (indent > this.indent) indent = this.indent + 2;
                    else indent = this.indent;
                    caret.indent = indent;
                    return caret;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_tactic(caret, type) {
            if (caret instanceof LeanCaret) {
                this.arg = new LeanTactic(type, caret, caret.indent, caret.level);
                return caret;
            }
            throw new Error(`LeanSequentialTacticCombinator.insert_tactic: unexpected`);
        }

        is_indented() {
            return this.newlineBefore;
        }

        latexFormat() {
            return `${this.command} %s`;
        }

        sep() {
            // PHP: arg is a tactic block, or a genuinely indented rhs of a multiline `<;>`
            if (this.arg instanceof LeanTacticBlock) return '\n';
            if (this.newlineBehind && this.arg.indent > 0) return '\n';
            if (this.arg instanceof LeanCaret) return '\n'; // split head renders a trailing `<;>` hole
            return ' ';
        }

        set_line(line) {
            this.line = line;
            if (this.newlineBehind && (this.arg instanceof LeanTacticBlock || this.arg.indent >= this.indent)) line++;
            return this.arg.set_line(line);
        }

        /**
         * @param {Record<string, unknown>} [syntax]
         * @returns {Lean[]}
         */
        split(syntax) {
            if (this.newlineBehind) return [this];
            const arg = this.arg;
            const args = arg.split(syntax);
            const self = this.clone();
            self.arg = args[0];
            args[0] = self;
            return args;
        }

        strFormat() {
            const sep = this.sep();
            return `${this.operator}${sep}%s`;
        }
    }

    class LeanTacticBlock extends LeanUnary {
        constructor(arg, indent, level, parent = null) {
            super(arg, indent, level, parent);
            arg.indent += 2;
        }

        get command() {
            return '\\cdot';
        }

        get operator() {
            return '·';
        }

        insert_line_comment(caret, comment) {
            if (caret instanceof LeanCaret) {
                const indent = this.indent + 2;
                const line = new LeanLineComment(comment, indent, caret.level);
                this.arg = new LeanStatements([line], indent, caret.level);
                return line;
            }
            throw new Error('LeanTacticBlock.insert_line_comment: unexpected');
        }

        insert_newline(caret, newline_count, indent, next) {
            if (caret === this.arg) {
                if (caret instanceof LeanCaret) {
                    if (this.indent <= indent) {
                        if (indent === this.indent) indent = this.indent + 2;
                        caret.indent = indent;
                        const stmts = new LeanStatements([caret], indent, caret.level);
                        this.arg = stmts;
                        let last = caret;
                        for (let i = 1; i < newline_count; i++) {
                            last = new LeanCaret(indent, caret.level);
                            stmts.push(last);
                        }
                        return last;
                    }
                } else if (caret instanceof LeanStatements) {
                    const block = caret;
                    if (indent >= block.indent) {
                        let last = null;
                        for (let i = 0; i < newline_count; i++) {
                            last = new LeanCaret(block.indent, block.level);
                            block.push(last);
                        }
                        return last;
                    }
                } else if (this.indent < indent) {
                    const oldArg = this.arg;
                    oldArg.indent = indent;
                    const c = new LeanCaret(indent, oldArg.level);
                    this.arg = new LeanStatements([oldArg, c], indent, c.level);
                    return c;
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        is_indented() {
            return true;
        }

        latexFormat() {
            const s = this.sep();
            return `${this.command}${s}%s`;
        }

        sep() {
            const a = this.arg;
            return a instanceof LeanStatements ? '\n' : a instanceof LeanCaret ? '' : ' ';
        }

        strFormat() {
            return `${this.operator}${this.sep()}%s`;
        }

        echo() {
            const statements = this.arg;
            if (!(statements instanceof LeanStatements)) return;
            statements.echo();
            const parent = this.parent;
            if (parent instanceof LeanSequentialTacticCombinator) {
                let token;
                const gp = parent.parent;
                if (gp instanceof LeanTactic) {
                    const w = gp.with;
                    if (w) token = w.unique_token(statements.indent);
                }
                if (token == null) token = new LeanToken('⊢', statements.indent, statements.level);
                statements.unshift(new LeanTactic('echo', token, statements.indent, statements.level));
            } else if (parent instanceof LeanStatements) {
                const index = parent.args.indexOf(this);
                let tacticBlockCount = 0;
                for (let i = index - 1; i >= 0; i--) {
                    const stmt = parent.args[i];
                    if (stmt.is_comment()) continue;
                    if (stmt instanceof LeanTacticBlock) {
                        ++tacticBlockCount;
                        continue;
                    }
                    if (stmt instanceof LeanTactic) {
                        if (stmt.tacticName === 'echo') continue;
                        const {indent, level} = statements;
                        switch (stmt.tacticName) {
                            case 'rcases': {
                                const $with = stmt.with;
                                const tokens = $with.tokens_bar_separated();
                                if ($with && tokens.length && tacticBlockCount < tokens.length) {
                                    let token = tokens[tacticBlockCount];
                                    if (Array.isArray(token)) {
                                        token = token.filter((token) => token.text !== 'rfl');
                                        token = [...token];
                                        token = token.map(token => {
                                            token = token.clone();
                                            token.indent = indent;
                                            token.level = level;
                                            return token;
                                        });
                                        token =
                                            token.length === 1 ? token[0] : new LeanArgsCommaSeparated(token, indent, level);
                                    } else {
                                        token = token.clone();
                                        token.indent = indent;
                                        token.level = level;
                                    }
                                    statements.unshift(new LeanTactic('echo', token, indent, level));
                                }
                                break;
                            }
                            case "cases'": {
                                const $with = stmt.with;
                                const tokens = w.tokens_space_separated();
                                if ($with instanceof LeanWith && tokens.length && tacticBlockCount < tokens.length) {
                                    const token = tokens[tacticBlockCount].clone();
                                    token.indent = indent;
                                    token.level = level;
                                    statements.unshift(
                                        new LeanTactic('echo', token, indent, level),
                                    );
                                }
                                break;
                            }
                            case 'obtain': {
                                const assign = stmt.arg;
                                if (assign instanceof LeanAssign) {
                                    let {lhs} = assign;
                                    if (lhs instanceof LeanColon) lhs = lhs.lhs;
                                    if (lhs instanceof LeanAngleBracket) {
                                        const tokens = lhs.tokens_comma_separated();
                                        if (tokens.length && tacticBlockCount < tokens.length) {
                                            const token = tokens[tacticBlockCount].clone();
                                            token.indent = indent;
                                            token.level = level;
                                            statements.unshift(
                                                new LeanTactic('echo', token, indent, level),
                                            );
                                        }
                                    } else if (lhs instanceof LeanBitOr) {
                                        const tokens = lhs.tokens_bar_separated();
                                        if (tokens.length && tacticBlockCount < tokens.length) {
                                            const token = tokens[tacticBlockCount].clone();
                                            token.indent = indent;
                                            token.level = level;
                                            statements.unshift(
                                                new LeanTactic('echo', token, indent, level),
                                            );
                                        }
                                    }
                                }
                                break;
                            }
                            case 'split_ifs': {
                                const $with = stmt.with;
                                if (!($with instanceof LeanWith) || $with.args.length !== 1) break;
                                let tokens = $with.args[0];
                                if (!(tokens instanceof LeanArgsSpaceSeparated || tokens instanceof LeanToken)) break;
                                statements.unshift(
                                    new LeanTactic(
                                        'echo',
                                        new LeanToken('⊢', indent, level),
                                        indent,
                                        level,
                                    ),
                                );
                                tokens = tokens.tactic_block_info()[tacticBlockCount] ?? null;
                                if (tokens) {
                                    const span = tokens.map(token => token.cache.size);
                                    let args = parent.args.slice(index);
                                    const {length} = args;
                                    for (let si = 0; si < span.length; si++) {
                                        const span_i = span[si];
                                        let token = tokens[si].clone();
                                        token.indent = this.indent;
                                        const stop = this.tactic_block(args, span_i);
                                        let new_list = args.slice(0, stop);
                                        const first = new_list[0];
                                        if (first instanceof LeanTactic && first.tacticName === 'echo') {
                                            if (first.arg instanceof LeanToken)
                                                first.arg = new LeanArgsCommaSeparated(
                                                    [token, first.arg],
                                                    this.indent,
                                                    token.level,
                                                );
                                            else first.arg.unshift(token);
                                        } else {
                                            new_list.unshift(
                                                new LeanTactic('echo', token, this.indent, token.level),
                                            );
                                        }
                                        const last = new_list[new_list.length - 1];
                                        if (last instanceof LeanTactic && last.tacticName === 'echo') {
                                            if (last.arg instanceof LeanToken)
                                                last.arg = new LeanArgsCommaSeparated(
                                                    [last.arg, token],
                                                    this.indent,
                                                    token.level,
                                                );
                                            else last.arg.push(token);
                                        } else {
                                            new_list.push(new LeanTactic('echo', token, this.indent, token.level));
                                        }
                                        args.splice(0, stop, ...new_list);
                                    }
                                    if (index) {
                                        const prev = parent.args[index - 1];
                                        if (prev instanceof LeanTactic && prev.tacticName === 'echo') {
                                            const first = args.shift();
                                            if (prev.arg instanceof LeanToken) {
                                                if (first.arg instanceof LeanToken)
                                                    prev.arg = new LeanArgsCommaSeparated(
                                                        [prev.arg, first.arg],
                                                        this.indent,
                                                        prev.arg.level,
                                                    );
                                                else
                                                    prev.arg = new LeanArgsCommaSeparated(
                                                        [prev.arg, ...first.arg.args],
                                                        this.indent,
                                                        prev.arg.level,
                                                    );
                                            } else {
                                                if (first.arg instanceof LeanToken) prev.arg.push(first.arg);
                                                else for (const arg of first.arg.args) prev.arg.push(arg);
                                            }
                                        }
                                    }
                                    return [length, ...args];
                                }
                                break;
                            }
                            case 'by_cases': {
                                const colon = stmt.arg;
                                if (colon instanceof LeanColon && colon.lhs instanceof LeanToken) {
                                    const tokens = colon.lhs.tokens_space_separated();
                                    var token = tokens[tacticBlockCount] ?? null;
                                    if (token) {
                                        token = token.clone();
                                        token.indent = this.indent;
                                        token.level = this.level;
                                        const echo = new LeanTactic('echo', token, this.indent, this.level);
                                        return [1, echo, this, echo.clone()];
                                    }
                                }
                                break;
                            }
                            case 'split': {
                                const at = stmt.at;
                                if (at) {
                                    let token = at.arg;
                                    if (token instanceof LeanToken) {
                                        token = token.clone();
                                        token.indent = indent;
                                        token.level = level;
                                        statements.unshift(
                                            new LeanTactic('echo', token, indent, level),
                                        );
                                    }
                                }
                                break;
                            }
                            default: {
                                let token = new LeanToken('⊢', indent, level);
                                const {sequential_tactic_combinator} = stmt;
                                if (sequential_tactic_combinator) {
                                    const tactic = sequential_tactic_combinator.arg;
                                    const tactic_token = tactic.get_echo_token();
                                    if (tactic_token) {
                                        if (tactic_token instanceof LeanArgsCommaSeparated) {
                                            tactic_token.push(token);
                                            token = tactic_token;
                                        } else {
                                            token = new LeanArgsCommaSeparated(
                                                [tactic_token, token],
                                                indent,
                                                level,
                                            );
                                        }
                                    }
                                }
                                statements.unshift(new LeanTactic('echo', token, indent, level));
                            }
                        }
                    }
                    break;
                }
            }
        }

        tactic_block(args, span) {
            let count = 0;
            let j = 0;
            while (count < span && j < args.length) {
                if (args[j] instanceof LeanTacticBlock) count++;
                j++;
            }
            return j;
        }

        split(syntax) {
            if (this.arg instanceof LeanStatements) {
                const self = this.clone();
                const stmts = self.arg;
                self.arg = new LeanCaret(this.indent, self.arg.level);
                const statements = [self];
                stmts.swap_echo_star(syntax, statements);
                return statements;
            }
            return [this];
        }

        set_line(line) {
            this.line = line;
            if (this.arg instanceof LeanStatements) line++;
            return this.arg.set_line(line);
        }
    }

    class LeanWith extends LeanArgs {
        static findAlternativeCaret(node, indent) {
            for (let p = node; p; p = p.parent) {
                if (p instanceof LeanWith && p.indent === indent) {
                    const cases = p.args;
                    if (cases.length > 0) {
                        const c = cases[cases.length - 1];
                        if (c instanceof LeanCaret) return c;
                        if (c instanceof LeanBar || c.is_comment()) {
                            const nc = new LeanCaret(p.indent, c.level);
                            p.push(nc);
                            return nc;
                        }
                    }
                }
            }
            return null;
        }

        /**
         * @param {Lean} arg
         * @param {number} indent
         * @param {number} level
         * @param {import('./node.js').Node | null} [parent]
         */
        constructor(arg, indent, level, parent = null) {
            super([arg], indent, level, parent);
        }

        is_indented() {
            return false;
        }

        get stack_priority() {
            return this.parent instanceof Lean_match ? 23 : 17;
        }

        get operator() {
            return 'with';
        }
        get command() {
            return 'with';
        }

        sep() {
            if (this.args.length > 1) return '\n';
            if (!this.args.length) return '';
            const [caret] = this.args;
            // `match … with` then `| pat =>`: first case is `LeanBar`; `tokens_space_separated()` is `[]` but
            // `[]` is truthy in JS, so we wrongly used ` ` and re-parse merged `with` and `|` (round-trip loss).
            if (caret instanceof LeanBar) return '\n';
            return caret instanceof LeanCaret || caret.tokens_space_separated() || caret instanceof LeanBitOr
                ? ' '
                : '\n';
        }

        strFormat() {
            const s = this.sep();
            return `${this.operator}${s}${Array(this.args.length).fill('%s').join('\n')}`;
        }

        relocate_last_comment() {
            const a = this.args[this.args.length - 1];
            a.relocate_last_comment();
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent > indent) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            const cases = this.args;
            if (cases.length > 0) {
                let c = cases[cases.length - 1];
                if (c instanceof LeanCaret) return c;
                if (next === '|') {
                    if (c instanceof LeanBar || c.is_comment()) {
                        const nc = new LeanCaret(this.indent, c.level);
                        this.push(nc);
                        return nc;
                    }
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_bar(caret, prevToken, next) {
            const cases = this.args;
            const last = cases[cases.length - 1];
            if (last === caret) {
                if (caret instanceof LeanCaret) {
                    this.replace(caret, new LeanBar(caret, this.indent, caret.level));
                    return caret;
                }
                const $new = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanBitOr(caret, $new, this.indent, caret.level));
                return $new;
            }
            throw new Error(`LeanWith.insert_bar: unexpected for ${this.constructor.name}`);
        }

        insert_tactic(caret, token) {
            if (caret instanceof LeanCaret) return this.insert_word(caret, token);
            return super.insert_tactic(caret, token);
        }

        insert_comma(caret) {
            if (caret === this.args[this.args.length - 1]) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            throw new Error(`LeanWith.insert_comma: unexpected for ${this.constructor.name}`);
        }

        set_line(line) {
            this.line = line;
            if (this.sep() === '\n') line++;
            for (const arg of this.args) {
                line = arg.set_line(line) + 1;
            }
            return line - 1;
        }

        tokens_bar_separated() {
            if (this.args.length === 1 && this.args[0] instanceof LeanBitOr) {
                return this.args[0].tokens_bar_separated();
            }
            return [];
        }

        unique_token(indent) {
            if (this.args.length === 1) {
                const stmt = this.args[0];
                if (stmt instanceof LeanBitOr || stmt instanceof LeanArgsSpaceSeparated) {
                    return stmt.unique_token(indent);
                }
            }
            return undefined;
        }

        tokens_space_separated() {
            if (this.args.length === 1 && this.args[0] instanceof LeanArgsSpaceSeparated) {
                return this.args[0].tokens_space_separated();
            }
            return [];
        }

        echo() {
            for (var arg of this.args) {
                arg.echo();
            }
        }
    }

    class LeanAttribute extends LeanUnary {
        get operator() {
            return '@';
        }

        get command() {
            return '@';
        }

        append($new, type) {
            const declType = typeof $new === 'string' ? $new : type;
            return this.push_accessibility(declType, 'public');
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.parent instanceof LeanTactic)
                return super.insert_newline(caret, newline_count, indent, next);
            return caret;
        }

        is_indented() {
            return false;
        }

        latexFormat() {
            return `${this.command} %s`;
        }

        push_accessibility($new, accessibility) {
            switch ($new) {
                case 'Lean_theorem':
                case 'Lean_lemma':
                case 'Lean_def':
                case 'Lean_abbrev': {
                    $new = LEAN_CLASSES[$new];
                    const {level, indent} = this;
                    const caret = new LeanCaret(indent, level);
                    const replacement = new $new(accessibility, caret, indent, level);
                    this.parent.replace(this, replacement);
                    replacement.attribute = this;
                    return caret;
                }
                default:
                    throw new Error(`push_accessibility is unexpected for ${this.constructor.name}`);
            }
        }

        sep() {
            return '';
        }

        strFormat() {
            return `${this.operator}${this.sep()}%s`;
        }
    }

    return {
        LeanSyntax,
        LeanTactic,
        LeanBy,
        LeanFrom,
        LeanCalc,
        LeanMOD,
        LeanUsing,
        LeanAt,
        LeanIn,
        LeanGeneralizing,
        LeanSequentialTacticCombinator,
        LeanTacticBlock,
        LeanWith,
        LeanAttribute,
    };
}
