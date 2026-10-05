/**
 * Syntax and tactics: `LeanSyntax` and `LeanTactic`.
 *
 * `LeanArgs`, the argument-list classes, and the other classes already
 * declared above this factory stay in `lean.js` and are passed in, along
 * with `leanIsInfixContinue`, `leanSubtreeContains`, and
 * `escapeSpecialsForLatex`. Classes created later (`LeanBy`, sequential
 * combinators, tactic blocks, `Lean_def`, `Lean_let`, `Lean_have`, paired
 * delimiters, and the rest) are filled on `tacticLate`; methods only use
 * them via `instanceof` or `new`. `LEAN_CLASSES` is the shared registry
 * filled after this returns. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanArgs
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
    const LeanAt = lateCtor('LeanAt');
    const LeanBitOr = lateCtor('LeanBitOr');
    const LeanBrace = lateCtor('LeanBrace');
    const LeanBy = lateCtor('LeanBy');
    const LeanCalc = lateCtor('LeanCalc');
    const LeanPairedGroup = lateCtor('LeanPairedGroup');
    const LeanParenthesis = lateCtor('LeanParenthesis');
    const LeanSequentialTacticCombinator = lateCtor('LeanSequentialTacticCombinator');
    const LeanTacticBlock = lateCtor('LeanTacticBlock');
    const LeanUsing = lateCtor('LeanUsing');
    const LeanWith = lateCtor('LeanWith');
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

    return {
        LeanSyntax,
        LeanTactic,
    };
}
