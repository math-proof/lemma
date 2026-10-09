/**
 * Syntax and tactics: `LeanSyntax`, `LeanTactic`, and the wrappers that
 * follow them through `LeanAttribute` (`by`, `from`, `calc`, `at`, `<;>`,
 * tactic blocks, `with`, attributes).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { escapeSpecialsForLatex, leanIsInfixContinue, leanSubtreeContains } from './utility.js';
import { LeanArgs, LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanSyntax extends LeanArgs {
    static { this.register(); }

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
            const Ctor = typeof func === 'string' ? L[func] : func;
            const newCaret = new L.LeanCaret(this.indent, caret.level);
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
        // Hanging args under a tactic app (`exact f a\n  b\n  c`): wrap the
        // on-line `LeanArgsSpaceSeparated` in `LeanArgsIndented` so serialize
        // keeps newlines. Pushing into the space-list used to flatten them.
        if (caret === this.arg && this.indent < indent && caret instanceof L.LeanArgsSpaceSeparated) {
            const nlCaret = new L.LeanCaret(indent, caret.level);
            const nl = new L.LeanArgsNewLineSeparated([nlCaret], indent, caret.level);
            const c = nl.push_newlines(newline_count - 1);
            this.replace(caret, new L.LeanArgsIndented(caret, nl, this.indent, c.level));
            return c;
        }
        // Bare keyword whose operand starts on the following, deeper-indented line
        // (a `show` followed by a deeper-indented operand line): the operand belongs to this node, not to a new statement.
        if (caret === this.arg && caret instanceof L.LeanCaret && this.indent < indent && !leanIsInfixContinue(next)) {
            const $new = new L.LeanCaret(indent, caret.level);
            this.replace(caret, $new);
            return $new;
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }
}

export class LeanTactic extends LeanSyntax {
    static { this.register(); }

    constructor(name, arg, indent, level) {
        super([arg], indent, level);
        this.tacticName = name;
        this.only = undefined;
    }

    static continueSequentialTacticCombinator(node, indent) {
        for (let p = node.parent, c = node; p; c = p, p = p.parent) {
            if (p instanceof L.Lean_def || p instanceof L.LeanModule) return null;
            if (!(p instanceof LeanTactic || p instanceof L.Lean_let)) continue;
            if (p.indent > indent) continue;
            if (c !== p.args[p.args.length - 1]) return null;
            const caret = new L.LeanCaret(indent, c.level);
            p.push(caret);
            return caret;
        }
        return null;
    }

    /**
     * Is `node` (the current leaf) a top-level pattern of `rintro`, where `-` is the clear
     * pattern (`rintro _ ⟨D, hD, rfl⟩ -`, `rintro - h`) rather than subtraction?
     * Space-separated patterns can sit in nested `LeanArgsSpaceSeparated` (`p (hp | hp) -`).
     * @param {Lean} node
     */
    static isRintroPattern(node) {
        let {parent} = node;
        while (parent instanceof L.LeanArgsSpaceSeparated) [node, parent] = [parent, parent.parent];
        return parent instanceof LeanTactic && parent.tacticName === 'rintro' && parent.arg === node;
    }

    /**
     * Push the `rintro` clear pattern `-` after `node` as one more space-separated word.
     * @param {Lean} node the current leaf, see `isRintroPattern`
     * @param {string} token `-`
     */
    static pushRintroClear(node, token) {
        const {LeanCaret, LeanArgsSpaceSeparated, LeanToken} = L;
        if (node instanceof LeanCaret) return node.parent.insert_word(node, token);
        const {parent} = node;
        if (parent instanceof LeanArgsSpaceSeparated) {
            const $new = new LeanToken(token, parent.indent, node.level);
            parent.push($new);
            return $new;
        }
        return node.push_token(token);
    }

    get stack_priority() {
        // Term-level `(by tac : T)`: the `:` is a type ascription outside the `by`. Not for
        // `by_cases h : p`, whose `:` is its own syntax: `fun ω ↦ by by_cases h : ω ∈ s <;> simp [h]`
        // must keep `h : ω ∈ s` inside the tactic, or `<;> simp` is torn off the line in the echo.
        if (this.parent instanceof LeanBy && this.tacticName !== 'by_cases') return L.LeanColon.input_priority;
        if (this.tacticName === 'obtain') return L.LeanAssign.input_priority - 1;
        return L.LeanAssign.input_priority;
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
        if (a instanceof L.LeanColon && a.rhs instanceof L.LeanAssign) a = a.rhs;
        if (a instanceof L.LeanAssign && a.rhs instanceof LeanBy) return a.rhs;
    }

    get arrow() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof L.LeanRightarrow) return this.args[i];
        }
    }

    echo() {
        const token = this.get_echo_token();
        const {sequential_tactic_combinator} = this;
        const has_sequential_tactic_combinator = sequential_tactic_combinator && sequential_tactic_combinator.arg.indent;
        if (token) {
            const echo = new LeanTactic('echo', token, this.indent, this.level);
            if (token instanceof L.LeanToken && token.text === '*') 
                // echo * simp at *
                return [1, echo, this];
            const {by, with: $with} = this;
            if (by && by.arg instanceof L.LeanStatements) by.echo();
            if ($with && $with.args.length) $with.echo();
            if (this.tacticName === 'case') {
                const arrow = this.arrow;
                if (arrow && arrow.rhs instanceof L.LeanStatements) arrow.rhs.echo();
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
                if (token instanceof L.LeanArgsSpaceSeparated) {
                    token = new L.LeanArgsCommaSeparated(
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
                if (arg instanceof L.LeanToken) token.push(arg.clone());
                else if (arg instanceof L.LeanArgsSpaceSeparated) {
                    for (const a of arg.tokens_space_separated()) {
                        if (a instanceof L.LeanToken) token.push(a.clone());
                        else if (Array.isArray(a)) for (const x of a) token.push(x.clone());
                    }
                } else if (arg instanceof L.LeanAngleBracket) {
                    const inner = arg.arg;
                    if (inner instanceof L.LeanToken) token.push(inner.clone());
                    else if (inner instanceof L.LeanArgsCommaSeparated)
                        token = inner.args.map((x) => x.clone());
                }
                break;
            case 'denote':
            case "denote'":
                if (arg instanceof L.LeanColon) {
                    const v = arg.lhs;
                    if (v instanceof L.LeanToken) token.push(v.clone());
                }
                turnstile = null;
                break;
            case 'by_cases':
                if (arg instanceof L.LeanColon) {
                    const v = arg.lhs;
                    if (v instanceof L.LeanToken) {
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
                    if (v instanceof L.LeanArgsSpaceSeparated) token = v.args;
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
                if (assign instanceof L.LeanAssign) {
                    let {lhs} = assign;
                    if (lhs instanceof L.LeanColon) lhs = lhs.lhs;
                    if (lhs instanceof L.LeanAngleBracket) {
                        for (const t of lhs.tokens_comma_separated()) {
                            if (t.text !== 'rfl') token.push(t);
                        }
                    } else if (lhs instanceof L.LeanBitOr) {
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
                if (a instanceof L.LeanArgsSpaceSeparated && (a = a.args[0]) instanceof L.LeanToken) token.push(a.clone());
                turnstile = null;
                break;
            }
            case 'contrapose':
            case 'contrapose!':
                if (arg instanceof L.LeanToken) token.push(arg.clone());
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
        else if (turnstile) token.push(new L.LeanToken(turnstile, this.indent, this.level));
        if (token.length === 0) return;
        if (token.length === 1) return token[0];
        return new L.LeanArgsCommaSeparated(token, this.indent, this.level);
    }

    has_tactic_block_followed() {
        const p = this.parent;
        if (!(p instanceof L.LeanStatements)) return;
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
        if (this.tacticName === 'first' && caret === this.arg && caret instanceof L.LeanCaret) {
            this.replace(caret, new L.LeanBar(caret, this.indent, caret.level));
            return caret;
        }
        return super.insert_bar(caret, prevToken, next);
    }

    insert_comma(caret) {
        if (caret === this.arg) {
            if (
                caret instanceof L.LeanToken ||
                caret instanceof L.LeanBinary ||
                caret instanceof L.LeanPairedGroup
            ) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                this.replace(caret, new L.LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            if (caret instanceof L.LeanArgsCommaSeparated) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                caret.push($new);
                return $new;
            }
        }
        const arg = this.arg;
        if (arg instanceof L.LeanArgsSpaceSeparated) {
            const index = arg.args.indexOf(caret);
            if (index >= 0) {
                if (
                    caret instanceof L.LeanToken ||
                    caret instanceof L.LeanBinary ||
                    caret instanceof L.LeanPairedGroup
                ) {
                    const $new = new L.LeanCaret(this.indent, caret.level);
                    arg.replace(caret, new L.LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                    return $new;
                }
                if (caret instanceof L.LeanArgsCommaSeparated) {
                    const $new = new L.LeanCaret(this.indent, caret.level);
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
            // Hanging args after a multi-arg first line (`exact f a\n  b`): wrap in
            // LeanArgsIndented. Old code pushed into the space-list at `this.indent`,
            // which flattened the hang on serialize.
            if (this.indent < indent && caret instanceof L.LeanArgsSpaceSeparated) {
                const $new = new L.LeanCaret(indent, caret.level);
                const nl = new L.LeanArgsNewLineSeparated([$new], indent, $new.level);
                const c = nl.push_newlines(newline_count - 1);
                this.replace(caret, new L.LeanArgsIndented(caret, nl, this.indent, c.level));
                return c;
            }
            if (this.indent < indent && (caret instanceof L.LeanToken || caret instanceof L.LeanProperty || caret instanceof L.LeanParenthesis)) {
                const $new = new L.LeanCaret(indent, caret.level);
                const nl = new L.LeanArgsNewLineSeparated([$new], indent, $new.level);
                const c = nl.push_newlines(newline_count - 1);
                this.replace(caret, new L.LeanArgsIndented(caret, nl, caret.indent, c.level));
                return c;
            }
            if (caret instanceof L.LeanCaret && this.indent < indent) {
                caret.indent = indent;
                const nl = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
                this.replace(caret, nl);
                return nl.push_newlines(newline_count - 1);
            }
            if (next === '<') {
                const c = new L.LeanCaret(indent, caret.level);
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
                const $new = new L.LeanCaret(this.indent, caret.level);
                if (caret instanceof L.LeanArgsSemicolonSeparated) caret.push($new);
                else this.replace(caret, new L.LeanArgsSemicolonSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            if (this.parent instanceof L.LeanStatements) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                if (caret instanceof L.LeanArgsSemicolonSeparated) caret.push($new);
                else this.parent.replace(this, new L.LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                return $new;
            }
            if (this.parent instanceof LeanBy && this.parent.arg === this) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                if (caret instanceof L.LeanArgsSemicolonSeparated) caret.push($new);
                else this.parent.replace(this, new L.LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                return $new;
            }
            if (this.parent instanceof LeanTacticBlock && this.parent.arg === this) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                if (caret instanceof L.LeanArgsSemicolonSeparated) caret.push($new);
                else this.parent.replace(this, new L.LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                return $new;
            }
        }
        return super.insert_semicolon(caret);
    }

    insert_sequential_tactic_combinator(caret, prevToken, nextToken) {
        const last = this.args[this.args.length - 1];
        if (caret !== last)
            throw new Error(`LeanTactic.insert_sequential_tactic_combinator: unexpected for ${this.constructor.name}`);
        if (caret instanceof L.LeanCaret)
            this.replace(caret, new LeanSequentialTacticCombinator(caret, prevToken == '\n' ? caret.indent : this.indent, caret.level, prevToken == '\n', nextToken == '\n'));
        else {
            caret = new L.LeanCaret(this.indent, caret.level);
            // PHP constructs with default `newline=false` (multiline semantics);
            // promoted to a real indent by insert_newline when the rhs lands on a new line.
            this.push(new LeanSequentialTacticCombinator(caret, this.indent, caret.level, false, nextToken == '\n'));
        }
        return caret;
    }

    insert_tactic(caret, type) {
        const last = this.args[this.args.length - 1];
        if (last !== caret || !(caret instanceof L.LeanCaret)) {
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
        if (p instanceof L.LeanStatements || (p instanceof L.LeanIte && !p.inline)) return true;
        if (p instanceof L.LeanArgsNewLineSeparated) return true;
        if (p instanceof L.LeanArgsSpaceSeparated && p.parent instanceof LeanTactic) return true;
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
        if (!(this.arg instanceof L.LeanCaret)) func += '\\ ';
        return func + Array(this.args.length).fill('%s').join('\\ ');
    }

    push_line_comment(comment) {
        const line = new L.LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }

    relocate_last_comment() {
        const a = this.args[this.args.length - 1];
        if (a instanceof L.LeanRightarrow || a instanceof LeanWith) a.relocate_last_comment();
    }

    repeat_block() {
        if (this.tacticName === 'repeat') {
            const brace = this.arg;
            if (brace instanceof L.LeanBrace) {
                const block = brace.arg;
                if (block instanceof L.LeanStatements) return block;
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
                if (block.arg instanceof L.LeanStatements) {
                    const self = this.clone();
                    const inner = self.sequential_tactic_combinator.arg;
                    const stmts = inner.arg;
                    inner.arg = new L.LeanCaret(0, 0);
                    const statements = [self];
                    stmts.swap_echo_star(syntax, statements);
                    return statements;
                }
            } else if (
                (block instanceof LeanTactic || block instanceof L.Lean_have || block instanceof L.Lean_let) &&
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
                    comb.arg = new L.LeanCaret(0, 0);
                    const arr = [self];
                    arr.push(...cont.split(syntax));
                    return arr;
                }
            }
        } else {
            const rb = this.repeat_block();
            if (rb) {
                const self = this.clone();
                self.arg = new L.LeanBrace(new L.LeanCaret(this.indent, this.level), this.indent, this.level);
                const arr = [self];
                for (const stmt of rb.args) arr.push(...stmt.split(syntax));
                const rbrace = new L.LeanBrace(new L.LeanCaret(this.indent, this.level), this.indent, this.level);
                rbrace.is_closed = false;
                arr.push(rbrace);
                return arr;
            }
        }
        const {by} = this;
        if (by && by.arg instanceof L.LeanStatements) {
            const self = this.clone();
            self.by.arg = new L.LeanCaret(by.indent, by.level);
            const statements = [self];
            by.arg.swap_echo_star(syntax, statements);
            return statements;
        }
        const {using} = this;
        if (using && using.arg instanceof LeanCalc) {
            const self = this.clone();
            let calc = self.using.arg;
            let statements = calc.split(syntax);
            calc.arg = new L.LeanCaret(using.indent, using.level);
            statements[0] = self;
            return statements;
        }
        if (this.tacticName === 'case') {
            const arrow = this.arrow;
            if (arrow && arrow.rhs instanceof L.LeanStatements) {
                const self = this.clone();
                const clonedArrow = self.arrow;
                const stmts = clonedArrow.rhs;
                clonedArrow.rhs = new L.LeanCaret(clonedArrow.indent, stmts.level);
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
            if (arg instanceof L.LeanCaret);
            else if (arg instanceof LeanSequentialTacticCombinator && arg.newlineBefore) parts.push('\n');
            else if (arg instanceof L.LeanArgsNewLineSeparated) parts.push('\n');
            else parts.push(' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }

    set_line(line) {
        this.line = line;
        let lineNo = line;
        for (const arg of this.args) {
            if (arg == null) continue;
            if (arg instanceof L.LeanCaret);
            else if (arg instanceof LeanSequentialTacticCombinator && arg.newlineBefore) lineNo++;
            else if (arg instanceof L.LeanArgsNewLineSeparated) lineNo++;
            lineNo = arg.set_line(lineNo);
        }
        return lineNo;
    }
}

export class LeanBy extends LeanUnary {
    static { this.register(); }

    get operator() {
        return 'by';
    }

    get command() {
        return 'by';
    }

    echo() {
        this.arg.echo();
    }

    /**
     * `:= by -- note`: the block's indent is only known at the next line, so keep the comment until
     * `insert_newline` makes it the block's first line. Replacing the caret by the comment left
     * `by -- note` without a block, and the proof bubbled out of the lemma.
     */
    insert_line_comment(caret, comment) {
        if (caret instanceof L.LeanCaret && caret === this.arg && this.pendingComment === undefined) {
            this.pendingComment = comment;
            return caret;
        }
        return super.insert_line_comment(caret, comment);
    }

    insert_newline(caret, newline_count, indent, next) {
        const {pendingComment} = this;
        delete this.pendingComment;
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            // When the next line is already deeper than `by`, use that indent; when it matches the assign
            // line (common after a column-0 `-- proof`), keep that indent so tactics stay inside the
            // proof block instead of bubbling to `LeanModule` (AST → string → AST).
            indent = indent >= this.indent ? indent : this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            if (pendingComment !== undefined)
                this.arg.unshift(new L.LeanLineComment(pendingComment, indent, caret.level));
            for (let i = 1; i < newline_count; ++i) {
                caret = new L.LeanCaret(indent, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        if (pendingComment !== undefined && caret === this.arg) caret = caret.push_line_comment(pendingComment);
        return super.insert_newline(caret, newline_count, indent, next);
    }

    insert_semicolon(caret) {
        if (caret === this.arg) {
            const c = new L.LeanCaret(this.indent, caret.level);
            this.arg = new L.LeanArgsSemicolonSeparated([this.arg, c], this.indent, c.level);
            return c;
        }
        if (this.parent) return this.parent.insert_semicolon(this);
    }

    is_indented() {
        return this.parent instanceof L.LeanArgsCommaNewLineSeparated;
    }

    latexFormat() {
        const arg = this.arg;
        const command = '{\\color{#00f}by}';
        if (arg instanceof L.LeanStatements) return `\\begin{align*}\n${command} && \\\\\n%s\n\\end{align*}`;
        return `${command}\\ %s`;
    }

    relocate_last_comment() {
        this.arg.relocate_last_comment();
    }

    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
        return ' ';
    }

    set_line(line) {
        this.line = line;
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }

    strFormat() {
        const s = this.sep();
        return `by${s}%s`;
    }
}

export class LeanFrom extends LeanUnary {
    static { this.register(); }

    is_indented() {
        return this.parent instanceof L.LeanArgsCommaNewLineSeparated;
    }
    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            indent = indent >= this.indent ? indent : this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            for (let i = 1; i < newline_count; i++) {
                caret = new L.LeanCaret(indent, caret.level);
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
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }
    get operator() {
        return 'from';
    }
    get command() {
        return 'from';
    }
}

export class LeanCalc extends LeanUnary {
    static { this.register(); }

    is_indented() {
        const p = this.parent;
        return !p || p instanceof L.LeanStatements || (p instanceof L.LeanIte && !p.inline) ||
            // `have h : a ≤ c :=\n    calc …` — term-mode calc on its own line keeps its column
            p instanceof L.LeanArgsNewLineSeparated;
    }

    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanArgsNewLineSeparated) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
            if (caret instanceof L.LeanCaret) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const nl = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
                this.replace(caret, nl);
                return nl.push_newlines(newline_count - 1);
            }
            if (caret instanceof L.LeanAssign) {
                const $new = this.push_args_indented(indent, newline_count, false);
                if ($new) return $new;
            }
            // a new step must be deeper than the calc's indent, unless the calc starts its own line (`:=⏎    calc`):
            // in `have h : T := calc⏎    _ = … := …` or a tactic `calc⏎    …` the calc carries the statement's indent,
            // so the next statement at that indent closes the calc instead of becoming a step
            if (caret instanceof L.LeanArgsNewLineSeparated && (indent > this.indent || this.parent instanceof L.LeanArgsNewLineSeparated)) {
                const c = new L.LeanCaret(indent, caret.level);
                caret.push(c);
                for (let i = 1; i < newline_count; ++i) {
                    caret.push(new L.LeanCaret(indent, caret.level));
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
                if (child !== p.arg || !(child instanceof L.LeanAssign) || !sawBy || indent < p.indent) return null;
                return p.insert_newline(child, newline_count, indent, '_');
            }
            const calc =
                p instanceof L.LeanArgsIndented && p.parent instanceof LeanCalc ? p.parent
                : p instanceof L.LeanArgsNewLineSeparated && p.parent instanceof L.LeanArgsIndented &&
                    p.parent.rhs === p && p.parent.parent instanceof LeanCalc ? p.parent.parent
                : null;
            if (calc) {
                if (!sawBy || indent < calc.indent || !(child instanceof L.LeanAssign)) return null;
                if (p instanceof L.LeanArgsIndented && child !== p.lhs) return null;
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
        return L.LeanAssign.input_priority - 1;
    }

    set_line(line) {
        this.line = line;
        let lineNo = line;
        if (this.arg instanceof L.LeanArgsNewLineSeparated) lineNo++;
        return this.arg.set_line(lineNo);
    }

    echo() {
        const arg = this.arg;
        const echoStep = (stmt) => {
            if (stmt instanceof L.LeanAssign && stmt.rhs instanceof LeanBy) {
                const byArg = stmt.rhs.arg;
                if (byArg instanceof L.LeanStatements) {
                    const {indent, level} = byArg;
                    byArg.unshift(new LeanTactic('echo', new L.LeanToken('⊢', indent, level), indent, level));
                }
            }
            stmt.echo();
        };
        if (arg instanceof L.LeanArgsNewLineSeparated) {
            for (const stmt of arg.args) echoStep(stmt);
        } else if (arg instanceof L.LeanArgsIndented) {
            echoStep(arg.rhs);
        }
    }

    split(syntax) {
        const arg = this.arg;
        if (arg instanceof L.LeanArgsNewLineSeparated) {
            if (syntax) syntax.calc = true;
            const self = this.clone();
            const stmts = self.arg.args;
            self.arg = new L.LeanCaret(this.indent, this.level);
            self.originalCalc = this;
            const statements = [self];
            for (const stmt of stmts) statements.push(...stmt.split(syntax));
            return statements;
        }
        if (arg instanceof L.LeanArgsIndented) {
            if (syntax) syntax.calc = true;
            const self = this.clone();
            const a = self.arg;
            const content = a.rhs;
            a.rhs = new L.LeanCaret(content.indent, content.level);
            self.originalCalc = this;
            const statements = [self];
            statements.push(...content.split(syntax));
            return statements;
        }
        return [this];
    }
}

export class LeanMOD extends LeanUnary {
    static { this.register(); }

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

export class LeanUsing extends LeanUnary {
    static { this.register(); }

    is_indented() {
        return false;
    }
    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
            if (caret instanceof L.LeanArgsSpaceSeparated) {
                const $new = new L.LeanCaret(indent, caret.level);
                caret.push($new);
                return $new;
            }
            if (
                caret instanceof L.LeanToken ||
                caret instanceof L.LeanProperty ||
                caret instanceof L.LeanParenthesis
            ) {
                const $new = new L.LeanCaret(indent, caret.level);
                const nl = new L.LeanArgsNewLineSeparated([$new], indent, $new.level);
                const c = nl.push_newlines(newline_count - 1);
                this.arg = new L.LeanArgsIndented(caret, nl, caret.indent, c.level);
                return c;
            }
            if (caret instanceof L.LeanArgsIndented) {
                return caret.insert_newline(caret.rhs, newline_count, indent, next);
            }
        }
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            for (let i = 1; i < newline_count; i++) {
                caret = new L.LeanCaret(indent, caret.level);
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
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }
}

export class LeanAt extends LeanUnary {
    static { this.register(); }

    get operator() {
        return 'at';
    }

    get command() {
        return 'at';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            for (let i = 1; i < newline_count; i++) {
                caret = new L.LeanCaret(indent, caret.level);
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
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }
}

export class LeanIn extends LeanUnary {
    static { this.register(); }

    is_indented() {
        return false;
    }
    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            for (let i = 1; i < newline_count; i++) {
                caret = new L.LeanCaret(indent, caret.level);
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
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }
}

export class LeanGeneralizing extends LeanUnary {
    static { this.register(); }

    is_indented() {
        return false;
    }
    sep() {
        const {arg} = this;
        if (arg instanceof L.LeanStatements) return '\n';
        if (arg instanceof L.LeanCaret) return '';
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
        if (this.indent <= indent && caret instanceof L.LeanCaret && caret === this.arg) {
            if (indent === this.indent) indent = this.indent + 2;
            caret.indent = indent;
            this.arg = new L.LeanStatements([caret], indent, caret.level);
            for (let i = 1; i < newline_count; i++) {
                caret = new L.LeanCaret(indent, caret.level);
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
        let lineNo = line;
        if (this.arg instanceof L.LeanStatements) lineNo++;
        return this.arg.set_line(lineNo);
    }
}

export class LeanSequentialTacticCombinator extends LeanUnary {
    static { this.register(); }

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
            const echo = new LeanTactic('echo', new L.LeanToken('⊢', indent, level), indent, level);
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
        if (caret instanceof L.LeanCaret && caret === this.arg) {
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
        if (caret instanceof L.LeanCaret) {
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
        if (this.arg instanceof L.LeanCaret) return '\n'; // split head renders a trailing `<;>` hole
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

export class LeanTacticBlock extends LeanUnary {
    static { this.register(); }

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
        if (caret instanceof L.LeanCaret) {
            const indent = this.indent + 2;
            const line = new L.LeanLineComment(comment, indent, caret.level);
            this.arg = new L.LeanStatements([line], indent, caret.level);
            return line;
        }
        throw new Error('LeanTacticBlock.insert_line_comment: unexpected');
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.arg) {
            if (caret instanceof L.LeanCaret) {
                if (this.indent <= indent) {
                    if (indent === this.indent) indent = this.indent + 2;
                    caret.indent = indent;
                    const stmts = new L.LeanStatements([caret], indent, caret.level);
                    this.arg = stmts;
                    let last = caret;
                    for (let i = 1; i < newline_count; i++) {
                        last = new L.LeanCaret(indent, caret.level);
                        stmts.push(last);
                    }
                    return last;
                }
            } else if (caret instanceof L.LeanStatements) {
                const block = caret;
                if (indent >= block.indent) {
                    let last = null;
                    for (let i = 0; i < newline_count; i++) {
                        last = new L.LeanCaret(block.indent, block.level);
                        block.push(last);
                    }
                    return last;
                }
            } else if (this.indent < indent) {
                const oldArg = this.arg;
                oldArg.indent = indent;
                const c = new L.LeanCaret(indent, oldArg.level);
                this.arg = new L.LeanStatements([oldArg, c], indent, c.level);
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
        return a instanceof L.LeanStatements ? '\n' : a instanceof L.LeanCaret ? '' : ' ';
    }

    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }

    echo() {
        const statements = this.arg;
        if (!(statements instanceof L.LeanStatements)) return;
        statements.echo();
        const parent = this.parent;
        if (parent instanceof LeanSequentialTacticCombinator) {
            let token;
            const gp = parent.parent;
            if (gp instanceof LeanTactic) {
                const w = gp.with;
                if (w) token = w.unique_token(statements.indent);
            }
            if (token == null) token = new L.LeanToken('⊢', statements.indent, statements.level);
            statements.unshift(new LeanTactic('echo', token, statements.indent, statements.level));
        } else if (parent instanceof L.LeanStatements) {
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
                                        token.length === 1 ? token[0] : new L.LeanArgsCommaSeparated(token, indent, level);
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
                            if (assign instanceof L.LeanAssign) {
                                let {lhs} = assign;
                                if (lhs instanceof L.LeanColon) lhs = lhs.lhs;
                                if (lhs instanceof L.LeanAngleBracket) {
                                    const tokens = lhs.tokens_comma_separated();
                                    if (tokens.length && tacticBlockCount < tokens.length) {
                                        const token = tokens[tacticBlockCount].clone();
                                        token.indent = indent;
                                        token.level = level;
                                        statements.unshift(
                                            new LeanTactic('echo', token, indent, level),
                                        );
                                    }
                                } else if (lhs instanceof L.LeanBitOr) {
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
                            if (!(tokens instanceof L.LeanArgsSpaceSeparated || tokens instanceof L.LeanToken)) break;
                            statements.unshift(
                                new LeanTactic(
                                    'echo',
                                    new L.LeanToken('⊢', indent, level),
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
                                        if (first.arg instanceof L.LeanToken)
                                            first.arg = new L.LeanArgsCommaSeparated(
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
                                        if (last.arg instanceof L.LeanToken)
                                            last.arg = new L.LeanArgsCommaSeparated(
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
                                        if (prev.arg instanceof L.LeanToken) {
                                            if (first.arg instanceof L.LeanToken)
                                                prev.arg = new L.LeanArgsCommaSeparated(
                                                    [prev.arg, first.arg],
                                                    this.indent,
                                                    prev.arg.level,
                                                );
                                            else
                                                prev.arg = new L.LeanArgsCommaSeparated(
                                                    [prev.arg, ...first.arg.args],
                                                    this.indent,
                                                    prev.arg.level,
                                                );
                                        } else {
                                            if (first.arg instanceof L.LeanToken) prev.arg.push(first.arg);
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
                            if (colon instanceof L.LeanColon && colon.lhs instanceof L.LeanToken) {
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
                                if (token instanceof L.LeanToken) {
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
                            let token = new L.LeanToken('⊢', indent, level);
                            const {sequential_tactic_combinator} = stmt;
                            if (sequential_tactic_combinator) {
                                const tactic = sequential_tactic_combinator.arg;
                                const tactic_token = tactic.get_echo_token();
                                if (tactic_token) {
                                    if (tactic_token instanceof L.LeanArgsCommaSeparated) {
                                        tactic_token.push(token);
                                        token = tactic_token;
                                    } else {
                                        token = new L.LeanArgsCommaSeparated(
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
        if (this.arg instanceof L.LeanStatements) {
            const self = this.clone();
            const stmts = self.arg;
            self.arg = new L.LeanCaret(this.indent, self.arg.level);
            const statements = [self];
            stmts.swap_echo_star(syntax, statements);
            return statements;
        }
        return [this];
    }

    set_line(line) {
        this.line = line;
        if (this.arg instanceof L.LeanStatements) line++;
        return this.arg.set_line(line);
    }
}

export class LeanWith extends LeanArgs {
    static { this.register(); }

    static findAlternativeCaret(node, indent) {
        for (let p = node; p; p = p.parent) {
            if (p instanceof LeanWith && p.indent === indent) {
                const cases = p.args;
                if (cases.length > 0) {
                    const c = cases[cases.length - 1];
                    if (c instanceof L.LeanCaret) return c;
                    if (c instanceof L.LeanBar || c.is_comment()) {
                        const nc = new L.LeanCaret(p.indent, c.level);
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

    /** `{ s with … }`: a structure update (the `with` closes a brace's space-separated head). */
    isStructUpdate() {
        const p = this.parent;
        return p instanceof L.LeanArgsSpaceSeparated && p.args[p.args.length - 1] === this && p.parent instanceof L.LeanBrace;
    }

    /**
     * `{ s with⏎ a := 1⏎ b := 2 }` (`inline` false) / `{ s with a := 1⏎ b := 2 }` (`inline` true).
     * @type {boolean | undefined}
     */
    inline = undefined;

    get stack_priority() {
        return this.parent instanceof L.Lean_match ? 23 : 17;
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
        if (caret instanceof L.LeanStatements && caret.structInst === true) return this.inline ? ' ' : '\n';
        // `match … with` then `| pat =>`: first case is `LeanBar`; `tokens_space_separated()` is `[]` but
        // `[]` is truthy in JS, so we wrongly used ` ` and re-parse merged `with` and `|` (round-trip loss).
        if (caret instanceof L.LeanBar) return '\n';
        return caret instanceof L.LeanCaret || caret.tokens_space_separated() || caret instanceof L.LeanBitOr
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
        if (this.args.length === 1 && caret === this.args[0] && this.isStructUpdate()) {
            const brace = this.parent.parent;
            if (indent > brace.indent || (indent > this.indent && !(caret instanceof L.LeanCaret))) {
                if (caret instanceof L.LeanCaret) {
                    // `{ s with⏎`: the fields follow, one per line, in column `indent`
                    caret.indent = indent;
                    const stmts = new L.LeanStatements([caret], indent, caret.level);
                    stmts.structInst = true;
                    this.args[0] = stmts;
                    stmts.parent = this;
                    this.inline = false;
                    return caret;
                }
                if (!(caret instanceof L.LeanStatements) && L.LeanBrace.isStructInstField(caret)) {
                    const [stmts, out] = L.LeanBrace.openStructInstBody(this, caret, newline_count, indent);
                    this.args[0] = stmts;
                    stmts.parent = this;
                    this.inline = true;
                    return out;
                }
            }
        }
        if (this.indent > indent) {
            return super.insert_newline(caret, newline_count, indent, next);
        }
        const cases = this.args;
        if (cases.length > 0) {
            let c = cases[cases.length - 1];
            if (c instanceof L.LeanCaret) return c;
            if (next === '|') {
                if (c instanceof L.LeanBar || c.is_comment()) {
                    const nc = new L.LeanCaret(this.indent, c.level);
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
            if (caret instanceof L.LeanCaret) {
                this.replace(caret, new L.LeanBar(caret, this.indent, caret.level));
                return caret;
            }
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.replace(caret, new L.LeanBitOr(caret, $new, this.indent, caret.level));
            return $new;
        }
        throw new Error(`LeanWith.insert_bar: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        if (caret instanceof L.LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    insert_comma(caret) {
        if (caret === this.args[this.args.length - 1]) {
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.replace(caret, new L.LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
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
        if (this.args.length === 1 && this.args[0] instanceof L.LeanBitOr) {
            return this.args[0].tokens_bar_separated();
        }
        return [];
    }

    unique_token(indent) {
        if (this.args.length === 1) {
            const stmt = this.args[0];
            if (stmt instanceof L.LeanBitOr || stmt instanceof L.LeanArgsSpaceSeparated) {
                return stmt.unique_token(indent);
            }
        }
        return undefined;
    }

    tokens_space_separated() {
        if (this.args.length === 1 && this.args[0] instanceof L.LeanArgsSpaceSeparated) {
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

export class LeanAttribute extends LeanUnary {
    static { this.register(); }

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
                $new = L[$new];
                const {level, indent} = this;
                const caret = new L.LeanCaret(indent, level);
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
