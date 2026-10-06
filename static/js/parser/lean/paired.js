/**
 * Paired delimiters: `LeanPairedGroup` and parenthesis, bracket, brace, abs,
 * norm, inner, ceil, floor, white square bracket, and angle quotations.
 *
 * Arithmetic classes are consulted only from methods (`instanceof`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { Closable } from '../node.js';
import { LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/**
 * Abstract paired delimiters. Uses `Closable(LeanUnary)` like `MarkdownLink extends Closable(MarkdownArgs)` in `markdown.js`.
 */
export class LeanPairedGroup extends Closable(LeanUnary) {
    static { this.register(); }

    static input_priority = 60;

    argFormat() {
        return '%s';
    }

    /**
     * @param {Lean} caret
     * @param {string | typeof Lean} func
     * @param {string} type
     */
    insert(caret, func, type) {
        if (this.arg === caret) {
            if (caret instanceof L.LeanCaret) {
                const Ctor = typeof func === 'string' ? L[func] : func;
                this.arg = new Ctor(caret, this.indent, caret.level);
                return caret;
            }
            if (caret instanceof L.LeanToken) {
                const $new = new L.LeanCaret(this.indent, caret.level);
                const Ctor = typeof func === 'string' ? L[func] : func;
                this.arg = new L.LeanArgsSpaceSeparated([this.arg, new Ctor($new, this.indent, caret.level)], this.indent, caret.level);
                return $new;
            }
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_comma(caret) {
        caret = new L.LeanCaret(this.indent, caret.level);
        const a = this.arg;
        if (a instanceof L.LeanArgsCommaSeparated) {
            a.push(caret);
        } else {
            this.arg = new L.LeanArgsCommaSeparated([a, caret], this.indent, caret.level);
        }
        return caret;
    }

    insert_semicolon(caret) {
        caret = new L.LeanCaret(this.indent, caret.level);
        const a = this.arg;
        if (a instanceof L.LeanArgsSemicolonSeparated) {
            a.push(caret);
        } else {
            this.arg = new L.LeanArgsSemicolonSeparated([a, caret], this.indent, caret.level);
        }
        return caret;
    }

    insert_if(caret) {
        if (this.arg === caret && caret instanceof L.LeanCaret) {
            this.arg = new L.LeanIte([caret], caret.indent, caret.level);
            return caret;
        }
        if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newline_count, indent, next);
        }
        if (this.indent <= indent) {
            if (caret instanceof L.LeanCaret) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                if (this instanceof LeanBrace) {
                    this.arg = new L.LeanStatements([caret], indent, caret.level);
                    return caret;
                }
                this.arg = new L.LeanArgsCommaNewLineSeparated(
                    [new L.LeanArgsCommaSeparated([caret], indent, caret.level)],
                    indent,
                    caret.level,
                );
                return caret;
            }
            if (indent === this.indent) return caret;
            if (indent > this.indent) {
                if (caret instanceof L.LeanArgsSpaceSeparated) {
                    return this.push_args_indented(indent, newline_count, false);
                }
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    insert_tactic(caret, token) {
        if (caret instanceof L.LeanCaret) return this.insert_word(caret, token);
        if (this.parent) return this.parent.insert_tactic(caret, token);
        throw new Error(`LeanPairedGroup.insert_tactic: unexpected for ${this.constructor.name}`);
    }

    is_Expr() {
        return true;
    }

    /**
     * After the closing delimiter, a new token/space-separated arg arrives.
     * Push it into the parent's arg list (or wrap self+new in LeanArgsSpaceSeparated),
     * so tokens like `hsec_y` after `«y.bvar»` are not swallowed.
     */
    append($new, _func) {
        const {indent, level} = this;
        const caret = new L.LeanCaret(indent, level);
        if (typeof $new === 'string') {
            const Ctor = L[$new];
            const node = new Ctor(caret, indent, level);
            if (this.parent instanceof L.LeanArgsSpaceSeparated) {
                this.parent.push(node);
            } else {
                // Wrap the closed group itself (not its contents): `(a _) fun t => ?_` must not become `(a _ fun t => ?_)`.
                this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, node], indent, level));
            }
            return caret;
        }
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, $new], indent, level));
        return $new;
    }

    is_indented() {
        const parent = this.parent;
        return !(
            parent instanceof L.LeanTactic ||
            parent instanceof L.LeanArgsCommaSeparated ||
            parent instanceof L.LeanAssign ||
            parent instanceof L.LeanArgsSpaceSeparated ||
            parent instanceof L.LeanBinaryBoolean ||
            parent instanceof L.LeanRightarrow ||
            parent instanceof L.LeanUnaryArithmeticPre ||
            parent instanceof L.LeanArithmetic ||
            parent instanceof L.LeanProperty ||
            parent instanceof L.LeanColon ||
            parent instanceof L.LeanUnaryArithmeticPost ||
            parent instanceof LeanPairedGroup ||
            parent instanceof L.LeanBigOperator ||
            parent instanceof L.LeanGetElem ||
            parent instanceof L.LeanGetElemQue ||
            parent instanceof L.LeanGetElemQuote
        );
    }

    /** @param {string} funcName e.g. 'LeanParenthesis' */
    push_right(funcName) {
        if (this.constructor.name === funcName) {
            this.is_closed = true;
            // `a[i]'(proof)` is a complete term; stay on the get-elem so `*`, `.`, `[` bind outside the proof.
            if (this.parent instanceof L.LeanGetElemQuote && this.parent.args[2] === this)
                return this.parent;
            return this;
        }
        if (this.parent) return this.parent.push_right(funcName);
    }

    set_line(line) {
        this.line = line;
        const arg = this.arg;
        const hasNewline = arg instanceof L.LeanStatements;
        if (hasNewline) line++;
        line = arg.set_line(line);
        if (hasNewline) line++;
        return line;
    }

    strFormat(format) {
        format = format || this.argFormat();
        const {operator} = this;
        const open = typeof operator === 'string' ? operator[0] : operator[0];
        const close = typeof operator === 'string' ? operator[1] : operator[1];
        const c = this.is_closed;
        if (c) {
            format = open + format + close;
        } else if (c == null) {
            format = open + format;
        } else {
            format += close;
        }
        return format;
    }
}

/**
 * Multiline module-level `(...) := by` parenthesis closing (JS serializer parity); kept outside the class so
 * member-list audit matches PHP `LeanParenthesis` (no extra instance method vs `lean.php`).
 * @param {LeanParenthesis} paren
 */
function leanParenthesisLemmaAssignByMultilineClose(paren) {
    const asn = paren.parent;
    return (
        asn instanceof L.LeanAssign &&
        asn.parent instanceof L.LeanModule &&
        asn.rhs instanceof L.LeanBy &&
        (asn.indent ?? 0) > 0 &&
        String(paren.arg).includes('\n')
    );
}

/** Parentheses: inner `level` for rainbow LaTeX. Method order follows the reference `LeanParenthesis` class. */
export class LeanParenthesis extends LeanPairedGroup {
    static { this.register(); }

    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super(arg, indent, level, parent);
        this.arg.level++;
    }

    get stack_priority() {
        return 10;
    }

    get operator() {
        return '()';
    }

    argFormat() {
        const arg = this.arg;
        if (arg instanceof L.LeanBy) {
            const stmt = arg.arg;
            if (stmt instanceof L.LeanStatements) {
                const last = stmt.args[stmt.args.length - 1];
                if (last instanceof L.LeanCaret) {
                    return `%s${' '.repeat(this.indent)}`;
                }
            }
        }
        return '%s';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret === this.arg) {
            if (this.indent === indent) {
                if (caret instanceof L.LeanBy) {
                    const c2 = new L.LeanCaret(indent, caret.level);
                    const newNL = new L.LeanArgsNewLineSeparated([this.arg, c2], indent, c2.level);
                    const c = newNL.push_newlines(newline_count - 1);
                    this.arg = newNL;
                    return c;
                }
                if (next != ')')
                    // excluding next = ')' so that the parentheses can balance vertically
                    indent = this.indent + 2;
            }
            return this.push_args_indented(indent, newline_count, false);
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    insert_unary(caret, funcName) {
        if (caret !== this.arg) {
            throw new Error(`insert_unary is unexpected for ${this.constructor.name}`);
        }
        const {indent} = this;
        const Ctor = L[funcName];
        let caretOut;
        let newNode;
        if (caret instanceof L.LeanCaret) {
            newNode = new Ctor(caret, indent, caret.level);
            caretOut = caret;
        } else {
            const level = caret.level;
            caretOut = new L.LeanCaret(indent, level);
            newNode = new L.LeanArgsSpaceSeparated(
                [this.arg, new Ctor(caretOut, indent, level)],
                indent,
                level,
            );
        }
        this.arg = newNode;
        return caretOut;
    }

    is_indented() {
        const parent = this.parent;
        if (parent instanceof L.LeanColon && parent.parent instanceof L.LeanModule) {
            const rhs = parent.rhs;
            if (
                rhs instanceof L.LeanStatements &&
                rhs.args.length === 1 &&
                rhs.args[0] instanceof L.LeanLineComment &&
                rhs.args[0].text === 'imply'
            ) {
                const mod = parent.parent;
                const index = mod.args.indexOf(parent);
                const next = index >= 0 && index + 1 < mod.args.length ? mod.args[index + 1] : null;
                if (next instanceof L.Lean_let || next instanceof L.LeanQuantifier) {
                    return true;
                }
            }
        }
        if (parent instanceof L.LeanProperty) {
            const stmts = parent.parent;
            if (stmts instanceof L.LeanStatements) {
                const index = stmts.args.indexOf(parent);
                if (index > 0) {
                    const prev = stmts.args[index - 1];
                    if (prev instanceof L.LeanLineComment && prev.text === 'imply') {
                        return true;
                    }
                }
            }
        }
        if (parent instanceof L.LeanStatements && this.indent > 0) return true;
        // When LeanArgsIndented itself is indented, it prefixes the block — avoid double indent.
        if (parent instanceof L.LeanArgsIndented && this.indent > 0 && !parent.is_indented()) return true;
        if (leanParenthesisLemmaAssignByMultilineClose(this)) return true;
        if (parent instanceof L.LeanRelational && this.indent > parent.indent && parent.parent instanceof L.LeanArgsNewLineSeparated)
            return true;
        return parent instanceof L.LeanArgsNewLineSeparated || parent instanceof L.LeanArgsCommaNewLineSeparated || (parent instanceof L.LeanIte && !parent.inline && this !== parent.if);
    }

    isMatMulContext() {
        return this.parent != null && this.parent.isMatMulContext();
    }

    isProp(vars) {
        return this.arg.isProp(vars);
    }

    isProbEventParen() {
        const p = this.parent;
        return (
            p instanceof L.LeanArgsSpaceSeparated &&
            p.args.length >= 2 &&
            p.args[1] === this &&
            L.LeanArgsSpaceSeparated.isProbBinderHead(p.args[0])
        );
    }

    isExpectBodyParen() {
        const p = this.parent;
        return (
            p instanceof L.LeanArgsSpaceSeparated &&
            p.args.length >= 2 &&
            p.args[1] === this &&
            L.LeanArgsSpaceSeparated.isExpectBinderHead(p.args[0])
        );
    }

    /** `ℙ[…](…)` / `𝔼[…](…)`, also under a trailing projection: `ℙ[π](…).toReal`. */
    isProbExpectParen() {
        if (this.isProbEventParen() || this.isExpectBodyParen()) return true;
        const {LeanProperty, LeanArgsSpaceSeparated} = L;
        const p = this.parent;
        if (!(p instanceof LeanProperty) || p.args[0] !== this) return false;
        const pp = p.parent;
        return (
            pp instanceof LeanArgsSpaceSeparated &&
            pp.args.length >= 2 &&
            pp.args[1] === p &&
            (LeanArgsSpaceSeparated.isProbBinderHead(pp.args[0]) || LeanArgsSpaceSeparated.isExpectBinderHead(pp.args[0]))
        );
    }

    /** Rendered as `\left(…\right)` (not elided / not a multi-row block), so a `\middle` may sit inside. */
    isLatexStretchy() {
        return this.latexFormat() === this.toColor();
    }

    /**
     * The conditioning `|` directly inside these parentheses: `𝔼[…](body | cond)`, `𝔼[…](body | y, z)`,
     * `ℙ[…](x = a | y = b)` or `(X ⟂ᵢ Y | Z)`. Returns the `LeanBitOr`, or null when the parentheses do not
     * stretch (then the bar stays a plain `|`). Set-builder / match / abs bars never reach here.
     */
    conditioningBar() {
        const {LeanBitOr, LeanArgsCommaSeparated, Lean_perp} = L;
        const {arg} = this;
        const probExpect = this.isProbExpectParen();
        const bar =
            arg instanceof LeanBitOr ? arg
            : probExpect && arg instanceof LeanArgsCommaSeparated && arg.args[0] instanceof LeanBitOr ? arg.args[0]
            : null;
        if (!bar || !(probExpect || Lean_perp.independenceOf(bar.lhs))) return null;
        return this.isLatexStretchy() ? bar : null;
    }

    /**
     * `\middle|` must be at the same group level as its `\left(` / `\right)` (KaTeX: "\middle without
     * preceding \left" otherwise), so the bar is emitted directly in the paren body, not inside the
     * `{…}` group of `LeanBitOr` / `LeanArgsCommaSeparated`: `\left({body} \,\middle|\, {cond}, {…}\right)`.
     */
    conditioningLatex(syntax) {
        const bar = this.conditioningBar();
        if (!bar) return null;
        const [lhs, rhs] = bar.latexArgs(syntax);
        const rest = bar === this.arg ? [] : this.arg.args.slice(1).map((a) => `{${a.toLatex(syntax)}}`);
        return [[`{${lhs}} ${LeanParenthesis.middleBar} {${rhs}}`, ...rest].join(', ')];
    }

    static middleBar = '\\,\\middle|\\,';

    latexArgs(syntax) {
        const arg = this.arg;
        // the RV-only `ℙ`/`𝔼` forms below put `\mid` straight into the paren body: stretch it there too
        const mid = () => (this.isLatexStretchy() ? LeanParenthesis.middleBar : '\\mid');
        if (this.isProbEventParen()) {
            const rvs = L.LeanArgsSpaceSeparated.collectProbEventRVs(arg);
            if (rvs) return [rvs.map((t) => t.toLatex(syntax)).join(', ')];
            const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
            const body = peel(arg);
            if (body instanceof L.LeanBitOr) {
                const left = L.LeanArgsSpaceSeparated.collectProbEventRVs(body.lhs);
                const right = L.LeanArgsSpaceSeparated.collectProbEventRVs(body.rhs);
                if (left && right) {
                    const lhsLatex = left.map((t) => t.toLatex(syntax)).join(', ');
                    const R = right.map((t) => t.toLatex(syntax)).join(', ');
                    return [`${lhsLatex} ${mid()} ${R}`];
                }
            }
        }
        if (this.isExpectBodyParen()) {
            const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
            const body = peel(arg);
            if (body instanceof L.LeanBitOr) {
                const right = L.LeanArgsSpaceSeparated.collectProbEventRVs(body.rhs);
                if (right) {
                    const R = right.map((t) => t.toLatex(syntax)).join(', ');
                    return [`${body.lhs.toLatex(syntax)} ${mid()} ${R}`];
                }
            }
        }
        const conditioning = this.conditioningLatex(syntax);
        if (conditioning) return conditioning;
        if (arg.matrixLatexSpec())
            return [arg.toLatex(syntax)];
        if (arg instanceof L.LeanColon) {
            if (arg.lhs instanceof LeanBrace) return arg.lhs.latexArgs(syntax) ?? [arg.lhs.toLatex(syntax)];
            if (arg.rhs instanceof L.LeanToken && arg.rhs.text === 'Bool') return [arg.lhs.toLatex(syntax)];
            if (arg.isZeroOneTensor()) return [arg.toLatex(syntax)];
            if (this.isLatexArgAscription()) return [arg.lhs.toLatex(syntax)];
        }
        if (this.isLatexGetElemOperand())
            return [arg.toLatex(syntax)];
        if (this.isLatexRedundantPrecedence())
            return [arg.toLatex(syntax)];
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const arg = this.arg;
        if (arg.matrixLatexSpec())
            return '%s';
        if (arg instanceof L.LeanColon) {
            if (arg.lhs instanceof LeanBrace) return arg.lhs.latexFormat() ?? '%s';
            if (arg.rhs instanceof L.LeanToken && arg.rhs.text === 'Bool') return '\\left|{%s}\\right|';
            if (arg.isZeroOneTensor()) return '%s';
            if (this.isLatexArgAscription()) return '%s';
        }
        if (this.isLatexGetElemOperand())
            return '%s';
        if (this.isLatexRedundantPrecedence())
            return '%s';
        if (String(arg).includes('\n') && !(arg instanceof L.LeanArgsIndented && arg.isMultilineApplication()))
            // Multi-row content (e.g. `(by …)` tactic block rendering as `align*`):
            // `\mathord{\left(...\right)}` would stretch to the full block height.
            return '%s';
        return this.toColor();
    }

    /**
     * Parentheses only needed for Lean parsing (e.g. `(γ ^ id) @ r[t:]`): the inner operator
     * binds tighter than the surrounding one, so LaTeX can drop the parens (`γ^{id} × r_{t:}`).
     */
    isLatexRedundantPrecedence() {
        const p = this.parent;
        if (!(p instanceof L.LeanArithmetic)) return false;
        const arg = this.arg;
        if (!(arg instanceof L.LeanArithmetic)) return false;
        const childPri = arg.constructor.input_priority ?? 0;
        const parentPri = p.constructor.input_priority ?? 0;
        return childPri > parentPri;
    }

    /** Parenthesized GetElem base/index: `(e)[i]` → `e_i`, not `(e)_i`. */
    isLatexGetElemOperand() {
        const p = this.parent;
        if (!(
            p instanceof L.LeanGetElem ||
            p instanceof L.LeanGetElemQue ||
            p instanceof L.LeanGetElemQuote
        )) return false;
        // Base of `(f x)[i]` / `(a + b)[i]`: dropping the parens would read as `f x_i`.
        if (p.args[0] === this) {
            const arg = this.arg;
            return (
                arg instanceof L.LeanToken ||
                arg instanceof L.LeanProperty ||
                arg instanceof LeanPairedGroup ||
                arg instanceof L.LeanGetElem ||
                arg instanceof L.LeanGetElemQue ||
                arg instanceof L.LeanGetElemQuote
            );
        }
        return true;
    }

    isLatexArgAscription() {
        const arg = this.arg;
        if (!(arg instanceof L.LeanColon)) return false;
        if (arg.isZeroOneTensor()) return false;
        if (arg.lhs instanceof LeanBrace) return false;
        if (arg.rhs instanceof L.LeanToken && arg.rhs.text === 'Bool') return false;
        const p = this.parent;
        // Binder of a lambda (`fun s (_ : Iic 0) => s`): the type is part of the binder.
        if (
            p instanceof L.LeanArgsSpaceSeparated &&
            (p.parent instanceof L.LeanRightarrow || p.parent instanceof L.Lean_mapsto) &&
            p.parent.lhs === p && p.parent.parent instanceof L.Lean_fun
        ) return false;
        // Only elide simple casts like `(n : ℝ)`; a structured type such as
        // `(μ : Measure (ℕ → S))` carries information the reader needs.
        if (!(arg.rhs instanceof L.LeanToken)) return false;
        return (
            p instanceof L.LeanArgsSpaceSeparated ||
            p instanceof L.LeanArgsCommaSeparated ||
            p instanceof L.LeanGetElem ||
            p instanceof L.LeanGetElemQue ||
            p instanceof L.LeanGetElemQuote ||
            p instanceof L.LeanRelational
        );
    }

    peelLatexCoe() {
        const inner = this.arg.peelLatexCoe();
        if (inner !== this.arg) return inner;
        return this;
    }

    peelParen() {
        if (this.arg instanceof L.LeanColon) return this;
        return this.arg.peelParen();
    }

    peelGroup() {
        return this.arg.peelGroup();
    }

    regexp() {
        return this.arg.regexp();
    }

    /**
     * `LeanArgsIndented` under `LeanStatements` prepends its indent only to this node's line; multiline
     * `arg` (e.g. `by` / tactic block) keeps smaller absolute indents, so the next parse sees a dedent
     * before `(` closes and drops the proof body. Pad continuation lines by the parent indent.
     */
    strArgs() {
        const arg = this.arg;
        if (this.is_indented() && this.parent instanceof L.LeanArgsIndented && this.parent.indent > 0) {
            const s = String(arg);
            if (s.includes('\n')) {
                const pad = this.parent.indent;
                const lines = s.split('\n');
                const bumped = lines.map((line, i) => {
                    if (i === 0 || line === '') return line;
                    return ' '.repeat(pad) + line;
                });
                return [bumped.join('\n')];
            }
        }
        if (leanParenthesisLemmaAssignByMultilineClose(this)) {
            return [String(arg).replace(/\n+$/, '')];
        }
        return [arg];
    }

    strFormat() {
        if (leanParenthesisLemmaAssignByMultilineClose(this)) {
            const asn = this.parent;
            const pad = ' '.repeat((asn.indent ?? 0) + 2);
            return super.strFormat(`%s\n${pad}`);
        }
        return super.strFormat();
    }

    toColor() {
        let n = (this.arg.level ?? 0) & 7;
        const b = '9f'[n & 1];
        n >>= 1;
        const g = '9f'[n & 1];
        n >>= 1;
        const r = '9f'[n & 1];
        return `\\colorbox{#${r}${g}${b}}{$\\mathord{\\left(%s\\right)}$}`;
    }
}

export class LeanAngleBracket extends LeanPairedGroup {
    static { this.register(); }

    get stack_priority() {
        return 10;
    }
    get operator() {
        return ['⟨', '⟩'];
    }

    is_indented() {
        const p = this.parent;
        return !(p instanceof L.Lean_mapsto || 
            p instanceof L.LeanAssign || 
            p instanceof L.LeanTactic || 
            p instanceof L.LeanArgsSpaceSeparated || 
            p instanceof L.LeanRelational || 
            p instanceof L.LeanRightarrow || 
            p instanceof L.LeanColon || 
            p instanceof L.LeanArgsCommaSeparated ||
            p instanceof L.LeanBitOr | 
            p instanceof L.LeanWith ||
            p instanceof LeanAngleBracket
        );
    }

    latexFormat() {
        return '\\langle {%s} \\rangle';
    }

    push_token(word) {
        const level = this.level;
        const newTok = new L.LeanToken(word, this.indent, level);
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    strArgs() {
        return [this.arg];
    }

    tokens_comma_separated() {
        const a = this.arg;
        if (a instanceof L.LeanArgsCommaSeparated) return a.tokens_comma_separated();
        return [a];
    }
}

/**
 * Square brackets. Declaration order matches the reference `LeanBracket` class: virtual `stack_priority` /
 * `operator`, `is_Expr`, `latexFormat`, `push_right`, `strArgs`. `toString` is a JS-only indent tweak when the
 * parent is `LeanModule` (no separate method in the reference class).
 */
export class LeanBracket extends LeanPairedGroup {
    static { this.register(); }

    is_Expr() {
        return false;
    }

    latexFormat() {
        return '\\left[ {%s} \\right]';
    }

    get operator() {
        return '[]';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent && caret === this.arg) {
            if (this.indent === indent) {
                if (next != ']')
                    indent = this.indent + 2;
            }
            return this.push_args_indented(indent, newline_count, false);
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    push_right(funcName) {
        if (funcName === this.constructor.name) {
            let lt = null;
            const {arg} = this;
            if (arg instanceof L.Lean_lt && arg.lhs instanceof L.LeanToken)
                lt = arg;
            else if (arg instanceof L.LeanArgsSpaceSeparated) {
                const siblings = arg.args.filter((x) => !(x instanceof L.LeanCaret));
                if (siblings.length === 1 && siblings[0] instanceof L.Lean_lt && siblings[0].lhs instanceof L.LeanToken)
                    lt = siblings[0];
            }
            if (lt) {
                // Tensor index `[i < m]`: final tree is LeanStack(Lean_lt, scope), not bracket + wrapper.
                this.arg = lt;
                lt.parent = this;
                const {level} = this;
                const stack = new L.LeanStack(lt, this.indent, level);
                const scope = new L.LeanCaret(this.indent, level);
                stack.scope = scope;
                this.parent.replace(this, stack);
                return scope;
            }
            const lim = this.parent;
            if (lim instanceof L.Lean_lim && lim.bound === this && !lim.scope) {
                lim.bound = this.arg;
                const scope = new L.LeanCaret(this.indent, this.level);
                lim.scope = scope;
                return scope;
            }
        }
        return super.push_right(funcName);
    }

    /** Like `LeanAngleBracket.push_token`: after `]` the caret is this node; splice a following identifier (e.g. `[i] X[i]'`). */
    push_token(word) {
        const level = this.level;
        const newTok = new L.LeanToken(word, this.indent, level);
        const pow = this.parent;
        if (pow instanceof L.LeanPow && pow.rhs === this) {
            const grandparent = pow.parent;
            const wrapper = new L.LeanArgsSpaceSeparated([pow, newTok], this.indent, level);
            grandparent.replace(pow, wrapper);
            return newTok;
        }
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    get stack_priority() {
        return 17;
    }

    strArgs() {
        return [this.arg];
    }
}

export class LeanBrace extends LeanPairedGroup {
    static { this.register(); }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent <= indent) {
            if (caret instanceof L.LeanCaret) {
                if (indent === this.indent) {
                    indent = this.indent + 2;
                }
                caret.indent = indent;
                this.arg = new L.LeanStatements([caret], indent, caret.level);
                return caret;
            }
            if (indent > this.indent) {
                const newIndent = this.indent + 2;
                const current = this.arg;
                let stmts;
                if (current instanceof L.LeanStatements) {
                    stmts = current;
                } else {
                    current.indent = newIndent;
                    stmts = new L.LeanStatements([current], newIndent, current.level ?? this.level);
                    this.arg = stmts;
                }
                const out = new L.LeanCaret(newIndent, stmts.level);
                stmts.push(out);
                for (let i = 1; i < newline_count; i++)
                    stmts.push(new L.LeanCaret(newIndent, stmts.level));
                return out;
            }
            if (indent === this.indent) return caret;
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_Expr() {
        return false;
    }

    is_indented() {
        const p = this.parent;
        return !(p instanceof L.LeanQuantifier || 
            p instanceof L.LeanBinaryBoolean || 
            p instanceof L.LeanColon || 
            p instanceof L.LeanSetOperator || 
            p instanceof L.LeanTactic || 
            p instanceof L.LeanAssign || 
            p instanceof L.Lean_rightarrow || 
            p instanceof L.LeanArgsSpaceSeparated
        );
    }

    latexFormat() {
        return '\\left\\{ {%s} \\right\\}';
    }

    get operator() {
        return '{}';
    }

    get stack_priority() {
        return 17;
    }
}

export class LeanAbs extends LeanPairedGroup {
    static { this.register(); }

    get operator() {
        return '||';
    }
    get stack_priority() {
        return 17;
    }
    insert_bar(caret, prevToken, next) {
        return this.push_right('LeanAbs');
    }
    latexFormat() {
        return '\\left| {%s} \\right|';
    }
}

export class LeanNorm extends LeanPairedGroup {
    static { this.register(); }

    get stack_priority() {
        return 17;
    }
    get operator() {
        return ['‖', '‖'];
    }
    latexFormat() {
        return '\\left\\lVert {%s} \\right\\rVert';
    }
}

/** Inner product `⟪x, y⟫` (Mathlib `inner` notation). */
export class LeanInner extends LeanPairedGroup {
    static { this.register(); }

    static input_priority = 72;
    get stack_priority() {
        return 10;
    }
    get operator() {
        return ['⟪', '⟫' + (this.field ?? '')];
    }
    latexFormat() {
        return '\\left\\langle {%s} \\right\\rangle';
    }
}

export class LeanCeil extends LeanPairedGroup {
    static { this.register(); }

    static input_priority = 72;
    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['⌈', this.nat ? '⌉₊' : '⌉'];
    }
    latexFormat() {
        return this.nat ? '\\left\\lceil {%s} \\right\\rceil_{+}' : '\\left\\lceil {%s} \\right\\rceil';
    }
}

export class LeanFloor extends LeanPairedGroup {
    static { this.register(); }

    static input_priority = 72;
    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['⌊', this.nat ? '⌋₊' : '⌋'];
    }
    latexFormat() {
        return this.nat ? '\\left\\lfloor {%s} \\right\\rfloor_{+}' : '\\left\\lfloor {%s} \\right\\rfloor';
    }
}

export class LeanWhiteSquareBracket extends LeanPairedGroup {
    static { this.register(); }

    static input_priority = 72;
    get stack_priority() {
        return 17;
    }
    get operator() {
        return ['⟦', '⟧'];
    }
    latexFormat() {
        return '\\left\\llbracket {%s} \\right\\rrbracket';
    }
}

export class LeanDoubleAngleQuotation extends LeanPairedGroup {
    static { this.register(); }

    is_Expr() {
        return false;
    }

    /** `«y.bvar»` is a term-level node — never add its own indentation. */
    is_indented() {
        return false;
    }

    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['«', '»'];
    }
    boundValueLhs() {
        const inner = this.arg;
        if (
            inner instanceof L.LeanProperty &&
            inner.rhs instanceof L.LeanToken &&
            inner.rhs.text === 'bvar'
        ) {
            return inner.lhs;
        }
        return null;
    }
    latexFormat() {
        return this.boundValueLhs() ? '%s' : '{\\color{red}%s}';
    }
    latexArgs(syntax) {
        const lhs = this.boundValueLhs();
        return lhs ? [lhs.toLatex(syntax)] : super.latexArgs(syntax);
    }
}

/** Lean `‹p›` assumption term (look up a local of type `p`). */
export class LeanSingleAngleQuotation extends LeanPairedGroup {
    static { this.register(); }

    get stack_priority() {
        return 10;
    }
    get operator() {
        return ['‹', '›'];
    }
    latexFormat() {
        return '\\text{‹}{%s}\\text{›}';
    }
}
