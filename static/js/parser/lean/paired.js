import { Closable } from '../node.js';

/**
 * Paired delimiters: `LeanPairedGroup` and parenthesis, bracket, brace, abs,
 * norm, inner, ceil, floor, white square bracket, and angle quotations.
 *
 * `LeanUnary` stays in `lean.js`. This factory runs after that base exists.
 * Arithmetic classes are consulted only from methods (`instanceof`), and they
 * are registered on `arithmeticLate` after `createArithmeticFamily` returns.
 *
 * @param {object} deps
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.arithmeticLate
 */
export function createPairedFamily(deps) {
    const {
        LeanUnary,
        LeanArgsCommaNewLineSeparated,
        LeanArgsCommaSeparated,
        LeanArgsIndented,
        LeanArgsNewLineSeparated,
        LeanArgsSemicolonSeparated,
        LeanArgsSpaceSeparated,
        LeanAssign,
        LeanBigOperator,
        LeanBinaryBoolean,
        LeanBy,
        LeanCaret,
        LeanColon,
        LeanGetElem,
        LeanGetElemQue,
        LeanGetElemQuote,
        LeanIte,
        LeanLineComment,
        LeanModule,
        LeanProperty,
        LeanQuantifier,
        LeanRelational,
        LeanRightarrow,
        LeanSetOperator,
        LeanStack,
        LeanStatements,
        LeanTactic,
        LeanToken,
        LeanWith,
        Lean_fun,
        Lean_let,
        Lean_lim,
        Lean_lt,
        Lean_mapsto,
        Lean_rightarrow,
        classRegistry,
        arithmeticLate,
    } = deps;
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before paired registration');
            return map[key];
        },
    });
    function lateClass(name) {
        function Ctor() {}
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = arithmeticLate[name];
                if (real == null) throw new Error(`${name} used before arithmetic registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanArithmetic = lateClass('LeanArithmetic');
    const LeanBitOr = lateClass('LeanBitOr');
    const LeanPow = lateClass('LeanPow');
    const LeanUnaryArithmeticPost = lateClass('LeanUnaryArithmeticPost');
    const LeanUnaryArithmeticPre = lateClass('LeanUnaryArithmeticPre');

    /**
     * Abstract paired delimiters. Uses `Closable(LeanUnary)` like `MarkdownLink extends Closable(MarkdownArgs)` in `markdown.js`.
     */
    class LeanPairedGroup extends Closable(LeanUnary) {
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
                if (caret instanceof LeanCaret) {
                    const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                    this.arg = new Ctor(caret, this.indent, caret.level);
                    return caret;
                }
                if (caret instanceof LeanToken) {
                    const $new = new LeanCaret(this.indent, caret.level);
                    const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                    this.arg = new LeanArgsSpaceSeparated([this.arg, new Ctor($new, this.indent, caret.level)], this.indent, caret.level);
                    return $new;
                }
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_comma(caret) {
            caret = new LeanCaret(this.indent, caret.level);
            const a = this.arg;
            if (a instanceof LeanArgsCommaSeparated) {
                a.push(caret);
            } else {
                this.arg = new LeanArgsCommaSeparated([a, caret], this.indent, caret.level);
            }
            return caret;
        }

        insert_semicolon(caret) {
            caret = new LeanCaret(this.indent, caret.level);
            const a = this.arg;
            if (a instanceof LeanArgsSemicolonSeparated) {
                a.push(caret);
            } else {
                this.arg = new LeanArgsSemicolonSeparated([a, caret], this.indent, caret.level);
            }
            return caret;
        }

        insert_if(caret) {
            if (this.arg === caret && caret instanceof LeanCaret) {
                this.arg = new LeanIte([caret], caret.indent, caret.level);
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
                if (caret instanceof LeanCaret) {
                    if (indent === this.indent) indent = this.indent + 2;
                    caret.indent = indent;
                    if (this instanceof LeanBrace) {
                        this.arg = new LeanStatements([caret], indent, caret.level);
                        return caret;
                    }
                    this.arg = new LeanArgsCommaNewLineSeparated(
                        [new LeanArgsCommaSeparated([caret], indent, caret.level)],
                        indent,
                        caret.level,
                    );
                    return caret;
                }
                if (indent === this.indent) return caret;
                if (indent > this.indent) {
                    if (caret instanceof LeanArgsSpaceSeparated) {
                        return this.push_args_indented(indent, newline_count, false);
                    }
                }
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_tactic(caret, token) {
            if (caret instanceof LeanCaret) return this.insert_word(caret, token);
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
            const caret = new LeanCaret(indent, level);
            if (typeof $new === 'string') {
                const Ctor = LEAN_CLASSES[$new];
                const node = new Ctor(caret, indent, level);
                if (this.parent instanceof LeanArgsSpaceSeparated) {
                    this.parent.push(node);
                } else {
                    // Wrap the closed group itself (not its contents): `(a _) fun t => ?_` must not become `(a _ fun t => ?_)`.
                    this.parent.replace(this, new LeanArgsSpaceSeparated([this, node], indent, level));
                }
                return caret;
            }
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, $new], indent, level));
            return $new;
        }

        is_indented() {
            const parent = this.parent;
            return !(
                parent instanceof LeanTactic ||
                parent instanceof LeanArgsCommaSeparated ||
                parent instanceof LeanAssign ||
                parent instanceof LeanArgsSpaceSeparated ||
                parent instanceof LeanBinaryBoolean ||
                parent instanceof LeanRightarrow ||
                parent instanceof LeanUnaryArithmeticPre ||
                parent instanceof LeanArithmetic ||
                parent instanceof LeanProperty ||
                parent instanceof LeanColon ||
                parent instanceof LeanUnaryArithmeticPost ||
                parent instanceof LeanPairedGroup ||
                parent instanceof LeanBigOperator ||
                parent instanceof LeanGetElem ||
                parent instanceof LeanGetElemQue ||
                parent instanceof LeanGetElemQuote
            );
        }

        /** @param {string} funcName e.g. 'LeanParenthesis' */
        push_right(funcName) {
            if (this.constructor.name === funcName) {
                this.is_closed = true;
                // `a[i]'(proof)` is a complete term; stay on the get-elem so `*`, `.`, `[` bind outside the proof.
                if (this.parent instanceof LeanGetElemQuote && this.parent.args[2] === this)
                    return this.parent;
                return this;
            }
            if (this.parent) return this.parent.push_right(funcName);
        }

        set_line(line) {
            this.line = line;
            const arg = this.arg;
            const hasNewline = arg instanceof LeanStatements;
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
            asn instanceof LeanAssign &&
            asn.parent instanceof LeanModule &&
            asn.rhs instanceof LeanBy &&
            (asn.indent ?? 0) > 0 &&
            String(paren.arg).includes('\n')
        );
    }

    /** Parentheses: inner `level` for rainbow LaTeX. Method order follows the reference `LeanParenthesis` class. */
    class LeanParenthesis extends LeanPairedGroup {
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
            if (arg instanceof LeanBy) {
                const stmt = arg.arg;
                if (stmt instanceof LeanStatements) {
                    const last = stmt.args[stmt.args.length - 1];
                    if (last instanceof LeanCaret) {
                        return `%s${' '.repeat(this.indent)}`;
                    }
                }
            }
            return '%s';
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent && caret === this.arg) {
                if (this.indent === indent) {
                    if (caret instanceof LeanBy) {
                        const c2 = new LeanCaret(indent, caret.level);
                        const newNL = new LeanArgsNewLineSeparated([this.arg, c2], indent, c2.level);
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
            const Ctor = LEAN_CLASSES[funcName];
            let caretOut;
            let newNode;
            if (caret instanceof LeanCaret) {
                newNode = new Ctor(caret, indent, caret.level);
                caretOut = caret;
            } else {
                const level = caret.level;
                caretOut = new LeanCaret(indent, level);
                newNode = new LeanArgsSpaceSeparated(
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
            if (parent instanceof LeanColon && parent.parent instanceof LeanModule) {
                const rhs = parent.rhs;
                if (
                    rhs instanceof LeanStatements &&
                    rhs.args.length === 1 &&
                    rhs.args[0] instanceof LeanLineComment &&
                    rhs.args[0].text === 'imply'
                ) {
                    const mod = parent.parent;
                    const index = mod.args.indexOf(parent);
                    const next = index >= 0 && index + 1 < mod.args.length ? mod.args[index + 1] : null;
                    if (next instanceof Lean_let || next instanceof LeanQuantifier) {
                        return true;
                    }
                }
            }
            if (parent instanceof LeanProperty) {
                const stmts = parent.parent;
                if (stmts instanceof LeanStatements) {
                    const index = stmts.args.indexOf(parent);
                    if (index > 0) {
                        const prev = stmts.args[index - 1];
                        if (prev instanceof LeanLineComment && prev.text === 'imply') {
                            return true;
                        }
                    }
                }
            }
            if (parent instanceof LeanStatements && this.indent > 0) return true;
            // When LeanArgsIndented itself is indented, it prefixes the block — avoid double indent.
            if (parent instanceof LeanArgsIndented && this.indent > 0 && !parent.is_indented()) return true;
            if (leanParenthesisLemmaAssignByMultilineClose(this)) return true;
            if (parent instanceof LeanRelational && this.indent > parent.indent && parent.parent instanceof LeanArgsNewLineSeparated)
                return true;
            return parent instanceof LeanArgsNewLineSeparated || parent instanceof LeanArgsCommaNewLineSeparated || (parent instanceof LeanIte && !parent.inline && this !== parent.if);
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
                p instanceof LeanArgsSpaceSeparated &&
                p.args.length >= 2 &&
                p.args[1] === this &&
                LeanArgsSpaceSeparated.isProbBinderHead(p.args[0])
            );
        }

        isExpectBodyParen() {
            const p = this.parent;
            return (
                p instanceof LeanArgsSpaceSeparated &&
                p.args.length >= 2 &&
                p.args[1] === this &&
                LeanArgsSpaceSeparated.isExpectBinderHead(p.args[0])
            );
        }

        latexArgs(syntax) {
            const arg = this.arg;
            if (this.isProbEventParen()) {
                const rvs = LeanArgsSpaceSeparated.collectProbEventRVs(arg);
                if (rvs) return [rvs.map((t) => t.toLatex(syntax)).join(', ')];
                const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
                const body = peel(arg);
                if (body instanceof LeanBitOr) {
                    const left = LeanArgsSpaceSeparated.collectProbEventRVs(body.lhs);
                    const right = LeanArgsSpaceSeparated.collectProbEventRVs(body.rhs);
                    if (left && right) {
                        const L = left.map((t) => t.toLatex(syntax)).join(', ');
                        const R = right.map((t) => t.toLatex(syntax)).join(', ');
                        return [`${L} \\mid ${R}`];
                    }
                }
            }
            if (this.isExpectBodyParen()) {
                const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
                const body = peel(arg);
                if (body instanceof LeanBitOr) {
                    const right = LeanArgsSpaceSeparated.collectProbEventRVs(body.rhs);
                    if (right) {
                        const R = right.map((t) => t.toLatex(syntax)).join(', ');
                        return [`${body.lhs.toLatex(syntax)} \\mid ${R}`];
                    }
                }
            }
            if (arg.matrixLatexSpec())
                return [arg.toLatex(syntax)];
            if (arg instanceof LeanColon) {
                if (arg.lhs instanceof LeanBrace) return arg.lhs.latexArgs(syntax) ?? [arg.lhs.toLatex(syntax)];
                if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return [arg.lhs.toLatex(syntax)];
                if (arg.isZeroOneTensor()) return [arg.toLatex(syntax)];
                if (this.isLatexArgAscription()) return [arg.lhs.toLatex(syntax)];
            }
            if (this.isLatexGetElemOperand())
                return [arg.toLatex(syntax)];
            return super.latexArgs(syntax);
        }

        latexFormat() {
            const arg = this.arg;
            if (arg.matrixLatexSpec())
                return '%s';
            if (arg instanceof LeanColon) {
                if (arg.lhs instanceof LeanBrace) return arg.lhs.latexFormat() ?? '%s';
                if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return '\\left|{%s}\\right|';
                if (arg.isZeroOneTensor()) return '%s';
                if (this.isLatexArgAscription()) return '%s';
            }
            if (this.isLatexGetElemOperand())
                return '%s';
            if (String(arg).includes('\n') && !(arg instanceof LeanArgsIndented && arg.isMultilineApplication()))
                // Multi-row content (e.g. `(by …)` tactic block rendering as `align*`):
                // `\mathord{\left(...\right)}` would stretch to the full block height.
                return '%s';
            return this.toColor();
        }

        /** Parenthesized GetElem base/index: `(e)[i]` → `e_i`, not `(e)_i`. */
        isLatexGetElemOperand() {
            const p = this.parent;
            if (!(
                p instanceof LeanGetElem ||
                p instanceof LeanGetElemQue ||
                p instanceof LeanGetElemQuote
            )) return false;
            // Base of `(f x)[i]` / `(a + b)[i]`: dropping the parens would read as `f x_i`.
            if (p.args[0] === this) {
                const arg = this.arg;
                return (
                    arg instanceof LeanToken ||
                    arg instanceof LeanProperty ||
                    arg instanceof LeanPairedGroup ||
                    arg instanceof LeanGetElem ||
                    arg instanceof LeanGetElemQue ||
                    arg instanceof LeanGetElemQuote
                );
            }
            return true;
        }

        isLatexArgAscription() {
            const arg = this.arg;
            if (!(arg instanceof LeanColon)) return false;
            if (arg.isZeroOneTensor()) return false;
            if (arg.lhs instanceof LeanBrace) return false;
            if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return false;
            const p = this.parent;
            // Binder of a lambda (`fun s (_ : Iic 0) => s`): the type is part of the binder.
            if (
                p instanceof LeanArgsSpaceSeparated &&
                (p.parent instanceof LeanRightarrow || p.parent instanceof Lean_mapsto) &&
                p.parent.lhs === p && p.parent.parent instanceof Lean_fun
            ) return false;
            // Only elide simple casts like `(n : ℝ)`; a structured type such as
            // `(μ : Measure (ℕ → S))` carries information the reader needs.
            if (!(arg.rhs instanceof LeanToken)) return false;
            return (
                p instanceof LeanArgsSpaceSeparated ||
                p instanceof LeanArgsCommaSeparated ||
                p instanceof LeanGetElem ||
                p instanceof LeanGetElemQue ||
                p instanceof LeanGetElemQuote ||
                p instanceof LeanRelational
            );
        }

        peelLatexCoe() {
            const inner = this.arg.peelLatexCoe();
            if (inner !== this.arg) return inner;
            return this;
        }

        peelParen() {
            if (this.arg instanceof LeanColon) return this;
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
            if (this.is_indented() && this.parent instanceof LeanArgsIndented && this.parent.indent > 0) {
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

    class LeanAngleBracket extends LeanPairedGroup {
        get stack_priority() {
            return 10;
        }
        get operator() {
            return ['⟨', '⟩'];
        }

        is_indented() {
            const p = this.parent;
            return !(p instanceof Lean_mapsto || 
                p instanceof LeanAssign || 
                p instanceof LeanTactic || 
                p instanceof LeanArgsSpaceSeparated || 
                p instanceof LeanRelational || 
                p instanceof LeanRightarrow || 
                p instanceof LeanColon || 
                p instanceof LeanArgsCommaSeparated ||
                p instanceof LeanBitOr | 
                p instanceof LeanWith ||
                p instanceof LeanAngleBracket
            );
        }

        latexFormat() {
            return '\\langle {%s} \\rangle';
        }

        push_token(word) {
            const level = this.level;
            const newTok = new LeanToken(word, this.indent, level);
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
            return newTok;
        }

        strArgs() {
            return [this.arg];
        }

        tokens_comma_separated() {
            const a = this.arg;
            if (a instanceof LeanArgsCommaSeparated) return a.tokens_comma_separated();
            return [a];
        }
    }

    /**
     * Square brackets. Declaration order matches the reference `LeanBracket` class: virtual `stack_priority` /
     * `operator`, `is_Expr`, `latexFormat`, `push_right`, `strArgs`. `toString` is a JS-only indent tweak when the
     * parent is `LeanModule` (no separate method in the reference class).
     */
    class LeanBracket extends LeanPairedGroup {
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
                if (arg instanceof Lean_lt && arg.lhs instanceof LeanToken)
                    lt = arg;
                else if (arg instanceof LeanArgsSpaceSeparated) {
                    const siblings = arg.args.filter((x) => !(x instanceof LeanCaret));
                    if (siblings.length === 1 && siblings[0] instanceof Lean_lt && siblings[0].lhs instanceof LeanToken)
                        lt = siblings[0];
                }
                if (lt) {
                    // Tensor index `[i < m]`: final tree is LeanStack(Lean_lt, scope), not bracket + wrapper.
                    this.arg = lt;
                    lt.parent = this;
                    const {level} = this;
                    const stack = new LeanStack(lt, this.indent, level);
                    const scope = new LeanCaret(this.indent, level);
                    stack.scope = scope;
                    this.parent.replace(this, stack);
                    return scope;
                }
                const lim = this.parent;
                if (lim instanceof Lean_lim && lim.bound === this && !lim.scope) {
                    lim.bound = this.arg;
                    const scope = new LeanCaret(this.indent, this.level);
                    lim.scope = scope;
                    return scope;
                }
            }
            return super.push_right(funcName);
        }

        /** Like `LeanAngleBracket.push_token`: after `]` the caret is this node; splice a following identifier (e.g. `[i] X[i]'`). */
        push_token(word) {
            const level = this.level;
            const newTok = new LeanToken(word, this.indent, level);
            const pow = this.parent;
            if (pow instanceof LeanPow && pow.rhs === this) {
                const grandparent = pow.parent;
                const wrapper = new LeanArgsSpaceSeparated([pow, newTok], this.indent, level);
                grandparent.replace(pow, wrapper);
                return newTok;
            }
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
            return newTok;
        }

        get stack_priority() {
            return 17;
        }

        strArgs() {
            return [this.arg];
        }
    }

    class LeanBrace extends LeanPairedGroup {
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent <= indent) {
                if (caret instanceof LeanCaret) {
                    if (indent === this.indent) {
                        indent = this.indent + 2;
                    }
                    caret.indent = indent;
                    this.arg = new LeanStatements([caret], indent, caret.level);
                    return caret;
                }
                if (indent > this.indent) {
                    const newIndent = this.indent + 2;
                    const current = this.arg;
                    let stmts;
                    if (current instanceof LeanStatements) {
                        stmts = current;
                    } else {
                        current.indent = newIndent;
                        stmts = new LeanStatements([current], newIndent, current.level ?? this.level);
                        this.arg = stmts;
                    }
                    const out = new LeanCaret(newIndent, stmts.level);
                    stmts.push(out);
                    for (let i = 1; i < newline_count; i++)
                        stmts.push(new LeanCaret(newIndent, stmts.level));
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
            return !(p instanceof LeanQuantifier || 
                p instanceof LeanBinaryBoolean || 
                p instanceof LeanColon || 
                p instanceof LeanSetOperator || 
                p instanceof LeanTactic || 
                p instanceof LeanAssign || 
                p instanceof Lean_rightarrow || 
                p instanceof LeanArgsSpaceSeparated
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

    class LeanAbs extends LeanPairedGroup {
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

    class LeanNorm extends LeanPairedGroup {
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
    class LeanInner extends LeanPairedGroup {
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

    class LeanCeil extends LeanPairedGroup {
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

    class LeanFloor extends LeanPairedGroup {
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

    class LeanWhiteSquareBracket extends LeanPairedGroup {
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

    class LeanDoubleAngleQuotation extends LeanPairedGroup {
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
                inner instanceof LeanProperty &&
                inner.rhs instanceof LeanToken &&
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
    class LeanSingleAngleQuotation extends LeanPairedGroup {
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

    return {
        LeanPairedGroup,
        LeanParenthesis,
        LeanAngleBracket,
        LeanBracket,
        LeanBrace,
        LeanAbs,
        LeanNorm,
        LeanInner,
        LeanCeil,
        LeanFloor,
        LeanWhiteSquareBracket,
        LeanDoubleAngleQuotation,
        LeanSingleAngleQuotation,
    };
}
