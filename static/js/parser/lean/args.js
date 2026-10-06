/**
 * Argument lists: space-, newline-, indented, comma-, semicolon-, and
 * comma-newline-separated (`LeanArgsSpaceSeparated` and the classes that
 * follow it up to `LeanSyntax`).
 *
 * `LeanArgs`, `LeanBinary`, `LeanMultipleLine`, and the classes already
 * declared above this factory stay in `lean.js` and are passed in.
 * `leanEvalPrefix` / `leanVarsGetitem` stay in `lean.js` as well.
 * Classes created later (`LeanTactic`, paired delimiters, arithmetic,
 * quantifiers, big operators, and the rest) are filled on `argsLate`;
 * methods only use them via `instanceof` or `new`. `LEAN_CLASSES` is the
 * shared registry filled after this returns. This factory does not import
 * `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanArgs
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanMultipleLine
 * @param {Function} deps.LeanAssign
 * @param {Function} deps.LeanBar
 * @param {Function} deps.LeanBinaryBoolean
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanColon
 * @param {Function} deps.LeanEq
 * @param {Function} deps.LeanGetElem
 * @param {Function} deps.LeanGetElemQue
 * @param {Function} deps.LeanGetElemQuote
 * @param {Function} deps.LeanIte
 * @param {Function} deps.LeanLogic
 * @param {Function} deps.LeanProperty
 * @param {Function} deps.LeanRelational
 * @param {Function} deps.LeanRightarrow
 * @param {Function} deps.LeanStatements
 * @param {Function} deps.LeanToken
 * @param {Function} deps.Lean_land
 * @param {Function} deps.Lean_mapsto
 * @param {Function} deps.leanEvalPrefix
 * @param {Function} deps.leanVarsGetitem
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.argsLate
 */
export function createArgsFamily(deps) {
    const {
        LeanArgs,
        LeanBinary,
        LeanMultipleLine,
        LeanAssign,
        LeanBar,
        LeanBinaryBoolean,
        LeanCaret,
        LeanColon,
        LeanEq,
        LeanGetElem,
        LeanGetElemQue,
        LeanGetElemQuote,
        LeanIte,
        LeanLogic,
        LeanProperty,
        LeanRelational,
        LeanRightarrow,
        LeanStatements,
        LeanToken,
        Lean_land,
        Lean_mapsto,
        leanEvalPrefix,
        leanVarsGetitem,
        classRegistry,
        argsLate,
    } = deps;

    function lateCtor(name) {
        function Ctor(...args) {
            const real = argsLate[name];
            if (real == null) throw new Error(`${name} used before args registration`);
            return new real(...args);
        }
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = argsLate[name];
                if (real == null) throw new Error(`${name} used before args registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const LeanAngleBracket = lateCtor('LeanAngleBracket');
    const LeanAppend = lateCtor('LeanAppend');
    const LeanBitOr = lateCtor('LeanBitOr');
    const LeanBracket = lateCtor('LeanBracket');
    const LeanBy = lateCtor('LeanBy');
    const LeanCalc = lateCtor('LeanCalc');
    const LeanDiv = lateCtor('LeanDiv');
    const LeanDoubleAngleQuotation = lateCtor('LeanDoubleAngleQuotation');
    const LeanParenthesis = lateCtor('LeanParenthesis');
    const LeanPreimage = lateCtor('LeanPreimage');
    const LeanQuantifier = lateCtor('LeanQuantifier');
    const LeanStack = lateCtor('LeanStack');
    const LeanSyntax = lateCtor('LeanSyntax');
    const LeanTactic = lateCtor('LeanTactic');
    const LeanTacticBlock = lateCtor('LeanTacticBlock');
    const Lean_fun = lateCtor('Lean_fun');
    const Lean_int = lateCtor('Lean_int');
    const Lean_show = lateCtor('Lean_show');
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before args registration');
            return map[key];
        },
    });

    class LeanArgsSpaceSeparated extends LeanArgs {
        static input_priority = 80; // exp x ^ n where exp x evaluates first
        constructor(args, indent, level, parent = null) {
            super(args, indent, level, parent);
            this.cache = null;
        }

        construct_prefix_tree() {
            const tokens = this.tokens_space_separated();
            return leanEvalPrefix(tokens, (arg) => arg.operand_count());
        }

        get stack_priority() {
            if (this.parent instanceof LeanBracket) return 17;
            if (
                this.parent instanceof LeanArgsCommaSeparated &&
                this.parent.parent instanceof LeanGetElem
            )
                return 18;
            if (
                this.parent instanceof LeanGetElem ||
                this.parent instanceof LeanGetElemQue ||
                this.parent instanceof LeanGetElemQuote
            )
                return 18;
            return 80;
        }

        peelGroup() {
            return this.args.length === 1 ? this.args[0].peelGroup() : this;
        }

        /**
         * @param {Record<string, unknown>} vars
         * @param {Lean} arg
         * @returns {unknown}
         */
        get_type(vars, arg) {
            if (arg instanceof LeanToken) return vars[arg.text] ?? '';
            if (arg instanceof LeanArgsSpaceSeparated) {
                const segs = arg.args.map((a) => this.get_type(vars, a)).map((x) => String(x ?? ''));
                return leanVarsGetitem(vars, segs);
            }
            return '';
        }

        /**
         * `A.hstack B` or `Tensor.hstack A B` → `[A, B]`.
         * @returns {Lean[] | null}
         */
        hstackBlocks() {
            const func = this.args[0];
            if (!(func instanceof LeanProperty) || !(func.rhs instanceof LeanToken) || func.rhs.text !== 'hstack')
                return null;
            if (this.args.length === 2) return [func.lhs, this.args[1]];
            if (this.args.length === 3) return [this.args[1], this.args[2]];
            return null;
        }

        insert(caret, func, type) {
            const last = this.args[this.args.length - 1];
            if (last === caret && !(caret instanceof LeanCaret) && type !== 'modifier') {
                const c = new LeanCaret(this.indent, caret.level);
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                this.push(new Ctor(c, c.indent, c.level));
                return c;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_colon(caret) {
            for (let n = caret; n.parent; n = n.parent) {
                const p = n.parent;
                if (p instanceof LeanIte && p.if === n) {
                    const c = new LeanCaret(caret.indent, caret.level);
                    caret.parent.replace(caret, new LeanColon(caret, c, caret.indent, caret.level));
                    return c;
                }
            }
            return caret.push_binary(LeanColon);
        }

        insert_unary(caret, func) {
            const last = this.args[this.args.length - 1];
            if (last !== caret) throw new Error(`insert_unary is unexpected for ${this.constructor.name}`);
            const {indent} = this;
            const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
            if (caret instanceof LeanCaret) {
                this.replace(caret, new Ctor(caret, indent, caret.level));
                return caret;
            }
            const c = new LeanCaret(indent, caret.level);
            this.push(new Ctor(c, indent, this.level));
            return c;
        }

        insert_word(caret, word) {
            const newTok = new LeanToken(word, this.indent, caret.level);
            this.push(newTok);
            return newTok;
        }

        push_post_unary(funcName) {
            const last = this.args[this.args.length - 1];
            if (!(last instanceof LeanCaret) && last != null) {
                // A postfix operator (`ᵀ`, `²`, `⁻¹`, …) right after the final argument binds to
                // that argument only: `f x yᵀ` parses as `f x (yᵀ)`, not `(f x y)ᵀ`.
                const Ctor = LEAN_CLASSES[funcName];
                const created = new Ctor(last, last.indent, last.level);
                this.replace(last, created);
                return created;
            }
            return super.push_post_unary(funcName);
        }

        is_Abs() {
            const args = this.args;
            const func = args[0];
            return func instanceof LeanToken && args.length === 2 && func.text === 'abs';
        }

        /** `inner 𝕜 x y` (or legacy `inner x y`) → `⟪x, y⟫`; returns `[x, y]` or null. */
        innerOperands() {
            const args = this.args;
            const func = args[0];
            const isInner = func instanceof LeanToken ? func.text === 'inner'
                : func instanceof LeanProperty && func.rhs instanceof LeanToken && func.rhs.text === 'inner' &&
                    func.lhs instanceof LeanToken && func.lhs.text === 'Inner';
            if (!isInner) return null;
            if (args.length === 4) return [args[2], args[3]];
            if (args.length === 3) return [args[1], args[2]];
            return null;
        }

        substOperands() {
            const {args} = this;
            if (args.length !== 2) return null;
            const [func, paren] = args;
            if (!(func instanceof LeanToken) || func.text !== 'Subst') return null;
            if (!(paren instanceof LeanParenthesis)) return null;
            const inner = paren.arg;
            if (!(inner instanceof LeanBitOr)) return null;
            const bindings = [];
            const split = (n) => {
                if (n instanceof LeanEq && n.lhs instanceof LeanToken) return {name: n.lhs, value: n.rhs};
                if (n instanceof LeanBinaryBoolean && !(n instanceof LeanLogic)) {
                    const inner = split(n.lhs);
                    if (!inner) return null;
                    const value = n.clone();
                    value.args = [inner.value, n.rhs];
                    return {name: inner.name, value};
                }
                return null;
            };
            const collect = (n) => {
                if (n instanceof Lean_land) return collect(n.lhs) && collect(n.rhs);
                const binding = split(n);
                if (!binding) return false;
                bindings.push(binding);
                return true;
            };
            if (!collect(inner.rhs)) return null;
            return {body: inner.lhs, bindings};
        }

        gradientOperands() {
            const {args} = this;
            if (args.length < 2) return null;
            const head = args[0];
            if (!(head instanceof LeanGetElem)) return null;
            const [base, index] = head.args;
            if (!(base instanceof LeanToken) || base.text !== '∇') return null;
            if (index instanceof LeanToken) return {name: index, point: null, body: args.slice(1)};
            if (index instanceof LeanEq && index.lhs instanceof LeanToken)
                return {name: index.lhs, point: index.rhs, body: args.slice(1)};
            return null;
        }

        is_Tendsto() {
            const args = this.args;
            if (args.length !== 4) return false;
            const func = args[0];
            if (func instanceof LeanToken) return func.text === 'Tendsto';
            return (
                func instanceof LeanProperty &&
                func.rhs instanceof LeanToken && func.rhs.text === 'Tendsto'
            );
        }

        /** `Ico` / `Finset.Ico` / `Set.Ico` (and Icc, Ioc, Ioo, Ici, Iic, Ioi, Iio). */
        intervalCtor() {
            const func = this.args[0];
            if (func instanceof LeanToken) return func.text;
            if (func instanceof LeanProperty && func.rhs instanceof LeanToken) return func.rhs.text;
            return null;
        }

        /**
         * `descFactorial x k` / `x.descFactorial k` / `Nat.descFactorial n k`
         * (same shapes for `ascFactorial`).
         */
        factorialPowerOperands() {
            const {args} = this;
            const func = args[0];
            if (func instanceof LeanToken && args.length === 3)
                return [args[1], args[2]];
            if (func instanceof LeanProperty && func.rhs instanceof LeanToken) {
                if (args.length === 2) return [func.lhs, args[1]];
                if (args.length === 3) return [args[1], args[2]];
            }
            return null;
        }

        /** Falling \(x^{\underline{k}}\) / rising \(x^{\overline{k}}\). */
        factorialPowerLatexFormat() {
            if (!this.factorialPowerOperands()) return null;
            const func = this.args[0];
            const name = func instanceof LeanToken ? func.text
                : func instanceof LeanProperty && func.rhs instanceof LeanToken ? func.rhs.text
                : null;
            switch (name) {
                case 'descFactorial':
                    return '{%s}^{\\underline{%s}}';
                case 'ascFactorial':
                    return '{%s}^{\\overline{%s}}';
                default:
                    return null;
            }
        }

        /** `Ico a b` → `[a, b)`. */
        intervalLatexFormat() {
            const ctor = this.intervalCtor();
            if (!ctor) return null;
            switch (this.args.length) {
                case 2:
                    switch (ctor) {
                        case 'Ici':
                            return '\\left[%s, \\infty\\right)';
                        case 'Iic':
                            return '\\left(-\\infty, %s\\right]';
                        case 'Ioi':
                            return '\\left(%s, \\infty\\right)';
                        case 'Iio':
                            return '\\left(-\\infty, %s\\right)';
                        default:
                            return null;
                    }
                case 3:
                    switch (ctor) {
                        case 'Ioc':
                            return '\\left(%s, %s\\right]';
                        case 'Ioo':
                            return '\\left(%s, %s\\right)';
                        case 'Icc':
                            return '\\left[%s, %s\\right]';
                        case 'Ico':
                            return '\\left[%s, %s\\right)';
                        default:
                            return null;
                    }
                default:
                    return null;
            }
        }

        is_Bool() {
            const args = this.args;
            const func = args[0];
            return func instanceof LeanProperty &&
                func.rhs instanceof LeanToken &&
                func.rhs.text === 'toNat' &&
                func.lhs instanceof LeanToken &&
                func.lhs.text === 'Bool';
        }

        is_Sum() {
            const [func, zero] = this.args;
            return func instanceof LeanProperty && 
                func.lhs instanceof LeanParenthesis && func.lhs.arg instanceof LeanStack &&
                func.rhs instanceof LeanToken && func.rhs.text === 'sum' && 
                zero instanceof LeanToken && 
                zero.text === '0';
        }

        is_Prod() {
            const [func, zero] = this.args;
            return func instanceof LeanProperty &&
                func.lhs instanceof LeanParenthesis && func.lhs.arg instanceof LeanStack &&
                func.rhs instanceof LeanToken && func.rhs.text === 'prod' &&
                zero instanceof LeanToken &&
                zero.text === '0';
        }

        is_MatProd() {
            const {args} = this;
            if (args.length !== 3) return false;
            const func = args[0];
            const isMatProd =
                (func instanceof LeanToken && func.text === 'matProd') ||
                (func instanceof LeanProperty &&
                    func.rhs instanceof LeanToken &&
                    func.rhs.text === 'matProd');
            if (!isMatProd) return false;
            const peel = (arg) => (arg instanceof LeanParenthesis ? arg.arg : arg);
            const fn = peel(args[2]);
            if (!(fn instanceof Lean_fun)) return false;
            const arrow = fn.arg;
            return arrow instanceof LeanRightarrow || arrow instanceof Lean_mapsto;
        }

        /**
         * LaTeX parts for matProd: `[i, n, body]` for `\prod\limits_{i < n} {body}`.
         * @returns {[string, string, string] | null}
         */
        matProdLatexParts(syntax) {
            if (!this.is_MatProd()) return null;
            const peel = (arg) => (arg instanceof LeanParenthesis ? arg.arg : arg);
            const n = peel(this.args[1]);
            const arrow = peel(this.args[2]).arg;
            let binder = peel(arrow.lhs);
            if (binder instanceof LeanColon) binder = binder.lhs;
            return [binder.toLatex(syntax), n.toLatex(syntax), arrow.rhs.toLatex(syntax)];
        }

        /** An explicit named-implicit argument `(name := value)`, as in `eye (α := α) m`. */
        isNamedImplicitArg(arg) {
            const a = arg instanceof LeanParenthesis ? arg.arg : arg;
            return a instanceof LeanAssign && a.lhs instanceof LeanToken;
        }

        /**
         * The single positional argument of `eye n` / `Tensor.eye n`, ignoring explicit
         * named-implicit args such as `(α := α)`; null for any other function or arity.
         */
        eyePositionalArgs(args) {
            const func = args[0];
            const isEye =
                (func instanceof LeanToken && func.text === 'eye') ||
                (func instanceof LeanProperty &&
                    func.rhs instanceof LeanToken &&
                    func.rhs.text === 'eye');
            if (!isEye) return null;
            const positional = args.slice(1).filter((arg) => !this.isNamedImplicitArg(arg));
            return positional.length === 1 ? positional : null;
        }

        is_indented() {
            const parent = this.parent;
            return (
                parent instanceof LeanStatements ||
                parent instanceof LeanArgsCommaNewLineSeparated ||
                parent instanceof LeanArgsNewLineSeparated ||
                (parent instanceof LeanIte && !parent.inline && (this === parent.then || this === parent.else))
            );
        }

        isProp(vars) {
            const targs = this.args.map((a) => this.get_type(vars, a));
            const type0 = targs[0];
            if (type0 != null && typeof type0 === 'object') {
                const rest = targs.slice(1).map((x) => String(x ?? ''));
                if (leanVarsGetitem(type0, rest) === 'Prop') return true;
            }
            const {args} = this;
            const func = args[0];
            if (func instanceof LeanToken) {
                switch (func.text) {
                    case 'HEq':
                    case 'Infinitesimal':
                    case 'Infinite':
                    case 'InfinitePos':
                    case 'InfiniteNeg':
                    case 'Tendsto':
                        return true;
                    default:
                }
            } else if (
                func instanceof LeanProperty &&
                func.rhs instanceof LeanToken &&
                func.rhs.text === 'Tendsto'
            ) {
                return true;
            }
            if (args.length == 3 && args[1] instanceof LeanToken && args[1].text === 'is')
                return true;
        }

        is_space_separated() {
            return true;
        }

        /**
         * @param {Record<string, unknown> | null} [syntax]
         * @returns {string[]}
         */
        /** `id (α := T) e` — identity; LaTeX prints only `e`. */
        idLatexInner() {
            const {args} = this;
            if (args.length !== 3 || !(args[0] instanceof LeanToken) || args[0].text !== 'id')
                return null;
            const named = args[1] instanceof LeanParenthesis ? args[1].arg : args[1];
            if (!(named instanceof LeanAssign && named.lhs instanceof LeanToken && named.lhs.text === 'α'))
                return null;
            let inner = args[2];
            if (
                inner instanceof LeanParenthesis &&
                !(inner.arg instanceof LeanColon) &&
                this.canStripIdParen(inner.arg)
            )
                inner = inner.arg;
            return inner;
        }

        /**
         * `A op B op' C` compares `op.stack_priority` with `op'.input_priority`.
         * After dropping `id`, `inner` is `op` on the left and `op'` on the right.
         */
        canStripIdParen(inner) {
            const parent = this.parent;
            if (!parent) return true;
            if (parent instanceof LeanBinary) {
                if (parent.lhs === this)
                    return parent.constructor.input_priority <= inner.stack_priority;
                if (parent.rhs === this)
                    return inner.constructor.input_priority > parent.stack_priority;
            }
            return inner.constructor.input_priority > parent.stack_priority;
        }

        static isProbBinderHead(node) {
            return (
                node instanceof LeanGetElem &&
                node.args[0] instanceof LeanToken &&
                node.args[0].text === 'ℙ'
            );
        }

        static markProbBinderArgs(node) {
            const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
            const markRA = (n) => {
                if (n instanceof LeanToken) n.kwargs.isRandomArgument = true;
            };
            const markRV = (n) => {
                if (n instanceof LeanToken) n.kwargs.isRandomVariable = true;
                // a slice of a sequence of random variables, e.g. `x[:t + 1]`
                else if (n instanceof LeanGetElem && n.args[0] instanceof LeanToken)
                    n.args[0].kwargs.isRandomVariable = true;
                // a random variable sequence applied to an index, e.g. `x 0`
                else if (n instanceof LeanArgsSpaceSeparated && n.args[0] instanceof LeanToken)
                    n.args[0].kwargs.isRandomVariable = true;
            };
            const markFactor = (n) => {
                if (!n) return;
                n = peel(n);
                if (n instanceof LeanToken) {
                    markRA(n);
                    return;
                }
                if (n instanceof LeanEq) {
                    markRV(peel(n.lhs));
                    return;
                }
                if (n instanceof LeanBitOr) {
                    markFactor(n.lhs);
                    markFactor(n.rhs);
                    return;
                }
                if (n instanceof LeanArgsCommaSeparated) {
                    for (const a of n.args) markFactor(a);
                    return;
                }
                if (typeof Lean_land !== 'undefined' && n instanceof Lean_land) {
                    markFactor(n.lhs);
                    markFactor(n.rhs);
                    return;
                }
            };
            markFactor(node);
        }

        static bvarQuotationName(n) {
            const peel = (x) => (x instanceof LeanParenthesis ? x.arg : x);
            n = peel(n);
            if (!(n instanceof LeanDoubleAngleQuotation)) return null;
            const lhs = n.boundValueLhs();
            return lhs instanceof LeanToken ? lhs : null;
        }

        static rvEqToken(n) {
            const peel = (x) => (x instanceof LeanParenthesis ? x.arg : x);
            n = peel(n);
            if (!(n instanceof LeanEq)) return null;
            const lhs = peel(n.lhs);
            // `x`, a slice `x[:t + 1]`, or an indexed variable `x 0`
            if (
                !(
                    lhs instanceof LeanToken ||
                    (lhs instanceof LeanGetElem && lhs.args[0] instanceof LeanToken) ||
                    (lhs instanceof LeanArgsSpaceSeparated && lhs.args[0] instanceof LeanToken)
                )
            )
                return null;
            // rhs spells the same expression with its base wrapped as a bound value:
            // `«x.bvar»`, `«x.bvar»[:t + 1]` or `«x[:t + 1].bvar»`
            const rhsText = strStmt(n.rhs).trim();
            if (!/«[^»]*\.bvar»/.test(rhsText)) return null;
            const plain = rhsText.replace(/«([^»]*?)\.bvar»/g, '$1');
            if (plain !== strStmt(lhs).trim()) return null;
            return lhs;
        }

        static collectProbEventRVs(n) {
            const peel = (x) => (x instanceof LeanParenthesis ? x.arg : x);
            const out = [];
            const walk = (node) => {
                node = peel(node);
                if (typeof Lean_land !== 'undefined' && node instanceof Lean_land) {
                    return walk(node.lhs) && walk(node.rhs);
                }
                const tok = LeanArgsSpaceSeparated.rvEqToken(node);
                if (!tok) return false;
                out.push(tok);
                return true;
            };
            if (!walk(n) || out.length === 0) return null;
            return out;
        }

        markProbBinderColors() {
            const {args} = this;
            if (args.length < 2 || !LeanArgsSpaceSeparated.isProbBinderHead(args[0])) return;
            LeanArgsSpaceSeparated.markProbBinderArgs(args[1]);
        }

        static isExpectBinderHead(node) {
            return (
                node instanceof LeanGetElem &&
                node.args[0] instanceof LeanToken &&
                node.args[0].text === '𝔼'
            );
        }

        /** Collect bound names (`x`) and free RA names (`y`) from `x: 𝕡 | y`. */
        static expectBinderNames(index) {
            const bound = new Set();
            const free = new Set();
            const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
            const addTok = (n, into) => {
                n = peel(n);
                if (n instanceof LeanToken) into.add(n.text);
                else if (n instanceof LeanArgsCommaSeparated)
                    for (const a of n.args) addTok(a, into);
            };
            const ix = peel(index);
            if (ix instanceof LeanColon) {
                addTok(ix.lhs, bound);
                let ty = peel(ix.rhs);
                if (ty instanceof LeanBitOr) {
                    addTok(ty.rhs, free);
                }
            } else if (ix instanceof LeanBitOr) {
                // rare: bare `x | y` without colon
                addTok(ix.lhs, bound);
                addTok(ix.rhs, free);
            }
            return {bound, free};
        }

        /** Walk body; mark free names magenta, bound names red (bound wins if overlap). */
        static markExpectBodyColors(body, bound, free) {
            const walk = (n) => {
                if (!n || typeof n !== 'object') return;
                if (n instanceof LeanToken) {
                    if (bound.has(n.text)) n.kwargs.isRandomVariable = true;
                    else if (free.has(n.text)) n.kwargs.isRandomArgument = true;
                    return;
                }
                // Body `(expr | y)` — also treat RHS of BitOr as free-RA list when present.
                if (n instanceof LeanBitOr) {
                    walk(n.lhs);
                    const peel = (x) => (x instanceof LeanParenthesis ? x.arg : x);
                    let rhs = peel(n.rhs);
                    const condRVs = LeanArgsSpaceSeparated.collectProbEventRVs(rhs);
                    if (condRVs) {
                        for (const t of condRVs) t.kwargs.isRandomVariable = true;
                        return;
                    }
                    const markFreeList = (x) => {
                        x = peel(x);
                        if (x instanceof LeanToken) {
                            if (!bound.has(x.text)) x.kwargs.isRandomArgument = true;
                            return;
                        }
                        if (x instanceof LeanArgsCommaSeparated)
                            for (const a of x.args) markFreeList(a);
                    };
                    markFreeList(rhs);
                    return;
                }
                if (Array.isArray(n.args)) for (const a of n.args) walk(a);
            };
            walk(body);
        }

        markExpectBinderColors() {
            const {args} = this;
            if (args.length < 2 || !LeanArgsSpaceSeparated.isExpectBinderHead(args[0])) return;
            const head = args[0];
            const {bound, free} = LeanArgsSpaceSeparated.expectBinderNames(head.rhs);
            // Also collect free names from body's `| y` if binder omitted them.
            const peel = (n) => (n instanceof LeanParenthesis ? n.arg : n);
            const body = args[1];
            const b = peel(body);
            if (b instanceof LeanBitOr) {
                const addTok = (n) => {
                    n = peel(n);
                    if (n instanceof LeanToken) free.add(n.text);
                    else if (n instanceof LeanArgsCommaSeparated)
                        for (const a of n.args) addTok(a);
                };
                addTok(b.rhs);
            }
            LeanArgsSpaceSeparated.markExpectBodyColors(body, bound, free);
            // Bound name under 𝔼 (the `x` in `x: 𝕡`) should be red too.
            const ix = peel(head.rhs);
            if (ix instanceof LeanColon && ix.lhs instanceof LeanToken && bound.has(ix.lhs.text))
                ix.lhs.kwargs.isRandomVariable = true;
        }

        latexArgs(syntax = null) {
            this.markProbBinderColors();
            this.markExpectBinderColors();
            const matrixArgs = this.matrixLatexArgs(syntax);
            if (matrixArgs) return matrixArgs;
            const idInner = this.idLatexInner();
            if (idInner) return [idInner.toLatex(syntax)];
            const grad = this.gradientOperands();
            if (grad) {
                const body = grad.body.map((arg) => {
                    if (arg instanceof LeanParenthesis && arg.arg instanceof LeanDiv) arg = arg.arg;
                    return arg.toLatex(syntax);
                });
                const name = grad.name.toLatex(syntax);
                if (!grad.point) return [name, ...body];
                const point = grad.point instanceof LeanParenthesis ? grad.point.arg : grad.point;
                return [name, ...body, name, point.toLatex(syntax)];
            }
            const subst = this.substOperands();
            if (subst)
                return [
                    subst.body.toLatex(syntax),
                    // a compound value is parenthesized in Lean (`term:max`); the subscript needs no parentheses
                    ...subst.bindings.flatMap(({name, value}) => [
                        name.toLatex(syntax),
                        (value instanceof LeanParenthesis ? value.arg : value).toLatex(syntax),
                    ]),
                ];
            const {args} = this;
            const func = args[0];
            if (this.is_MatProd()) return this.matProdLatexParts(syntax);
            if (this.eyePositionalArgs(args)) {
                if (syntax) syntax.eye = true;
                return [];
            }
            if (this.is_Abs()) {
                const stripped = this.strip_parenthesis();
                return [stripped[1].toLatex(syntax)];
            }
            if (this.is_Tendsto()) {
                return [args[2].toLatex(syntax), args[1].toLatex(syntax), args[3].toLatex(syntax)];
            }
            const innerArgs = this.innerOperands();
            if (innerArgs) {
                const peel = (arg) => (arg instanceof LeanParenthesis ? arg.arg : arg);
                return innerArgs.map((a) => peel(a).toLatex(syntax));
            }

            if (this.intervalLatexFormat()) {
                const s = this.strip_parenthesis();
                if (syntax && func instanceof LeanToken) syntax[func.text] = true;
                if (args.length === 2) return [s[1].toLatex(syntax)];
                return [s[1].toLatex(syntax), s[2].toLatex(syntax)];
            }
            if (this.factorialPowerLatexFormat()) {
                const [n, k] = this.factorialPowerOperands();
                const peel = (arg) => (arg instanceof LeanParenthesis ? arg.arg : arg);
                return [n.toLatex(syntax), peel(k).toLatex(syntax)];
            }
            if (func instanceof LeanToken) {
                const fn = func.text;
                if (syntax) syntax[fn] = true;
                switch (args.length) {
                    case 2:
                        switch (fn) {
                            case 'exp':
                            case 'cexp': {
                                const s = this.strip_parenthesis();
                                return [s[1].toLatex(syntax)];
                            }
                            case 'arcsin':
                            case 'arccos':
                            case 'arctan':
                            case 'sin':
                            case 'cos':
                            case 'tan':
                            case 'arg':
                            case 'arcsec':
                            case 'arccsc':
                            case 'arccot':
                            case 'arcsinh':
                            case 'arccosh':
                            case 'arctanh':
                            case 'arccoth': {
                                let arg = args[1];
                                if (arg instanceof LeanParenthesis && arg.arg instanceof LeanDiv) arg = arg.arg;
                                return [arg.toLatex(syntax)];
                            }
                            case 'Zeros':
                            case 'Ones': {
                                const s = this.strip_parenthesis();
                                return [s[1].toLatex(syntax)];
                            }
                            default:
                        }
                        break;
                    case 3:
                        switch (fn) {
                            case 'KroneckerDelta':
                                return [args[1].toLatex(syntax), args[2].toLatex(syntax)];
                            default:
                        }
                        break;
                    default:
                }
            } else if (this.is_Bool()) {
                const stripped = this.strip_parenthesis();
                return [stripped[1].toLatex(syntax)];
            } else if (this.is_Sum() || this.is_Prod()) {
                return this.args[0].lhs.arg.latexArgs();
            } else if (
                func instanceof LeanProperty &&
                func.rhs instanceof LeanToken &&
                func.rhs.text === 'choose' &&
                (args.length === 2 || args.length === 3)
            ) {
                const n = args.length === 2 ? func.lhs : args[1];
                const k = args.length === 2 ? args[1] : args[2];
                const peel = (arg) => (arg instanceof LeanParenthesis ? arg.arg : arg);
                return [peel(n).toLatex(syntax), peel(k).toLatex(syntax)];
            }
            return args.map((arg) => {
                if (arg instanceof LeanParenthesis && arg.arg instanceof LeanDiv)
                    arg = arg.arg;
                return arg.toLatex(syntax)
            });
        }

        latexFormat() {
            const rows = this.matrixLatexSpec();
            if (rows) return LeanAppend.bmatrixFormat(rows.length, rows[0].length);
            if (this.idLatexInner()) return '%s';
            const grad = this.gradientOperands();
            if (grad) {
                // `\nabla_{θ} body`, or `\left. \nabla_{θ} body \right|_{θ = θ_0}` for `∇[θ = θ₀] body`
                const body = grad.body.map(() => '{%s}').join('\\ ');
                const nabla = `\\nabla_{%s} {${body}}`;
                if (!grad.point) return nabla;
                return `\\left. ${nabla} \\right|_{{%s} = {%s}}`;
            }
            const subst = this.substOperands();
            if (subst) {
                // sympy `_print_Subs`: `\left. expr \right|_{\substack{x=x_0 \\ y=y_0}}`
                const subs = subst.bindings.map(() => '{%s} = {%s}').join(' \\\\ ');
                if (subst.bindings.length === 1) return `\\left. {%s} \\right|_{${subs}}`;
                return `\\left. {%s} \\right|_{\\substack{${subs}}}`;
            }
            const {args} = this;
            const func = args[0];
            if (this.is_Abs()) return '\\left|{%s}\\right|';
            if (this.is_Tendsto()) return '{%s} \\xrightarrow{\\,%s\\,} {%s}';
            if (this.innerOperands()) return '\\left\\langle {%s}, {%s} \\right\\rangle';

            if (this.is_MatProd()) return '\\prod\\limits_{%s < %s} {%s}';
            if (this.eyePositionalArgs(args)) return '\\mathbb{I}';
            const interval = this.intervalLatexFormat();
            if (interval) return interval;
            const factorialPower = this.factorialPowerLatexFormat();
            if (factorialPower) return factorialPower;
            // `f ⁻¹' s` — preimage as `f^{-1}[s]` (not to be read as an inverse applied to `s`)
            if (func instanceof LeanPreimage && args.length === 2) return '%s\\left[%s\\right]';
            if (func instanceof LeanToken) {
                switch (args.length) {
                    case 2:
                        switch (func.text) {
                            case 'exp':
                            case 'cexp':
                                return '{\\color{RoyalBlue} e} ^ {%s}';
                            case 'arcsin':
                            case 'arccos':
                            case 'arctan':
                            case 'sin':
                            case 'cos':
                            case 'tan':
                            case 'arg':
                                return `\\${func.text} {%s}`;
                            case 'arcsec':
                            case 'arccsc':
                            case 'arccot':
                            case 'arcsinh':
                            case 'arccosh':
                            case 'arctanh':
                            case 'arccoth':
                                return `${func.text}\\ {%s}`;
                            case 'Zeros':
                                return '\\mathbf{0}_{%s}';
                            case 'Ones':
                                return '\\mathbf{1}_{%s}';
                            default:
                        }
                        break;
                    case 3:
                        switch (func.text) {
                            case 'KroneckerDelta':
                                return '\\delta_{%s %s}';
                            default:
                        }
                        break;
                    default:
                }
            } else if (this.is_Bool()) {
                return '\\left|{%s}\\right|';
            } else if (this.is_Sum() || this.is_Prod()) {
                return `\\${this.args[0].rhs.text}\\limits_{\\substack{%s}} {%s}`;
            } else if (func instanceof LeanProperty && func.rhs instanceof LeanToken) {
                if (func.rhs.text === 'fmod' && args.length === 2) return '{%s}{%s}';
                if (func.rhs.text === 'choose' && (args.length === 2 || args.length === 3))
                    return '\\binom{%s}{%s}';
            }
            const n = args.length;
            return Array(n)
                .fill('{%s}')
                .join('\\ ');
        }

        operand_count() {
            return this.args[0].operand_count();
        }

        strArgs() {
            const args = this.args;
            let start = 0;
            while (start < args.length && args[start] instanceof LeanCaret) start++;
            const slice = args.slice(start);
            const p = this.parent;
            if (p instanceof LeanTactic && slice.length > 1) {
                const floor = (p.indent ?? 0) + 2;
                return slice.map((a, i) => {
                    if (i === 0 || a instanceof LeanToken || a instanceof LeanCaret) return a;
                    if (a instanceof LeanSyntax || (typeof a.is_comment === 'function' && a.is_comment())) {
                        const c = a.clone();
                        if ((c.indent ?? 0) < floor) c.indent = floor;
                        return c;
                    }
                    return a;
                });
            }
            return slice;
        }

        strFormat() {
            const args = this.args;
            const n = args.length;
            if (n === 0) return '';
            let start = 0;
            while (start < n && args[start] instanceof LeanCaret) start++;
            if (start >= n) return '';
            if (this.parent instanceof LeanTactic) {
                let out = '%s';
                for (let j = start + 1; j < n; j++) {
                    const a = args[j];
                    // `have` / `let` / `show` extend `LeanSyntax` but not `LeanTactic`; keep them on new lines like `by_contra`.
                    const sep = a instanceof LeanSyntax || a.is_comment() ? '\n' : ' ';
                    out += sep;
                    out += '%s';
                }
                return out;
            }
            return Array(n - start).fill('%s').join(' ');
        }

        tactic_block_info() {
            if (!this.cache) this.cache = {};
            if (this.cache.tactic_block_info != null)
                return /** @type {Record<number, LeanToken[]>} */ (this.cache.tactic_block_info);
            const nodes = this.construct_prefix_tree();
            let physic_index = 0;
            let logic_index = 0;
            for (const node of nodes) {
                node.traverse((n) => {
                    /** @type {ParserPrefixExpr[] | null} */
                    let args;
                    if (n.parent) args = n.parent.args;
                    else args = nodes;
                    const i = args.indexOf(n);
                    if (i > 0) {
                        for (let j = i - 1; j >= 0; j--) {
                            const size = args[j].size();
                            const pi = /** @type {{ physic_index?: number }} */ (args[j].cache).physic_index ?? 0;
                            if (pi + size === physic_index) {
                                const fc = /** @type {LeanToken} */ (args[j].func);
                                if (!fc.cache) fc.cache = {};
                                const idx = /** @type {{ index?: number }} */ (fc.cache).index ?? 0;
                                logic_index = Math.max(logic_index, idx + size);
                            }
                        }
                    } else if (n.parent && /** @type {LeanToken} */ (n.parent.func).is_parallel_operator()) {
                        logic_index++;
                    }
                    const f = /** @type {LeanToken} */ (n.func);
                    if (!f.cache) f.cache = {};
                    f.cache.index = logic_index;
                    f.cache.size = n.size();
                    n.cache.physic_index = physic_index;
                    physic_index++;
                });
            }
            const tokens = this.tokens_space_separated();
            /** @type {Record<number, LeanToken[]>} */
            const map = {};
            for (let ti = tokens.length - 1; ti >= 0; ti--) {
                const token = tokens[ti];
                if (!token.cache) token.cache = {};
                if (token.is_parallel_operator()) {
                    const sz = /** @type {{ size?: number }} */ (token.cache).size ?? 1;
                    token.cache.size = sz - 1;
                }
                const idx = /** @type {{ index?: number }} */ (token.cache).index ?? 0;
                if (!map[idx]) map[idx] = [];
                map[idx].push(token);
            }
            this.cache.tactic_block_info = map;
            return map;
        }

        tokens_space_separated() {
            if (!this.cache) this.cache = {};
            if (this.cache.tokens_space_separated != null)
                return /** @type {LeanToken[]} */ (this.cache.tokens_space_separated);
            const tokens = [];
            for (const arg of this.args) {
                if (arg instanceof LeanToken) tokens.push(arg);
                else if (arg instanceof LeanAngleBracket) tokens.push(...arg.tokens_comma_separated());
                else {
                    this.cache.tokens_space_separated = [];
                    return [];
                }
            }
            this.cache.tokens_space_separated = tokens;
            return tokens;
        }

        unique_token(indent) {
            const tokens = this.tokens_space_separated();
            if (!tokens.length) return undefined;
            const texts = tokens.map((t) => t.text);
            if (new Set(texts).size !== 1) return undefined;
            const token = tokens[0].clone();
            token.indent = indent;
            return token;
        }
    }

    class LeanArgsNewLineSeparated extends LeanMultipleLine(LeanArgs) {
        get stack_priority() {
            const parent = this.parent;
            if (parent instanceof LeanCalc) return LeanAssign.input_priority - 1;
            if (parent instanceof LeanArgsIndented) {
                const gp = parent.parent;
                if (gp instanceof LeanQuantifier) return 51;
                if (gp instanceof LeanCalc) return LeanAssign.input_priority - 1;
            }
            return 47;
        }

        insert_if(caret) {
            if (!(caret instanceof LeanCaret)) return undefined;
            const last = this.args[this.args.length - 1];
            if (last !== caret) return undefined;
            this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
            return caret;
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent > indent) {
                if (caret instanceof LeanParenthesis && next === ':') return caret;
                return super.insert_newline(caret, newline_count, indent, next);
            }
            if (this.indent < indent) {
                // Multiline app already has ≥2 lines: next indented line is another arg,
                // not nested under a bare Property/Parenthesis (e.g. `(x).isLt` then more args).
                if (this.args.length >= 2) {
                    const c = new LeanCaret(indent, caret.level);
                    this.push(c);
                    return c;
                }
                const $new = this.push_args_indented(indent, newline_count);
                if ($new) return $new;
                const c = new LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
            const last = this.args[this.args.length - 1];
            // if (this.parent instanceof LeanAssign && !(caret instanceof LeanLineComment) && last !== caret)
                // return super.insert_newline(caret, newline_count, indent, next);
            if (last === caret) {
                for (let i = 0; i < newline_count; ++i) {
                    caret = new LeanCaret(indent, caret.level);
                    this.push(caret);
                }
                return caret;
            }
            throw new Error(`LeanArgsNewLineSeparated.insert_newline: unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            return false;
        }

        latexFormat() {
            const n = this.args.length;
            if (n === 0) return '';
            if (n === 1) return '%s';
            const stmt = Array(n).fill('&{%s}&& ').join('\\\\\n');
            const p = this.parent;
            let align = (p instanceof LeanStatements) ? 'align*' : 'aligned';
            return `\\begin{${align}}\n${stmt}\n\\end{${align}}`;
        }

        push_newlines(newline_count) {
            for (let i = 0; i < newline_count; ++i) {
                this.push(new LeanCaret(this.indent, this.level));
            }
            return this.args[this.args.length - 1];
        }

        relocate_last_comment() {
            for (let index = this.args.length - 1; index >= 0; --index) {
                const end = this.args[index];
                if (end instanceof LeanCaret || end.is_comment()) {
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
                        return parent.relocate_last_comment();
                    }
                } else {
                    return end.relocate_last_comment();
                }
            }
        }

        strFormat() {
            return Array(this.args.length).fill('%s').join('\n');
        }
    }



    class LeanArgsIndented extends LeanBinary {
        get stack_priority() {
            if (this.parent instanceof LeanCalc) return 17;
            if (this.parent instanceof LeanQuantifier) return LeanRelational.input_priority + 1;
            return 47;
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.indent > indent) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            if (this.indent < indent) {
                const $new = this.push_args_indented(indent, newline_count);
                if ($new) return $new;
                this.rhs = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                return this.rhs.push_newlines(newline_count);
            }
            if (this.parent instanceof LeanAssign) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            if ((this.parent instanceof LeanTactic || this.parent instanceof Lean_show) && !leanIsInfixContinue(next)) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            // `∫ ω, f ω\n    ∂μ` integrand (see `Lean_int.continueMeasure`): a line that is not deeper ends the integral.
            if (this.parent instanceof Lean_int && this.parent.scope === this) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            // `calc first\n    _ = c := q\n  exact h` — only a `_` step continues the calc at this column.
            if (this.parent instanceof LeanCalc && next !== '_') {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            const last = this.args[this.args.length - 1];
            if (last === caret) {
                for (let i = 0; i < newline_count; ++i) {
                    caret = new LeanCaret(indent, caret.level);
                    this.push(caret);
                }
                return caret;
            }
            throw new Error(`LeanArgsIndented.insert_newline is unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            const p = this.parent;
            return (
                p instanceof LeanStatements ||
                p instanceof LeanArgsNewLineSeparated ||
                p instanceof LeanArgsCommaNewLineSeparated ||
                (p instanceof LeanAssign && p.sep() === '\n')
            );
        }

        /**
         * `f\n  (g\n    (h x))` — a function applied to a single argument on the next line
         * (the argument itself may again be a multi-line application).
         */
        isMultilineApplication() {
            const {lhs, rhs} = this;
            if (!(lhs instanceof LeanToken || lhs instanceof LeanProperty)) return false;
            if (rhs instanceof LeanParenthesis) return true;
            return rhs instanceof LeanArgsNewLineSeparated &&
                rhs.args.filter((a) => !(a instanceof LeanCaret)).length === 1 &&
                rhs.args[0] instanceof LeanParenthesis;
        }

        latexFormat() {
            // LaTeX ignores the newline; without a space the head and argument run together.
            if (this.isMultilineApplication()) return '%s\\ %s';
            const sep = this.sep();
            return `%s${sep}%s`;
        }

        relocate_last_comment() {
            for (let index = this.args.length - 1; index >= 0; --index) {
                const end = this.args[index];
                if (end instanceof LeanCaret || end.is_comment()) {
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
                        return parent.relocate_last_comment();
                    }
                } else {
                    return end.relocate_last_comment();
                }
            }
        }

        sep() {
            return '\n';
        }

        strFormat() {
            const sep = this.sep();
            return `%s${sep}%s`;
        }
    }

    class LeanArgsCommaSeparated extends LeanArgs {
        /**
         * Under LeanBar: LeanColon input priority; else one less so `:` binds in the right place.
         * GetElem index uses parent `LeanGetElem*` stack_priority, not this.
         */
        get stack_priority() {
            if (this.parent instanceof LeanBar) return LeanColon.input_priority;
            return LeanColon.input_priority - 1;
        }

        insert(caret, func, type) {
            const last = this.args[this.args.length - 1];
            if (last === caret) {
                if (caret instanceof LeanCaret) {
                    const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                    this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                    return caret;
                }
                if (this.parent) return this.parent.insert(this, func, type);
            }
        }

        insert_comma(caret) {
            caret = new LeanCaret(this.indent, caret.level);
            this.push(caret);
            return caret;
        }

        /**
         * Trailing comma then newline inside `[…]` / `⟨…⟩`: this line stays `LeanArgsCommaSeparated`;
         * the bracket body becomes (or grows) `LeanArgsCommaNewLineSeparated`.
         * Sibling items keep the incoming indent — do not bump by +2 (that made later
         * one-item-per-line entries look like a dedent and attach `.eq…` to the previous line).
         */
        insert_newline(caret, newline_count, indent, next) {
            if (caret instanceof LeanCaret && this.args[this.args.length - 1] === caret) {
                if (this.indent > indent) {
                    return super.insert_newline(caret, newline_count, indent, next);
                }
                this.args.pop();
                const lineCaret = new LeanCaret(indent, caret.level);
                const line = new LeanArgsCommaSeparated([lineCaret], indent, caret.level);
                const parent = this.parent;
                if (parent instanceof LeanArgsCommaNewLineSeparated) {
                    parent.push(line);
                    return lineCaret;
                }
                parent.replace(this, new LeanArgsCommaNewLineSeparated([this, line], indent, this.level));
                return lineCaret;
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        insert_tactic(caret, token) {
            if (caret instanceof LeanCaret) return this.insert_word(caret, token);
            throw new Error(`LeanArgsCommaSeparated.insert_tactic: unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            if (this.parent instanceof LeanArgsCommaNewLineSeparated)
                return this.parent.args.indexOf(this) > 0;
            return false;
        }

        latexFormat() {
            const n = this.args.length;
            return Array(n)
                .fill('{%s}')
                .join(', ');
        }

        strFormat() {
            return Array(this.args.length).fill('%s').join(', ');
        }

        tokens_comma_separated() {
            const tokens = [];
            for (const arg of this.args) {
                if (arg instanceof LeanToken) tokens.push(arg);
                else if (arg instanceof LeanAngleBracket) tokens.push(...arg.tokens_comma_separated());
            }
            return tokens;
        }
    }

    class LeanArgsSemicolonSeparated extends LeanArgs {
        get stack_priority() {
            return LeanColon.input_priority - 1;
        }

        insert(caret, func, type) {
            const last = this.args[this.args.length - 1];
            if (last === caret) {
                if (caret instanceof LeanCaret) {
                    const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                    this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                    return caret;
                }
                if (this.parent) return this.parent.insert(this, func, type);
            }
        }

        insert_semicolon(caret) {
            const c = new LeanCaret(this.indent, caret.level);
            this.push(c);
            return c;
        }

        insert_tactic(caret, type) {
            if (caret instanceof LeanCaret) {
                const p = this.parent;
                if ((p instanceof LeanTactic && p.is_inline_tactic_block()) || p instanceof LeanBy || p instanceof LeanStatements
                    || p instanceof LeanTacticBlock) {
                    this.replace(caret, new LeanTactic(type, caret, this.indent, caret.level));
                    return caret;
                }
                return this.insert_word(caret, type);
            }
            throw new Error(`LeanArgsSemicolonSeparated.insert_tactic: unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            const p = this.parent;
            return p instanceof LeanStatements && this.indent > 0 || p instanceof LeanBy && this.indent > p.indent;
        }

        latexFormat() {
            return Array(this.args.length)
                .fill('{%s}')
                .join('; ');
        }

        strFormat() {
            return Array(this.args.length).fill('%s').join('; ');
        }
    }

    class LeanArgsCommaNewLineSeparated extends LeanMultipleLine(LeanArgs) {
        get stack_priority() {
            return 17;
        }

        /**
         * @param {Lean} caret
         * @param {string | typeof Lean} func
         * @param {string} [type]
         */
        insert(caret, func, type) {
            const last = this.args[this.args.length - 1];
            if (last === caret && caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
                this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                return caret;
            }
            throw new Error(`LeanArgsCommaNewLineSeparated.insert: unexpected for ${this.constructor.name}`);
        }

        insert_comma(caret) {
            const c2 = new LeanCaret(caret.indent, caret.level);
            if (caret instanceof LeanArgsCommaSeparated) {
                caret.push(c2);
                return c2;
            }
            this.replace(caret, new LeanArgsCommaSeparated([caret, c2], caret.indent, caret.level));
            return c2;
        }

        /** When indent increases, also tries `push_args_indented` (multiline `⟨…⟩` / `[…]`). */
        insert_newline(caret, newline_count, indent, next) {
            if (this.indent > indent) {
                return super.insert_newline(caret, newline_count, indent, next);
            }
            if (this.indent < indent) {
                const $new = this.push_args_indented(indent, newline_count, false);
                if ($new) return $new;
                const c = new LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
            const last = this.args[this.args.length - 1];
            if (last === caret) {
                if (caret instanceof LeanArgsCommaSeparated) {
                    if (caret.args[caret.args.length - 1] instanceof LeanCaret) caret.args.pop();
                    const lineCaret = new LeanCaret(indent, caret.level);
                    const line = new LeanArgsCommaSeparated([lineCaret], indent, caret.level);
                    this.push(line);
                    return lineCaret;
                }
                for (let i = 0; i < newline_count - 1; ++i) {
                    caret = new LeanCaret(indent, caret.level);
                    this.push(caret);
                }
                return caret;
            }
            throw new Error(`LeanArgsCommaNewLineSeparated.insert_newline: unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            return false;
        }

        latexFormat() {
            return Array(this.args.length)
                .fill('{%s}')
                .join(',\n');
        }

        strFormat() {
            return Array(this.args.length).fill('%s').join(',\n');
        }
    }

    return {
        LeanArgsSpaceSeparated,
        LeanArgsNewLineSeparated,
        LeanArgsIndented,
        LeanArgsCommaSeparated,
        LeanArgsSemicolonSeparated,
        LeanArgsCommaNewLineSeparated,
    };
}
