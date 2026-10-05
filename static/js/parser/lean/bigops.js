/**
 * Big operators that extend `LeanBigOperator`: `∑` / `lim` / `∏` / `∫` /
 * `⋂` / `⋃` / `⨅` / `⨆` / `Stack`.
 *
 * Quantifiers stay in `quantifier.js`. `LeanAdd` is read for `input_priority`;
 * `LeanPlus`, `Lean_partial`, `LeanParenthesis`, and `LeanDoubleAngleQuotation`
 * are only used via `instanceof`. All five are filled on `bigopsLate` after
 * the paired and arithmetic factories return. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {object} deps.bigopsLate
 */
export function createBigOpsFamily(deps) {
    const {
        LeanBigOperator,
        LeanArgsCommaNewLineSeparated,
        LeanArgsIndented,
        LeanArgsNewLineSeparated,
        LeanArgsSpaceSeparated,
        LeanCaret,
        LeanColon,
        LeanEq,
        LeanIn,
        LeanIte,
        LeanProperty,
        LeanRelational,
        LeanStatements,
        LeanToken,
        LeanUpto,
        Lean_in,
        Lean_rightarrow,
        strStmt,
        bigopsLate,
    } = deps;
    function lateClass(name) {
        function Ctor() {}
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = bigopsLate[name];
                if (real == null) throw new Error(`${name} used before big-operator registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    function lateStatic(name) {
        return new Proxy(Object.create(null), {
            get(_target, prop) {
                const real = bigopsLate[name];
                if (real == null) throw new Error(`${name} used before big-operator registration`);
                return real[prop];
            },
        });
    }
    const LeanAdd = lateStatic('LeanAdd');
    const LeanPlus = lateClass('LeanPlus');
    const Lean_partial = lateClass('Lean_partial');
    const LeanParenthesis = lateClass('LeanParenthesis');
    const LeanDoubleAngleQuotation = lateClass('LeanDoubleAngleQuotation');

    class Lean_sum extends LeanBigOperator {
        static input_priority = 67;
        /** Mathlib parses big-operator bodies at precedence 67: `∑ i ∈ s, f i + c` is `(∑ i ∈ s, f i) + c`.
         *  Only operators below 67 (`+`/`-`/`++`/`∪`, input 65) close the body; postfix `²` (input 66) stays inside. */
        get stack_priority() {
            return this.scope ? LeanAdd.input_priority : super.stack_priority;
        }
        get baseOperator() {
            return '∑';
        }
        /**
         * `∑ «y.bvar» t, f`: a bound variable is never red, so the index and the body's `y t` that stands
         * for the bound value (`(y t) = «y.bvar» t` inside `ℙ[π](…)`) are drawn in the normal colour.
         */
        latexArgs(syntax) {
            const bnd = this.bound;
            if (
                this.scope &&
                bnd instanceof LeanArgsSpaceSeparated && bnd.args.length === 2 &&
                bnd.args[0] instanceof LeanDoubleAngleQuotation
            ) {
                const base = bnd.args[0].boundValueLhs();
                if (base instanceof LeanToken) {
                    const key = strStmt(bnd).trim();
                    const seen = new Set();
                    const walk = (n) => {
                        if (!n || typeof n !== 'object' || seen.has(n)) return;
                        seen.add(n);
                        if (n instanceof LeanEq && strStmt(n.rhs).trim() === key) {
                            let l = n.lhs;
                            while (l instanceof LeanParenthesis) l = l.arg;
                            if (l instanceof LeanArgsSpaceSeparated) l = l.args[0];
                            if (l instanceof LeanToken && l.text === base.text) l.kwargs.neverRed = true;
                        }
                        if (Array.isArray(n.args)) n.args.forEach(walk);
                    };
                    walk(this.scope);
                    base.kwargs.neverRed = true;
                }
            }
            return super.latexArgs(syntax);
        }
        latexFormat() {
            if (!this.superscript) return super.latexFormat();
            const op = `\\mathop{${this.command}\\nolimits${this.superscript}}`;
            if (this.finRangeBound())
                return `${op}\\limits_{%s < %s} {%s}`;
            return `${op}\\limits_{\\substack{%s}} {%s}`;
        }
    }

    class Lean_lim extends LeanBigOperator {
        static input_priority = 67;
        get command() {
            return '\\lim';
        }
        /** `lim [N → ∞] ∑ n ∈ range N, e` → infinite sum from `n = 0`. */
        asInfiniteRangeSum() {
            const unwrap = (n) => {
                while (n instanceof LeanParenthesis) n = n.arg;
                return n;
            };
            const isInf = (n) => {
                n = unwrap(n);
                if (n instanceof LeanToken) return n.text === '∞';
                if (n instanceof LeanPlus) {
                    const arg = unwrap(n.arg);
                    return arg instanceof LeanToken && arg.text === '∞';
                }
                return false;
            };
            const isRangeFn = (fn) => {
                fn = unwrap(fn);
                if (fn instanceof LeanToken) return fn.text === 'range';
                return fn instanceof LeanProperty && fn.rhs instanceof LeanToken && fn.rhs.text === 'range';
            };
            const isRangeOf = (node, n) => {
                node = unwrap(node);
                if (!(node instanceof LeanArgsSpaceSeparated) || node.args.length !== 2) return false;
                const arg = unwrap(node.args[1]);
                return isRangeFn(node.args[0]) && arg instanceof LeanToken && n instanceof LeanToken && arg.text === n.text;
            };
            const bound = unwrap(this.bound);
            if (!(bound instanceof Lean_rightarrow) || !isInf(bound.rhs)) return null;
            const nLim = unwrap(bound.lhs);
            if (!(nLim instanceof LeanToken)) return null;
            const sum = unwrap(this.scope);
            if (!(sum instanceof Lean_sum)) return null;
            const mem = unwrap(sum.bound);
            if (!(mem instanceof Lean_in) || !isRangeOf(mem.rhs, nLim)) return null;
            return {index: mem.lhs, body: sum.scope};
        }
        latexFormat() {
            if (this.asInfiniteRangeSum()) return '\\sum\\limits_{%s=0}^{\\infty} {%s}';
            return `${this.command}\\limits_{%s} {%s}`;
        }
        latexArgs(syntax) {
            const inf = this.asInfiniteRangeSum();
            if (inf) return [inf.index.toLatex(syntax), inf.body.toLatex(syntax)];
            return super.latexArgs(syntax);
        }
        get operator() {
            return 'lim';
        }
        get stack_priority() {
            if (this.scope) return 67;
            return LeanColon.input_priority - 1;
        }
        strFormat() {
            const sep = this.sep();
            if (this.args.length === 1) return `${this.operator} [%s]`;
            return `${this.operator} [%s]${sep}%s`;
        }
    }

    class Lean_prod extends LeanBigOperator {
        static input_priority = 67;
        /** Mathlib parses big-operator bodies at precedence 67: `∑ i ∈ s, f i + c` is `(∑ i ∈ s, f i) + c`.
         *  Only operators below 67 (`+`/`-`/`++`/`∪`, input 65) close the body; postfix `²` (input 66) stays inside. */
        get stack_priority() {
            return this.scope ? LeanAdd.input_priority : super.stack_priority;
        }
        get baseOperator() {
            return '∏';
        }
    }

    class Lean_int extends LeanBigOperator {
        static input_priority = 60;
        get baseOperator() {
            return '∫';
        }

        binderVar() {
            let b = this.bound;
            if (b instanceof LeanArgsSpaceSeparated) b = b.args[0];
            if (b instanceof LeanParenthesis) b = b.arg;
            if (b instanceof LeanColon) b = b.lhs;
            return b;
        }

        /** Domain after `in`, if any (e.g. `a..b` or `Ioc a b`). */
        intDomain() {
            const b = this.bound;
            if (b instanceof LeanArgsSpaceSeparated) {
                const inNode = b.args.find((a) => a instanceof LeanIn);
                return inNode ? inNode.arg : null;
            }
            return null;
        }

        /**
         * `∫ ω, f ω\n    ∂μ` — a continuation line starting with `∂` supplies the measure of the innermost
         * enclosing integral whose integrand holds `leaf` and has no measure yet. The integrand becomes
         * `LeanArgsIndented(integrand, [∂…])` so the line break survives.
         * @returns {LeanCaret | null}
         */
        static continueMeasure(leaf, indent) {
            for (let child = leaf, p = leaf.parent; p; child = p, p = p.parent) {
                if (!(p instanceof Lean_int)) continue;
                if (p.scope !== child || child instanceof LeanCaret || p.measurePartial()) continue;
                const caret = new LeanCaret(indent, child.level);
                const nl = new LeanArgsNewLineSeparated([caret], indent, child.level);
                p.scope = new LeanArgsIndented(child, nl, p.indent, child.level);
                return caret;
            }
            return null;
        }

        measurePartial() {
            const s = this.scope;
            if (s instanceof LeanArgsIndented && s.rhs instanceof LeanArgsNewLineSeparated) {
                const rest = s.rhs.args.filter((a) => !(a instanceof LeanCaret));
                return rest.length === 1 && rest[0] instanceof Lean_partial ? rest[0] : null;
            }
            if (s instanceof LeanArgsSpaceSeparated) {
                for (let i = s.args.length - 1; i >= 0; i--) {
                    if (s.args[i] instanceof LeanCaret) continue;
                    return s.args[i] instanceof Lean_partial ? s.args[i] : null;
                }
                return null;
            }
            if (s != null && s.rhs instanceof LeanArgsSpaceSeparated) {
                const args = s.rhs.args;
                for (let i = args.length - 1; i >= 0; i--) {
                    if (args[i] instanceof LeanCaret) continue;
                    return args[i] instanceof Lean_partial ? args[i] : null;
                }
            }
            if (s instanceof Lean_int) {
                const innerPartial = s.measurePartial();
                if (!innerPartial) return null;
                const a = innerPartial.arg;
                if (a instanceof LeanArgsSpaceSeparated) {
                    for (let i = a.args.length - 1; i >= 0; i--) {
                        if (a.args[i] instanceof LeanCaret) continue;
                        return a.args[i] instanceof Lean_partial ? a.args[i] : null;
                    }
                }
                return null;
            }
            return null;
        }

        integrandLatex(syntax, partial) {
            if (!partial) return this.scope ? this.scope.toLatex(syntax) : '';
            if (this.scope instanceof LeanArgsIndented && this.scope.rhs instanceof LeanArgsNewLineSeparated &&
                this.scope.rhs.args.includes(partial))
                return this.scope.lhs.toLatex(syntax);
            if (this.scope instanceof LeanArgsSpaceSeparated) {
                const args = this.scope.args
                    .filter((a) => a !== partial && !(a instanceof LeanCaret));
                return args.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
            }
            // Binary operator scope (e.g. `c • f x ∂μ`): partial is in scope.rhs
            if (this.scope != null && this.scope.rhs instanceof LeanArgsSpaceSeparated &&
                this.scope.rhs.args.includes(partial)) {
                const filteredRhs = this.scope.rhs.args
                    .filter((a) => a !== partial && !(a instanceof LeanCaret));
                const lhsLatex = this.scope.lhs.toLatex(syntax);
                const rhsLatex = filteredRhs.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
                const op = this.scope.command ?? this.scope.operator;
                return `${lhsLatex} ${op} ${rhsLatex}`;
            }
            return this.scope.toLatex(syntax);
        }

        latexFormat() {
            const op = this.superscript
                ? `\\int^{${this.superscript}}`
                : '\\int';
            const diff = this.measurePartial() ? '\\partial' : '\\mathrm{d}';
            const tail = `{\\color{blue}${diff}}{%s}`;
            const dom = this.intDomain();
            if (dom instanceof LeanUpto) return `${op}\\limits_{%s}^{%s} %s\\, ${tail}`;
            if (dom != null) return `${op}\\limits_{%s} %s\\, ${tail}`;
            return `${op} %s\\, ${tail}`;
        }

        latexArgs(syntax) {
            const partial = this.measurePartial();
            const body = this.integrandLatex(syntax, partial);
            const v = this.binderVar();
            // `∂μ` names the measure: show it rather than the bound variable
            // (which already appears in the integrand).
            const tail = partial
                ? partial.arg.toLatex(syntax)
                : v && !(v instanceof LeanCaret)
                    ? v.toLatex(syntax)
                    : '';
            const dom = this.intDomain();
            if (dom instanceof LeanUpto) {
                return [dom.lhs.toLatex(syntax), dom.rhs.toLatex(syntax), body, tail];
            }
            if (dom != null) return [dom.toLatex(syntax), body, tail];
            return [body, tail];
        }
    }

    class Lean_bigcap extends LeanBigOperator {
        static input_priority = 60;
        get baseOperator() {
            return '⋂';
        }
    }

    class Lean_bigcup extends LeanBigOperator {
        static input_priority = 60;
        get baseOperator() {
            return '⋃';
        }
    }

    class LeanInf extends LeanBigOperator {
        static input_priority = 60;
        get baseOperator() {
            return '⨅';
        }
        get command() {
            return '\\mathop{⨅}';
        }
    }

    class LeanSup extends LeanBigOperator {
        static input_priority = 60;
        get baseOperator() {
            return '⨆';
        }
        get command() {
            // katex doesn't support `\bigsqcup`
            return '⨆';
        }
    }

    class LeanStack extends LeanBigOperator {
        static input_priority = 52;

        get operator() {
            return 'Stack';
        }

        get command() {
            return 'Stack';
        }

        get stack_priority() {
            if (this.scope) return LeanRelational.input_priority;
            return 28;
        }

        is_indented() {
            const {parent} = this;
            return parent instanceof LeanStatements || (parent instanceof LeanIte && !parent.inline) || parent instanceof LeanArgsNewLineSeparated || parent instanceof LeanArgsCommaNewLineSeparated;
        }

        latexArgs(syntax) {
            if (syntax)
                syntax[this.constructor.name] = true;
            return super.latexArgs(syntax);
        }

        latexFormat() {
            return '\\left[{%s}\\right]{%s}';
        }

        push_args_indented(_indent, _newlineCount, _functionCall = true) {}

        strFormat() {
            var sep = this.sep();
            return `[%s]${sep}%s`;
        }
    }


    return {
        Lean_sum,
        Lean_lim,
        Lean_prod,
        Lean_int,
        Lean_bigcap,
        Lean_bigcup,
        LeanInf,
        LeanSup,
        LeanStack,
    };
}
