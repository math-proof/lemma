/**
 * Big operators: `LeanBigOperator` and `∑` / `lim` / `∏` / `∫` /
 * `∂` / `∇` / `𝔼` / `ℙ` / `𝕍𝕒𝕣` / `max` / `min` / `sup` / `inf` /
 * `max⁻¹` / `min⁻¹` / `⋂` / `⋃` / `⨅` / `⨆` / `Stack`.
 *
 * Quantifiers stay in `quantifier.js` (they extend `LeanBigOperator`).
 * `LeanAdd` is read for `input_priority` and `instanceof`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { strStmt } from './utility.js';
import { pathUniqKeepEmpty, pathStripTrailingHoles } from './pathChoices.js';
import { LeanArgs } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanBigOperator extends LeanArgs {
    static { this.register(); }

    superscript = null;

    get baseOperator() {
        throw new Error(`${this.constructor.name} must define baseOperator or override operator`);
    }

    get operator() {
        return this.superscript ? `${this.baseOperator}${this.superscript}` : this.baseOperator;
    }

    /**
     * @param {Lean} bound
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(bound, indent, level, parent = null) {
        super([bound], indent, level, parent);
    }

    get bound() {
        return this.args[0];
    }
    set bound(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get scope() {
        return this.args[1] ?? null;
    }
    set scope(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    get stack_priority() {
        if (this.scope) return L.LeanRelational.input_priority;
        return L.LeanColon.input_priority - 1;
    }

    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanArgsCommaNewLineSeparated ||
            parent instanceof L.LeanArgsNewLineSeparated ||
            parent instanceof L.LeanStatements ||
            (parent instanceof L.LeanIte && !parent.inline);
    }

    sep() {
        if (this.scope instanceof L.LeanArgsNewLineSeparated) return "\n";
        return ' ';
    }

    set_line(line) {
        this.line = line;
        line = this.bound.set_line(line);
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.scope.set_line(line);
    }

    strFormat() {
        const op = this.operator;
        if (this.args.length === 1) return `${op} %s,`;
        var sep = this.sep();
        return `${op} %s,${sep}%s`;
    }

    /** `i : Fin k` in ∑/∏ → subscript `i < k`. */
    finRangeBound() {
        const bound = this.bound;
        if (!(bound instanceof L.LeanColon)) return null;
        let ty = bound.rhs;
        if (ty instanceof L.LeanParenthesis) ty = ty.arg;
        if (ty instanceof L.LeanArgsSpaceSeparated && ty.args.length === 2) {
            const [fn, n] = ty.args;
            if (fn instanceof L.LeanToken && fn.text === 'Fin')
                return [bound.lhs, n];
        }
        return null;
    }

    /**
     * `∑/∏ i ∈ Finset.range n, f` / `∑/∏ i ∈ range n, f` → `[i, n]`, rendered as `\\sum_{i < n}`.
     * Parallel to `i : Fin n` → `i < n` (Finset.range n = {0, …, n − 1}).
     */
    rangeBound() {
        if (!(this instanceof Lean_sum || this instanceof Lean_prod)) return null;
        const peel = (n) => (n instanceof L.LeanParenthesis ? n.arg : n);
        const bound = this.bound;
        if (!(bound instanceof L.Lean_in)) return null;
        const set = peel(bound.rhs);
        if (!(set instanceof L.LeanArgsSpaceSeparated) || set.args.length !== 2) return null;
        const fn = peel(set.args[0]);
        const isRange =
            (fn instanceof L.LeanToken && fn.text === 'range') ||
            (fn instanceof L.LeanProperty &&
                fn.rhs instanceof L.LeanToken && fn.rhs.text === 'range' &&
                fn.lhs instanceof L.LeanToken && fn.lhs.text === 'Finset');
        if (!isRange) return null;
        return [bound.lhs, peel(set.args[1])];
    }


    /**
     * `∑/∏ i ∈ Finset.range (e + 1), f` / `∑/∏ i ∈ range (e + 1), f` → `[i, e]`,
     * rendered as `\sum_{i=0}^{e}` (same closed-interval style as `icoClosedBound`).
     */
    rangeClosedBound() {
        if (!(this instanceof Lean_sum || this instanceof Lean_prod)) return null;
        const peel = (n) => (n instanceof L.LeanParenthesis ? n.arg : n);
        const bound = this.bound;
        if (!(bound instanceof L.Lean_in)) return null;
        const set = peel(bound.rhs);
        if (!(set instanceof L.LeanArgsSpaceSeparated) || set.args.length !== 2) return null;
        const fn = peel(set.args[0]);
        const isRange =
            (fn instanceof L.LeanToken && fn.text === 'range') ||
            (fn instanceof L.LeanProperty &&
                fn.rhs instanceof L.LeanToken && fn.rhs.text === 'range' &&
                fn.lhs instanceof L.LeanToken && fn.lhs.text === 'Finset');
        if (!isRange) return null;
        const top = peel(set.args[1]);
        if (!(top instanceof L.LeanAdd) || !(top.rhs instanceof L.LeanToken) || top.rhs.text !== '1')
            return null;
        return [bound.lhs, top.lhs];
    }

    /**
     * `∑/∏ i ∈ Finset.Iio k, f` / `∑/∏ i ∈ Iio k, f` → `[i, k]`, rendered as `\\sum_{i < k}`.
     * Without this, membership falls through to interval TeX `(-\\infty, k)`.
     */
    iioBound() {
        if (!(this instanceof Lean_sum || this instanceof Lean_prod)) return null;
        const peel = (n) => (n instanceof L.LeanParenthesis ? n.arg : n);
        const bound = this.bound;
        if (!(bound instanceof L.Lean_in)) return null;
        const set = peel(bound.rhs);
        if (!(set instanceof L.LeanArgsSpaceSeparated) || set.args.length !== 2) return null;
        const fn = peel(set.args[0]);
        const isIio =
            (fn instanceof L.LeanToken && fn.text === 'Iio') ||
            (fn instanceof L.LeanProperty &&
                fn.rhs instanceof L.LeanToken && fn.rhs.text === 'Iio' &&
                fn.lhs instanceof L.LeanToken && fn.lhs.text === 'Finset');
        if (!isIio) return null;
        return [bound.lhs, peel(set.args[1])];
    }

    /**
     * `∑/∏ i ∈ Finset.Iic k, f` / `∑/∏ i ∈ Iic k, f` → `[i, k]`, rendered as `\\sum_{i \\le k}`.
     * Without this, membership falls through to interval TeX `(-\\infty, k]`.
     */
    iicBound() {
        if (!(this instanceof Lean_sum || this instanceof Lean_prod)) return null;
        const peel = (n) => (n instanceof L.LeanParenthesis ? n.arg : n);
        const bound = this.bound;
        if (!(bound instanceof L.Lean_in)) return null;
        const set = peel(bound.rhs);
        if (!(set instanceof L.LeanArgsSpaceSeparated) || set.args.length !== 2) return null;
        const fn = peel(set.args[0]);
        const isIic =
            (fn instanceof L.LeanToken && fn.text === 'Iic') ||
            (fn instanceof L.LeanProperty &&
                fn.rhs instanceof L.LeanToken && fn.rhs.text === 'Iic' &&
                fn.lhs instanceof L.LeanToken && fn.lhs.text === 'Finset');
        if (!isIic) return null;
        return [bound.lhs, peel(set.args[1])];
    }

    /**
     * `∑/∏ i ∈ Finset.Ico a (b + 1), f` → `[i, a, b]`, rendered as `\\prod_{i=a}^{b}`.
     */
    icoClosedBound() {
        if (!(this instanceof Lean_sum || this instanceof Lean_prod)) return null;
        const peel = (n) => (n instanceof L.LeanParenthesis ? n.arg : n);
        const bound = this.bound;
        if (!(bound instanceof L.Lean_in)) return null;
        const set = peel(bound.rhs);
        if (!(set instanceof L.LeanArgsSpaceSeparated) || set.args.length !== 3) return null;
        const fn = set.args[0];
        const isIco =
            (fn instanceof L.LeanToken && fn.text === 'Ico') ||
            (fn instanceof L.LeanProperty &&
                fn.rhs instanceof L.LeanToken && fn.rhs.text === 'Ico' &&
                fn.lhs instanceof L.LeanToken && fn.lhs.text === 'Finset');
        if (!isIco) return null;
        const top = peel(set.args[2]);
        if (!(top instanceof L.LeanAdd) || !(top.rhs instanceof L.LeanToken) || top.rhs.text !== '1')
            return null;
        return [bound.lhs, peel(set.args[1]), top.lhs];
    }

    latexFormat() {
        if (!(this instanceof L.LeanQuantifier) && this.finRangeBound())
            return `${this.command}\\limits_{%s < %s} {%s}`;
        if (!(this instanceof L.LeanQuantifier) && !this.superscript && this.rangeClosedBound())
            return `${this.command}\\limits_{%s=0}^{%s} {%s}`;
        if (!(this instanceof L.LeanQuantifier) && !this.superscript && this.rangeBound())
            return `${this.command}\\limits_{%s < %s} {%s}`;
        if (!(this instanceof L.LeanQuantifier) && !this.superscript && this.iioBound())
            return `${this.command}\\limits_{%s < %s} {%s}`;
        if (!(this instanceof L.LeanQuantifier) && !this.superscript && this.iicBound())
            return `${this.command}\\limits_{%s \\le %s} {%s}`;
        if (!this.superscript && this.icoClosedBound())
            return `${this.command}\\limits_{%s=%s}^{%s} {%s}`;
        const cmd = this.command;
        return `${cmd}\\limits_{\\substack{%s}} {%s}`;
    }

    latexArgs(syntax) {
        if (!(this instanceof L.LeanQuantifier)) {
            const fin = this.finRangeBound();
            if (fin) {
                const [i, n] = fin;
                const peel = (arg) => L.LeanParenthesis.peelLatex(arg);
                return [i.toLatex(syntax), peel(n).toLatex(syntax), this.scope.toLatex(syntax)];
            }
            const rngClosed = !this.superscript && this.rangeClosedBound();
            if (rngClosed) {
                const [i, e] = rngClosed;
                return [i.toLatex(syntax), e.toLatex(syntax), this.scope.toLatex(syntax)];
            }
            const rng = !this.superscript && this.rangeBound();
            if (rng) {
                const [i, n] = rng;
                const peel = (arg) => L.LeanParenthesis.peelLatex(arg);
                return [i.toLatex(syntax), peel(n).toLatex(syntax), this.scope.toLatex(syntax)];
            }
            const iio = !this.superscript && this.iioBound();
            if (iio) {
                const [i, k] = iio;
                const peel = (arg) => L.LeanParenthesis.peelLatex(arg);
                return [i.toLatex(syntax), peel(k).toLatex(syntax), this.scope.toLatex(syntax)];
            }
            const iic = !this.superscript && this.iicBound();
            if (iic) {
                const [i, k] = iic;
                const peel = (arg) => L.LeanParenthesis.peelLatex(arg);
                return [i.toLatex(syntax), peel(k).toLatex(syntax), this.scope.toLatex(syntax)];
            }
            const ico = !this.superscript && this.icoClosedBound();
            if (ico) {
                const [i, a, b] = ico;
                return [i.toLatex(syntax), a.toLatex(syntax), b.toLatex(syntax), this.scope.toLatex(syntax)];
            }
        }
        return super.latexArgs(syntax);
    }

    toJSON() {
        return {
            [this.func]: super.toJSON(),
        };
    }

    /**
     * `∫ x : ℝ in a..b, f x` — the `in` domain modifier attaches to the bound as a sibling:
     * bound becomes `LeanArgsSpaceSeparated [oldBound, LeanIn domain]`.
     */
    insert(caret, func, type) {
        if (func === 'LeanIn' && type === 'modifier' && caret === this.bound && this.scope == null) {
            const c = new L.LeanCaret(this.indent, caret.level);
            const domain = new L.LeanIn(c, this.indent, caret.level);
            this.bound = new L.LeanArgsSpaceSeparated([caret, domain], this.indent, caret.level);
            return c;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_comma(caret) {
        if (caret === this.bound) {
            const c = new L.LeanCaret(this.indent, caret.level);
            this.scope = c;
            return c;
        }
        // `⟨∑ s, ‖x s‖, 1⟩` — a comma after a finished body closes the big operator.
        if (caret === this.scope && !(caret instanceof L.LeanCaret) && this.parent)
            return this.parent.insert_comma(this);
        throw new Error(`${this.constructor.name}.insert_comma: unexpected`);
    }

    insert_if(caret) {
        if (this.scope === caret && caret instanceof L.LeanCaret) {
            this.scope = new L.LeanIte([caret], caret.indent, caret.level);
            return caret;
        }
        throw new Error(`${this.constructor.name}.insert_if: unexpected`);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.scope) {
            if (caret instanceof L.LeanCaret) {
                caret.indent = indent;
                const nl = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
                caret = nl.push_newlines(newline_count - 1);
                this.scope = nl;
                return caret;
            }
            else if (indent > this.indent) {
                // Continue trailing app in scope across newline under forall/exists
                // (HasLaw (fun...) then indented (Measure.pi...)).
                if (caret instanceof L.LeanArgsSpaceSeparated) {
                    const cont = caret.push_args_indented(indent, newline_count);
                    if (cont) return cont;
                }
                // a more-indented line continues the scope (e.g. a dangling
                // operator); a dedent closes this statement entirely — let the
                // enclosing statement list handle it instead of absorbing it
                const $new = this.push_args_indented(indent, newline_count);
                if ($new) return $new;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }
}

export class Lean_sum extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 67;
    /** Mathlib parses big-operator bodies at precedence 67: `∑ i ∈ s, f i + c` is `(∑ i ∈ s, f i) + c`.
     *  Only operators below 67 (`+`/`-`/`++`/`∪`, input 65) close the body; postfix `²` (input 66) stays inside. */
    get stack_priority() {
        return this.scope ? L.LeanAdd.input_priority : super.stack_priority;
    }
    get baseOperator() {
        return '∑';
    }

    /** Peel `(∑ …)` so nested display stacking still sees the inner sum. */
    static peelSum(n) {
        while (n instanceof L.LeanParenthesis) n = n.arg;
        return n;
    }

    /**
     * Display-only: `∑ i, ∑ j, body` → one `∑` with stacked limits.
     * Returns `{chain, body}` for a run of plain (non-`∑'`) nested sums, else null.
     */
    nestedSumChain() {
        if (this.superscript) return null;
        const chain = [this];
        let cur = this;
        while (true) {
            const next = Lean_sum.peelSum(cur.scope);
            if (!(next instanceof Lean_sum) || next.superscript) break;
            chain.push(next);
            cur = next;
        }
        if (chain.length < 2) return null;
        return {chain, body: cur.scope};
    }

    /**
     * Limit fragment for stacked nested sums (no body). Prefers the same sugar as
     * single-sum `latexFormat` (`i < n`, `i ≤ k`, …); upper-limit forms become
     * closed inequalities so they fit under `\substack`.
     */
    sumLimitLatex(syntax) {
        const peel = (arg) => L.LeanParenthesis.peelLatex(arg);
        const fin = this.finRangeBound();
        if (fin) {
            const [i, n] = fin;
            return `${i.toLatex(syntax)} < ${peel(n).toLatex(syntax)}`;
        }
        const rngClosed = !this.superscript && this.rangeClosedBound();
        if (rngClosed) {
            const [i, e] = rngClosed;
            return `0 \\le ${i.toLatex(syntax)} \\le ${e.toLatex(syntax)}`;
        }
        const rng = !this.superscript && this.rangeBound();
        if (rng) {
            const [i, n] = rng;
            return `${i.toLatex(syntax)} < ${peel(n).toLatex(syntax)}`;
        }
        const iio = !this.superscript && this.iioBound();
        if (iio) {
            const [i, k] = iio;
            return `${i.toLatex(syntax)} < ${peel(k).toLatex(syntax)}`;
        }
        const iic = !this.superscript && this.iicBound();
        if (iic) {
            const [i, k] = iic;
            return `${i.toLatex(syntax)} \\le ${peel(k).toLatex(syntax)}`;
        }
        const ico = !this.superscript && this.icoClosedBound();
        if (ico) {
            const [i, a, b] = ico;
            return `${a.toLatex(syntax)} \\le ${i.toLatex(syntax)} \\le ${b.toLatex(syntax)}`;
        }
        // Default / membership binder: same content that single-sum puts in `\substack`.
        return this.bound ? this.bound.toLatex(syntax) : '';
    }

    /**
     * `∑ «\sf{y}»[t], f` / `∑ «\sf{y}» t, f`: a bound variable is never red, so the index and the
     * body's `y[t]` / `y t` that stands for the bound value (`y[t] = «\sf{y}»[t]` / `y t = «\sf{y}» t`
     * inside `ℙ[π](…)`) are drawn in the normal colour.
     */
    latexArgs(syntax) {
        const bnd = this.bound;
        if (!this.scope) return super.latexArgs(syntax);
        let quote = null;
        let keyApp = '';
        let keyGet = '';
        if (
            bnd instanceof L.LeanArgsSpaceSeparated && bnd.args.length === 2 &&
            bnd.args[0] instanceof L.LeanDoubleAngleQuotation
        ) {
            quote = bnd.args[0];
            keyApp = strStmt(bnd).trim(); // `«\sf{y}» t`
            keyGet = `${strStmt(bnd.args[0]).trim()}[${strStmt(bnd.args[1]).trim()}]`; // `«\sf{y}»[t]`
        } else if (
            bnd instanceof L.LeanGetElem &&
            bnd.args[0] instanceof L.LeanDoubleAngleQuotation
        ) {
            quote = bnd.args[0];
            keyGet = strStmt(bnd).trim(); // `«\sf{y}»[t]`
            keyApp = `${strStmt(bnd.args[0]).trim()} ${strStmt(bnd.args[1]).trim()}`; // `«\sf{y}» t`
        }
        if (quote) {
            const base = quote.boundValueLhs();
            if (base instanceof L.LeanToken) {
                const seen = new Set();
                const walk = (n) => {
                    if (!n || typeof n !== 'object' || seen.has(n)) return;
                    seen.add(n);
                    if (n instanceof L.LeanEq) {
                        const rhs = strStmt(n.rhs).trim();
                        if (rhs === keyApp || rhs === keyGet) {
                            let l = n.lhs;
                            while (l instanceof L.LeanParenthesis) l = l.arg;
                            if (l instanceof L.LeanArgsSpaceSeparated) l = l.args[0];
                            if (l instanceof L.LeanGetElem) l = l.args[0];
                            if (l instanceof L.LeanToken && l.text === base.text) l.kwargs.neverRed = true;
                        }
                    }
                    if (Array.isArray(n.args)) n.args.forEach(walk);
                };
                walk(this.scope);
                base.kwargs.neverRed = true;
            }
        }
        const nested = this.nestedSumChain();
        if (nested) {
            // Inner binder first (evaluation / substack order), then outer.
            const limits = [...nested.chain].reverse().map((s) => s.sumLimitLatex(syntax)).join(' \\\\ ');
            return [limits, nested.body.toLatex(syntax)];
        }
        return super.latexArgs(syntax);
    }
    latexFormat() {
        if (this.nestedSumChain())
            return `\\sum\\limits_{\\substack{%s}} {%s}`;
        if (!this.superscript) return super.latexFormat();
        const op = `\\mathop{${this.command}\\nolimits${this.superscript}}`;
        if (this.rangeClosedBound())
            return `${op}\\limits_{%s=0}^{%s} {%s}`;
        if (this.finRangeBound() || this.rangeBound() || this.iioBound())
            return `${op}\\limits_{%s < %s} {%s}`;
        if (this.iicBound())
            return `${op}\\limits_{%s \\le %s} {%s}`;
        return `${op}\\limits_{\\substack{%s}} {%s}`;
    }
}

export class Lean_lim extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 67;
    get command() {
        return '\\lim';
    }
    /** `lim [N → ∞] ∑ n ∈ range N, e` → infinite sum from `n = 0`. */
    asInfiniteRangeSum() {
        const unwrap = (n) => {
            while (n instanceof L.LeanParenthesis) n = n.arg;
            return n;
        };
        const isInf = (n) => {
            n = unwrap(n);
            if (n instanceof L.LeanToken) return n.text === '∞';
            if (n instanceof L.LeanPlus) {
                const arg = unwrap(n.arg);
                return arg instanceof L.LeanToken && arg.text === '∞';
            }
            return false;
        };
        const isRangeFn = (fn) => {
            fn = unwrap(fn);
            if (fn instanceof L.LeanToken) return fn.text === 'range';
            return fn instanceof L.LeanProperty && fn.rhs instanceof L.LeanToken && fn.rhs.text === 'range';
        };
        const isRangeOf = (node, n) => {
            node = unwrap(node);
            if (!(node instanceof L.LeanArgsSpaceSeparated) || node.args.length !== 2) return false;
            const arg = unwrap(node.args[1]);
            return isRangeFn(node.args[0]) && arg instanceof L.LeanToken && n instanceof L.LeanToken && arg.text === n.text;
        };
        const bound = unwrap(this.bound);
        if (!(bound instanceof L.Lean_rightarrow) || !isInf(bound.rhs)) return null;
        const nLim = unwrap(bound.lhs);
        if (!(nLim instanceof L.LeanToken)) return null;
        const sum = unwrap(this.scope);
        if (!(sum instanceof Lean_sum)) return null;
        const mem = unwrap(sum.bound);
        if (!(mem instanceof L.Lean_in) || !isRangeOf(mem.rhs, nLim)) return null;
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
        return L.LeanColon.input_priority - 1;
    }
    strFormat() {
        const sep = this.sep();
        // Glued like `sup[…]`. A space (`lim […]`) parses as `Filter.lim` applied to a `List`.
        if (this.args.length === 1) return `${this.operator}[%s]`;
        return `${this.operator}[%s]${sep}%s`;
    }
}

export class Lean_prod extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 67;
    /** Mathlib parses big-operator bodies at precedence 67: `∑ i ∈ s, f i + c` is `(∑ i ∈ s, f i) + c`.
     *  Only operators below 67 (`+`/`-`/`++`/`∪`, input 65) close the body; postfix `²` (input 66) stays inside. */
    get stack_priority() {
        return this.scope ? L.LeanAdd.input_priority : super.stack_priority;
    }
    get baseOperator() {
        return '∏';
    }
}

export class Lean_int extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 60;
    get baseOperator() {
        return '∫';
    }

    binderVar() {
        let b = this.bound;
        if (b instanceof L.LeanArgsSpaceSeparated) b = b.args[0];
        if (b instanceof L.LeanParenthesis) b = b.arg;
        if (b instanceof L.LeanColon) b = b.lhs;
        return b;
    }

    /** Domain after `in`, if any (e.g. `a..b` or `Ioc a b`). */
    intDomain() {
        const b = this.bound;
        if (b instanceof L.LeanArgsSpaceSeparated) {
            const inNode = b.args.find((a) => a instanceof L.LeanIn);
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
            if (p.scope !== child || child instanceof L.LeanCaret || p.measurePartial()) continue;
            const caret = new L.LeanCaret(indent, child.level);
            const nl = new L.LeanArgsNewLineSeparated([caret], indent, child.level);
            p.scope = new L.LeanArgsIndented(child, nl, p.indent, child.level);
            return caret;
        }
        return null;
    }

    measurePartial() {
        const s = this.scope;
        if (s instanceof L.LeanArgsIndented && s.rhs instanceof L.LeanArgsNewLineSeparated) {
            const rest = s.rhs.args.filter((a) => !(a instanceof L.LeanCaret));
            if (rest.length === 1 && rest[0] instanceof L.Lean_partial) return rest[0];
            // Integrand line may trail with partial under Indented.lhs.
            const lhsPartial = Lean_int.trailingPartial(s.lhs);
            if (lhsPartial) return lhsPartial;
            if (rest.length) {
                const rhsPartial = Lean_int.trailingPartial(rest[rest.length - 1]);
                if (rhsPartial) return rhsPartial;
            }
            return null;
        }
        // Binder newline then `f partial-mu` on the next line (NewLineSeparated).
        if (s instanceof L.LeanArgsNewLineSeparated) {
            for (let i = s.args.length - 1; i >= 0; i--) {
                if (s.args[i] instanceof L.LeanCaret) continue;
                return Lean_int.trailingPartial(s.args[i]);
            }
            return null;
        }
        if (s instanceof L.LeanArgsSpaceSeparated) {
            return Lean_int.trailingPartial(s);
        }
        if (s != null && s.rhs instanceof L.LeanArgsSpaceSeparated) {
            return Lean_int.trailingPartial(s);
        }
        if (s instanceof Lean_int) {
            const innerPartial = s.measurePartial();
            if (!innerPartial) return null;
            const a = innerPartial.arg;
            if (a instanceof L.LeanArgsSpaceSeparated) {
                return Lean_int.trailingPartial(a);
            }
            return null;
        }
        // Nested ∑/∏/•/… under the integrand (right-spine walk).
        return Lean_int.trailingPartial(s);
    }

    /**
     * Trailing measure partial along the integrand right spine.
     * Walks SpaceSeparated / NewLineSeparated tails, binary rhs, Indented, and big-op scope
     * so `∫ ω, ∑ t, f • ∇ … ∂μ` still finds `∂μ` nested under ∑ / •.
     */
    static trailingPartial(node) {
        if (node == null || node instanceof L.LeanCaret) return null;
        if (node instanceof L.Lean_partial) return node;
        if (node instanceof L.LeanArgsSpaceSeparated ||
            node instanceof L.LeanArgsNewLineSeparated ||
            node instanceof L.LeanArgsCommaNewLineSeparated) {
            for (let i = node.args.length - 1; i >= 0; i--) {
                if (node.args[i] instanceof L.LeanCaret) continue;
                return Lean_int.trailingPartial(node.args[i]);
            }
            return null;
        }
        if (node instanceof L.LeanArgsIndented) {
            return Lean_int.trailingPartial(node.rhs) || Lean_int.trailingPartial(node.lhs);
        }
        // Binary / relational: measure trails on the rhs spine (`f • ∇ … ∂μ`).
        if (node.rhs != null) {
            const fromRhs = Lean_int.trailingPartial(node.rhs);
            if (fromRhs) return fromRhs;
        }
        // Nested big-op body (`∑` / `∏` / …) may hold the integral measure.
        if (node.scope != null) {
            return Lean_int.trailingPartial(node.scope);
        }
        return null;
    }

    integrandLatex(syntax, partial) {
        if (!partial) return this.scope ? this.scope.toLatex(syntax) : '';
        if (this.scope instanceof L.LeanArgsIndented && this.scope.rhs instanceof L.LeanArgsNewLineSeparated &&
            this.scope.rhs.args.includes(partial))
            return this.scope.lhs.toLatex(syntax);
        // Indented with partial trailing the lhs line: strip from lhs, keep rhs lines.
        if (this.scope instanceof L.LeanArgsIndented && Lean_int.trailingPartial(this.scope.lhs) === partial) {
            const lhs = this.stripPartialLatex(this.scope.lhs, partial, syntax);
            const rhs = this.scope.rhs ? this.scope.rhs.toLatex(syntax) : '';
            return rhs ? `${lhs}${this.scope.sep()}${rhs}` : lhs;
        }
        if (this.scope instanceof L.LeanArgsSpaceSeparated) {
            const args = this.scope.args
                .filter((a) => a !== partial && !(a instanceof L.LeanCaret));
            return args.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
        }
        // Binary operator scope (e.g. `c • f x partial-mu`): partial is in scope.rhs
        if (this.scope != null && this.scope.rhs instanceof L.LeanArgsSpaceSeparated &&
            this.scope.rhs.args.includes(partial)) {
            const filteredRhs = this.scope.rhs.args
                .filter((a) => a !== partial && !(a instanceof L.LeanCaret));
            const lhsLatex = this.scope.lhs.toLatex(syntax);
            const rhsLatex = filteredRhs.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
            const op = this.scope.command ?? this.scope.operator;
            return `${lhsLatex} ${op} ${rhsLatex}`;
        }
        // Binder newline then `f partial-mu`: strip trailing partial from last line.
        if (this.scope instanceof L.LeanArgsNewLineSeparated) {
            const parts = [];
            for (const a of this.scope.args) {
                if (a instanceof L.LeanCaret) continue;
                if (a === partial) continue;
                const stripped = this.stripPartialLatex(a, partial, syntax);
                if (stripped != null && stripped !== '') parts.push(stripped);
            }
            if (parts.length <= 1) return parts[0] ?? '';
            const stmt = parts.map((p) => `&{${p}}&& `).join('\\\\\n');
            return `\\begin{aligned}\n${stmt}\n\\end{aligned}`;
        }
        // Deep nesting (e.g. ∫ ∑ … • ∇ … ∂μ): drop partial from its SpaceSeparated parent.
        const parent = partial.parent;
        if (parent instanceof L.LeanArgsSpaceSeparated) {
            const idx = parent.args.indexOf(partial);
            if (idx >= 0) {
                const removed = parent.args.splice(idx, 1)[0];
                try {
                    return this.scope ? this.scope.toLatex(syntax) : '';
                } finally {
                    parent.args.splice(idx, 0, removed);
                }
            }
        }
        return this.scope.toLatex(syntax);
    }

    /** Drop a trailing measure partial from a SpaceSeparated / binary-rhs group for integrand latex. */
    stripPartialLatex(node, partial, syntax) {
        if (node instanceof L.LeanArgsSpaceSeparated && node.args.includes(partial)) {
            const args = node.args.filter((a) => a !== partial && !(a instanceof L.LeanCaret));
            return args.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
        }
        if (node != null && node.rhs instanceof L.LeanArgsSpaceSeparated &&
            node.rhs.args.includes(partial)) {
            const filteredRhs = node.rhs.args
                .filter((a) => a !== partial && !(a instanceof L.LeanCaret));
            const lhsLatex = node.lhs.toLatex(syntax);
            const rhsLatex = filteredRhs.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
            const op = node.command ?? node.operator;
            return `${lhsLatex} ${op} ${rhsLatex}`;
        }
        return node.toLatex(syntax);
    }

    latexFormat() {
        const op = this.superscript
            ? `\\int^{${this.superscript}}`
            : '\\int';
        const partial = this.measurePartial();
        const v = this.binderVar();
        const hasBinder = v && !(v instanceof L.LeanCaret);
        const diff = partial ? '\\partial' : '\\mathrm{d}';
        const tail = `{\\color{blue}${diff}}{%s}`;
        const dom = this.intDomain();
        // Domain forms keep limits + differential (binder or measure).
        if (dom instanceof L.LeanUpto) return `${op}\\limits_{%s}^{%s} %s\\, ${tail}`;
        if (dom != null) return `${op}\\limits_{%s} %s\\, ${tail}`;
        // No domain: show binder as subscript; measure is the only trailing differential.
        if (hasBinder) {
            if (partial) return `${op}_{%s} %s\\, {\\color{blue}\\partial}{%s}`;
            return `${op}_{%s} %s`;
        }
        if (partial) return `${op} %s\\, ${tail}`;
        return `${op} %s`;
    }

    latexArgs(syntax) {
        const partial = this.measurePartial();
        const body = this.integrandLatex(syntax, partial);
        const v = this.binderVar();
        const hasBinder = v && !(v instanceof L.LeanCaret);
        const measureTail = partial ? partial.bound.toLatex(syntax) : '';
        const binderTail = hasBinder ? v.toLatex(syntax) : '';
        const dom = this.intDomain();
        if (dom instanceof L.LeanUpto) {
            const tail = partial ? measureTail : binderTail;
            return [dom.lhs.toLatex(syntax), dom.rhs.toLatex(syntax), body, tail];
        }
        if (dom != null) {
            const tail = partial ? measureTail : binderTail;
            return [dom.toLatex(syntax), body, tail];
        }
        if (hasBinder) {
            if (partial) return [v.toLatex(syntax), body, measureTail];
            return [v.toLatex(syntax), body];
        }
        if (partial) return [body, measureTail];
        return [body];
    }
}

/**
 * `∂[x] body` / `∂[x = x₀] body` (deriv sugar) and measure `∂μ`.
 * Bound+scope like ∑/lim; path token Deriv. Created via insert_unary (so
 * `f x ∂μ` stays a flat SpaceSeparated sibling list).
 */
export class Lean_partial extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 75;

    get baseOperator() {
        return '∂';
    }

    get command() {
        return '\\partial';
    }

    get stack_priority() {
        if (this.scope) return L.LeanAdd.input_priority;
        if (!(this.bound instanceof L.LeanCaret)) return 67;
        return L.LeanColon.input_priority - 1;
    }

    /** Comma is not a binder separator (`∂[t, t]` commas live inside the bracket). */
    insert_comma(caret) {
        if (this.parent) return this.parent.insert_comma(this);
        throw new Error('Lean_partial.insert_comma: unexpected');
    }

    set_line(line) {
        this.line = line;
        line = this.bound.set_line(line);
        if (!this.scope) return line;
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.scope.set_line(line);
    }

    strFormat() {
        if (!this.scope) return `${this.operator}%s`;
        return `${this.operator}[%s]${this.sep()}%s`;
    }

    /**
     * Deriv: bound = index (`x` / `x = x₀` / `t, t`), scope = body.
     * Measure: bound = μ, no scope → null (unary \\partial{μ} latex).
     */
    derivSugar() {
        if (!this.scope) return null;
        const index = this.bound;
        let body;
        if (this.scope instanceof L.LeanArgsSpaceSeparated)
            body = this.scope.args.filter((a) => !(a instanceof L.LeanCaret));
        else if (this.scope instanceof L.LeanCaret)
            body = [];
        else
            body = [this.scope];
        if (index instanceof L.LeanEq && index.lhs instanceof L.LeanToken)
            return {name: index.lhs, point: index.rhs, body};
        return {name: index, point: null, body};
    }

    latexArgs(syntax) {
        const sugar = this.derivSugar();
        if (!sugar) {
            // Measure ∂μ
            return [this.bound.toLatex(syntax)];
        }
        const body = sugar.body.map((a) => {
            let arg = a;
            if (arg instanceof L.LeanParenthesis && arg.arg instanceof L.LeanDiv) arg = arg.arg;
            return arg.toLatex(syntax);
        });
        const name = sugar.name.toLatex(syntax);
        if (!sugar.point) return body.length ? [name, ...body] : [name];
        const point = L.LeanParenthesis.peelLatex(sugar.point);
        return [name, ...body, name, point.toLatex(syntax)];
    }

    latexFormat() {
        const sugar = this.derivSugar();
        if (!sugar) return '\\partial{%s}';
        const body = sugar.body.map(() => '{%s}').join('\\ ');
        const partial = body ? '\\partial_{%s} {' + body + '}' : '\\partial_{%s}';
        if (!sugar.point) return partial;
        return '\\left. ' + partial + ' \\right|_{{%s} = {%s}}';
    }

    /** Path token Deriv (Body t350); bound/scope are holes like ∑. */

    /**
     * Hole-regex: Deriv_ when bound/scope present (Body t350/t351).
     * @param {object} [_opts]
     * @returns {string|null}
     */
    holeRegex(opts = {}) {
        if (this.bound == null && this.scope == null) return null;
        // Hole scope (d[x] u / d[t,t] u): Deriv_. Structured integrand: Deriv_(scopeFrag).
        const scopeFrag = this.scope?.holeRegex?.(opts) ?? null;
        if (scopeFrag == null || scopeFrag === "" || scopeFrag === "_") return "Deriv_";
        return "Deriv_(" + scopeFrag + ")";
    }

    pathChoices(opts = {}) {
        const kid = this.scope ?? this.bound;
        const kids = kid?.pathChoices?.(opts) ?? [''];
        const out = [''];
        for (const k of kids) out.push(k ? 'Deriv' + k : 'Deriv_');
        return pathUniqKeepEmpty(out);
    }
}

/**
 * `∇[θ] body` / `∇[θ = θ₀] body` (binder) and binder-free `∇ J` / `∇ J θ`.
 * Bound+scope like lim/∂. Created via append like ∑/lim.
 */
export class Lean_nabla extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 75;

    get baseOperator() {
        return '∇';
    }

    get command() {
        return '\\nabla';
    }

    get stack_priority() {
        if (this.scope) return L.LeanAdd.input_priority;
        if (!(this.bound instanceof L.LeanCaret)) return 67;
        return L.LeanColon.input_priority - 1;
    }

    insert_comma(caret) {
        if (this.parent) return this.parent.insert_comma(this);
        throw new Error('Lean_nabla.insert_comma: unexpected');
    }

    set_line(line) {
        this.line = line;
        line = this.bound.set_line(line);
        if (!this.scope) return line;
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.scope.set_line(line);
    }

    strFormat() {
        // Binder form echoes `∇[θ] body` (glued like lim); binder-free `∇ J θ`.
        if (this.scope) return `${this.operator}[%s]${this.sep()}%s`;
        return `${this.operator} %s`;
    }

    /**
     * Binder sugar when scope is set (after `∇[…]` unwrap).
     * Binder-free `∇ J` / `∇ J θ` has no scope — bound holds the operands.
     */
    nablaSugar() {
        if (this.scope) {
            const index = this.bound;
            let body;
            if (this.scope instanceof L.LeanArgsSpaceSeparated)
                body = this.scope.args.filter((a) => !(a instanceof L.LeanCaret));
            else if (this.scope instanceof L.LeanCaret)
                body = [];
            else
                body = [this.scope];
            if (index instanceof L.LeanEq && index.lhs instanceof L.LeanToken)
                return {kind: 'binder', name: index.lhs, point: index.rhs, body};
            return {kind: 'binder', name: index, point: null, body};
        }
        // Binder-free: bound is J or SpaceSeparated(J, θ, …)
        const b = this.bound;
        if (b instanceof L.LeanCaret) return null;
        if (b instanceof L.LeanArgsSpaceSeparated)
            return {kind: 'function', operands: b.args.filter((a) => !(a instanceof L.LeanCaret))};
        return {kind: 'function', operands: [b]};
    }

    latexArgs(syntax) {
        const sugar = this.nablaSugar();
        if (!sugar) return [this.bound.toLatex(syntax)];
        if (sugar.kind === 'function') {
            return sugar.operands.map((arg) => {
                let a = arg;
                if (a instanceof L.LeanParenthesis && a.arg instanceof L.LeanDiv) a = a.arg;
                return L.LeanParenthesis.peelLatex(a).toLatex(syntax);
            });
        }
        const body = sugar.body.map((arg) => {
            let a = arg;
            if (a instanceof L.LeanParenthesis && a.arg instanceof L.LeanDiv) a = a.arg;
            return a.toLatex(syntax);
        });
        const name = sugar.name.toLatex(syntax);
        if (!sugar.point) return body.length ? [name, ...body] : [name];
        const point = L.LeanParenthesis.peelLatex(sugar.point);
        return [name, ...body, name, point.toLatex(syntax)];
    }

    latexFormat() {
        const sugar = this.nablaSugar();
        if (!sugar) return '\\nabla {%s}';
        if (sugar.kind === 'function') {
            const ops = sugar.operands;
            if (ops.length === 1) return '\\nabla {%s}';
            const rest = ops.slice(1).map(() => '{%s}').join('\\ ');
            return `\\nabla {%s}\\left(${rest}\\right)`;
        }
        const body = sugar.body.map(() => '{%s}').join('\\ ');
        const nabla = body ? `\\nabla_{%s} {${body}}` : '\\nabla_{%s}';
        if (!sugar.point) return nabla;
        return `\\left. ${nabla} \\right|_{{%s} = {%s}}`;
    }


    /**
     * Hole-regex: Grad_ when bound/scope present.
     * @param {object} [_opts]
     * @returns {string|null}
     */
    holeRegex(_opts = {}) {
        return (this.bound != null || this.scope != null) ? "Grad_" : null;
    }

    pathChoices(opts = {}) {
        const kid = this.scope ?? this.bound;
        const kids = kid?.pathChoices?.(opts) ?? [''];
        const out = [''];
        for (const k of kids) out.push(k ? 'Grad' + k : 'Grad_');
        return pathUniqKeepEmpty(out);
    }
}



/**
 * Random big-ops: `𝔼[binder](body)`, `ℙ[π](event)` / `ℙ[π]{event}`, `𝕍𝕒𝕣[binder](body)`.
 * Promoted from `GetElem(op, binder)` + Parenthesis/Brace body (same bound/scope
 * contract as ∑/∂/∇). Mathlib `Var[Y]` (no body delimiter) stays plain GetElem.
 */
export class LeanRandomBigOp extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 67;

    /** @type {'paren'|'brace'} delimiter that closed the body */
    bodyDelim = 'paren';

    get stack_priority() {
        if (this.scope) return L.LeanAdd.input_priority;
        return 67;
    }

    set_line(line) {
        this.line = line;
        line = this.bound.set_line(line);
        if (!this.scope) return line;
        return this.scope.set_line(line);
    }

    strFormat() {
        if (!this.scope) return `${this.operator}[%s]`;
        return `${this.operator}[%s]%s`;
    }

    sep() {
        return '';
    }

    get pathToken() {
        return 'Expect';
    }

    /**
     * Hole-regex: binder Expect/Prob/Var are binary (bound + scope).
     * Both holes -> Name__; bound hole + filled scope -> Name_(scopeFrag)
     * (same shape as Deriv_(scope) / Binom__). Mathlib Var[Y] stays GetElem.
     * @param {object} [opts]
     * @returns {string|null}
     */
    holeRegex(opts = {}) {
        if (this.bound == null && this.scope == null) return null;
        const tok = this.pathToken;
        const scopeFrag = this.scope?.holeRegex?.(opts) ?? null;
        if (scopeFrag == null || scopeFrag === "" || scopeFrag === "_") return `${tok}__`;
        return `${tok}_(${scopeFrag})`;
    }

    pathChoices(opts = {}) {
        const tok = this.pathToken;
        const kids = this.scope?.pathChoices?.(opts) ?? [''];
        const out = [''];
        let sawBothHoles = false;
        for (const k of kids) {
            if (!k) {
                if (!sawBothHoles) { out.push(`${tok}__`); sawBothHoles = true; }
                continue;
            }
            // Binary bound hole + scope fill: Expect_Mul..., Prob_..., Var_...
            out.push(`${tok}_` + k);
        }
        if (!sawBothHoles) out.push(`${tok}__`);
        out.push(tok);
        return pathUniqKeepEmpty(out);
    }

    binderLatex(syntax) {
        const ix = this.bound;
        if (ix instanceof L.LeanColon) {
            let ty = ix.rhs;
            if (ty instanceof L.LeanParenthesis) ty = ty.arg;
            if (ty instanceof L.LeanBitOr) {
                return `{${ix.lhs.toLatex(syntax)}} : {${ty.lhs.toLatex(syntax)}}`;
            }
        }
        return ix.toLatex(syntax);
    }

    latexArgs(syntax) {
        // Self-mark RV colors (node may sit outside ArgsSpaceSeparated after promote peel).
        if (this instanceof Lean_Expect)
            L.LeanArgsSpaceSeparated.markOneExpectBinder(this, this.scope);
        else if (this instanceof Lean_Prob)
            L.LeanArgsSpaceSeparated.markProbBinderArgs(this.scope);
        const binder = this.binderLatex(syntax);
        if (!this.scope) return [binder];
        return [binder, this.scope.toLatex(syntax)];
    }

    /**
     * Promote `GetElem(𝔼|ℙ|𝕍𝕒𝕣, binder)` + closed Parenthesis/Brace → Lean_* bigop.
     * @param {import('./base.js').Lean} bodyDelim
     * @returns {import('./base.js').Lean | null}
     */
    static tryPromote(bodyDelim) {
        const p = bodyDelim.parent;
        if (!(p instanceof L.LeanArgsSpaceSeparated)) return null;
        const i = p.args.indexOf(bodyDelim);
        if (i <= 0) return null;
        const head = p.args[i - 1];
        if (!(head instanceof L.LeanGetElem)) return null;
        const base = head.lhs ?? head.args?.[0];
        if (!(base instanceof L.LeanToken)) return null;
        let Ctor = null;
        if (base.text === '𝔼') Ctor = Lean_Expect;
        else if (base.text === 'ℙ') Ctor = Lean_Prob;
        else if (base.text === '𝕍𝕒𝕣') Ctor = Lean_Var;
        if (!Ctor) return null;
        const binder = head.rhs ?? head.args?.[1];
        const node = new Ctor(binder, bodyDelim.indent, bodyDelim.level, p);
        node.scope = bodyDelim;
        node.bodyDelim = bodyDelim instanceof L.LeanBrace ? 'brace' : 'paren';
        p.args.splice(i - 1, 2, node);
        bodyDelim.parent = node;
        if (binder) binder.parent = node;
        if (p.args.length === 1 && p.parent) {
            // Drop SpaceSeparated wrapper; clear parent so replace() rebinds to the outer node.
            node.parent = null;
            p.parent.replace(p, node);
            return node;
        }
        node.parent = p;
        return node;
    }
}

export class Lean_Expect extends LeanRandomBigOp {
    static { this.register(); }

    get baseOperator() {
        return '𝔼';
    }

    get pathToken() {
        return 'Expect';
    }

    latexFormat() {
        if (!this.scope) return '\\mathop{{𝔼}}\\limits_{%s}';
        return '\\mathop{{𝔼}}\\limits_{%s}\\ {%s}';
    }
}

export class Lean_Prob extends LeanRandomBigOp {
    static { this.register(); }

    get baseOperator() {
        return 'ℙ';
    }

    get pathToken() {
        return 'Prob';
    }

    latexFormat() {
        if (!this.scope) return '{{ℙ}}_{%s}';
        return '{{{ℙ}}_{%s}}\\ {%s}';
    }


    /**
     * Observation events `x = «\\sf{x}»` (and ∧ of them) are elided in latex to
     * `ℙ[π](x)` via collectProbEventRVs — hole-regex must be Prob__ (both holes),
     * never Prob_(Eq). Same rule as the RA form `ℙ[π](x)`.
     * @param {object} [opts]
     * @returns {string|null}
     */
    holeRegex(opts = {}) {
        if (this.bound == null && this.scope == null) return null;
        if (this.scope && L.LeanArgsSpaceSeparated.collectProbEventRVs(this.scope))
            return "Prob__";
        return super.holeRegex(opts);
    }

    /**
     * Observation events path like RA `ℙ[π](x)`: Prob__ / Prob, not Prob_Eq.
     * @param {object} [opts]
     * @returns {string[]}
     */
    pathChoices(opts = {}) {
        if (this.scope && L.LeanArgsSpaceSeparated.collectProbEventRVs(this.scope))
            return pathUniqKeepEmpty(["", "Prob__", "Prob"]);
        return super.pathChoices(opts);
    }

}

export class Lean_Var extends LeanRandomBigOp {
    static { this.register(); }

    get baseOperator() {
        return '𝕍𝕒𝕣';
    }

    get pathToken() {
        return 'Var';
    }

    latexFormat() {
        if (!this.scope) return '{{𝕍𝕒𝕣}}_{%s}';
        return '{{{𝕍𝕒𝕣}}_{%s}}\\ {%s}';
    }
}


/**
 * Limits-style GetElem sugars: `max[i] body`, `min[…]`, `sup[…]`, `inf[…]`,
 * `max⁻¹[…] body`, `min⁻¹[…] body`. Promoted from `GetElem(op, binder)` + body
 * (paren/brace close, or SpaceSeparated juxta / newline body). Same bound+scope
 * contract as ∑/𝔼. Unicode `⨅`/`⨆` stay `LeanInf`/`LeanSup` (not these).
 */
export class LeanLimitsBigOp extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 67;

    static LIMITS_CTOR = null; // filled after subclasses register

    static limitsCtorFor(text) {
        const map = LeanLimitsBigOp.LIMITS_CTOR;
        return map ? map[text] ?? null : null;
    }

    static isLimitsGetElem(head) {
        if (!(head instanceof L.LeanGetElem)) return null;
        const base = head.lhs ?? head.args?.[0];
        if (!(base instanceof L.LeanToken)) return null;
        const Ctor = LeanLimitsBigOp.limitsCtorFor(base.text);
        if (!Ctor) return null;
        return {Ctor, binder: head.rhs ?? head.args?.[1], base};
    }

    get stack_priority() {
        if (this.scope) return L.LeanAdd.input_priority;
        return 67;
    }

    set_line(line) {
        this.line = line;
        line = this.bound.set_line(line);
        if (!this.scope) return line;
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.scope.set_line(line);
    }

    strFormat() {
        if (!this.scope) return `${this.operator}[%s]`;
        return `${this.operator}[%s] %s`;
    }

    sep() {
        return ' ';
    }

    get pathToken() {
        return 'Max';
    }

    holeRegex(_opts = {}) {
        return (this.bound != null || this.scope != null) ? `${this.pathToken}_` : null;
    }

    pathChoices(opts = {}) {
        const kid = this.scope ?? this.bound;
        const kids = kid?.pathChoices?.(opts) ?? [''];
        const tok = this.pathToken;
        const out = [];
        for (const k of kids) {
            if (!k) continue;
            const core = pathStripTrailingHoles(k);
            if (!core) continue;
            out.push(tok + core);
        }
        out.push(tok, '');
        return pathUniqKeepEmpty(out);
    }

    binderLatex(syntax) {
        return L.LeanGetElem.expectBinderIndexLatex(this.bound, syntax);
    }

    latexArgs(syntax) {
        const binder = this.binderLatex(syntax);
        if (!this.scope) return [binder];
        return [binder, this.scope.toLatex(syntax)];
    }

    /**
     * Splice `GetElem(limitsOp, binder)` + body out of a SpaceSeparated into a limits bigop.
     * @param {import('./args.js').LeanArgsSpaceSeparated} ss
     * @returns {import('./base.js').Lean | null}
     */
    static tryPromoteSpaceSeparated(ss) {
        if (!(ss instanceof L.LeanArgsSpaceSeparated) || ss.args.length < 2) return null;
        const info = LeanLimitsBigOp.isLimitsGetElem(ss.args[0]);
        if (!info) return null;
        const rest = ss.args.slice(1);
        const scope = rest.length === 1
            ? rest[0]
            : new L.LeanArgsSpaceSeparated(rest, ss.indent, ss.level);
        const node = new info.Ctor(info.binder, ss.indent, ss.level, ss.parent);
        node.scope = scope;
        if (info.binder) info.binder.parent = node;
        if (scope) scope.parent = node;
        if (ss.parent) {
            node.parent = null;
            ss.parent.replace(ss, node);
        } else {
            node.parent = null;
        }
        return node;
    }

    /**
     * Promote `GetElem(max|…|max⁻¹, binder)` + closed Parenthesis/Brace → limits bigop.
     * @param {import('./base.js').Lean} bodyDelim
     * @returns {import('./base.js').Lean | null}
     */
    static tryPromote(bodyDelim) {
        const p = bodyDelim.parent;
        if (!(p instanceof L.LeanArgsSpaceSeparated)) return null;
        const i = p.args.indexOf(bodyDelim);
        if (i <= 0) return null;
        const head = p.args[i - 1];
        const info = LeanLimitsBigOp.isLimitsGetElem(head);
        if (!info) return null;
        const node = new info.Ctor(info.binder, bodyDelim.indent, bodyDelim.level, p);
        node.scope = bodyDelim;
        p.args.splice(i - 1, 2, node);
        bodyDelim.parent = node;
        if (info.binder) info.binder.parent = node;
        if (p.args.length === 1 && p.parent) {
            node.parent = null;
            p.parent.replace(p, node);
            return node;
        }
        node.parent = p;
        return node;
    }
}

export class Lean_max extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'max'; }
    get pathToken() { return 'Max'; }

    latexFormat() {
        if (!this.scope) return '\\max\\limits_{%s}';
        return '\\max\\limits_{%s} {%s}';
    }
}

export class Lean_min extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'min'; }
    get pathToken() { return 'Min'; }

    latexFormat() {
        if (!this.scope) return '\\min\\limits_{%s}';
        return '\\min\\limits_{%s} {%s}';
    }
}

export class Lean_sup extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'sup'; }
    get pathToken() { return 'Sup'; }

    latexFormat() {
        if (!this.scope) return '\\sup\\limits_{%s}';
        return '\\sup\\limits_{%s} {%s}';
    }
}

export class Lean_inf extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'inf'; }
    get pathToken() { return 'Inf'; }

    latexFormat() {
        if (!this.scope) return '\\inf\\limits_{%s}';
        return '\\inf\\limits_{%s} {%s}';
    }
}

export class Lean_argmax extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'max⁻¹'; }
    get pathToken() { return 'ArgMax'; }

    latexFormat() {
        // Do not use `\limits` on `^{-1}` (overscript bug); keep underset form.
        if (!this.scope) return '\\underset{%s}{\\operatorname{max}^{-1}}';
        return '\\underset{%s}{\\operatorname{max}^{-1}} {%s}';
    }
}

export class Lean_argmin extends LeanLimitsBigOp {
    static { this.register(); }

    get baseOperator() { return 'min⁻¹'; }
    get pathToken() { return 'ArgMin'; }

    latexFormat() {
        if (!this.scope) return '\\underset{%s}{\\operatorname{min}^{-1}}';
        return '\\underset{%s}{\\operatorname{min}^{-1}} {%s}';
    }
}

LeanLimitsBigOp.LIMITS_CTOR = {
    max: Lean_max,
    min: Lean_min,
    sup: Lean_sup,
    inf: Lean_inf,
    'max⁻¹': Lean_argmax,
    'min⁻¹': Lean_argmin,
};


export class Lean_bigcap extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 60;
    get baseOperator() {
        return '⋂';
    }
}

export class Lean_bigcup extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 60;
    get baseOperator() {
        return '⋃';
    }
}

export class LeanInf extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 60;
    get baseOperator() {
        return '⨅';
    }
    get command() {
        return '\\mathop{⨅}';
    }
}

export class LeanSup extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 60;
    get baseOperator() {
        return '⨆';
    }
    get command() {
        // katex doesn't support `\bigsqcup`
        return '⨆';
    }
}

/**
 * Fin-index sugar promoted from `LeanBracket` on `]`.
 * `operator` / `command` === `"Stack"` (lemmaPath token for DetStack_…).
 * - Tensor: `args[0]` = one `Lean_lt` (`[i < n] body`); `matrixFinBinders()` null
 * - Matrix ofFun: `args[0]` = `LeanArgsCommaSeparated` of two `Lean_lt`
 *   (`[i < n, j < n] body`); `args[1]` = entry body (may be NewLineSeparated);
 *   `matrixFinBinders()` → `[lt_i, lt_j]`
 */
export class LeanStack extends LeanBigOperator {
    static { this.register(); }

    static input_priority = 52;

    get operator() {
        return 'Stack';
    }

    get command() {
        return 'Stack';
    }

    get stack_priority() {
        if (this.scope) return L.LeanRelational.input_priority;
        return 28;
    }

    /**
     * Matrix Fin-entry sugar: bound is `,`-separated `i < m, j < n`.
     * @returns {[Lean, Lean] | null} the two `Lean_lt` binders
     */
    matrixFinBinders() {
        const b = this.bound;
        if (!(b instanceof L.LeanArgsCommaSeparated)) return null;
        const parts = b.args.filter((x) => !(x instanceof L.LeanCaret));
        if (
            parts.length !== 2 ||
            !parts.every((p) => p instanceof L.Lean_lt && p.lhs instanceof L.LeanToken)
        )
            return null;
        return /** @type {[Lean, Lean]} */ (parts);
    }

    is_indented() {
        const {parent} = this;
        return parent instanceof L.LeanStatements || (parent instanceof L.LeanIte && !parent.inline) || parent instanceof L.LeanArgsNewLineSeparated || parent instanceof L.LeanArgsCommaNewLineSeparated;
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
