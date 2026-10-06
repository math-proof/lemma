/**
 * Big operators: `LeanBigOperator` and `∑` / `lim` / `∏` / `∫` /
 * `⋂` / `⋃` / `⨅` / `⨆` / `Stack`.
 *
 * Quantifiers stay in `quantifier.js` (they extend `LeanBigOperator`).
 * `LeanAdd` is read for `input_priority` and `instanceof`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { strStmt } from './utility.js';
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
                const peel = (arg) => (arg instanceof L.LeanParenthesis ? arg.arg : arg);
                return [i.toLatex(syntax), peel(n).toLatex(syntax), this.scope.toLatex(syntax)];
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
    /**
     * `∑ «y.bvar» t, f`: a bound variable is never red, so the index and the body's `y t` that stands
     * for the bound value (`(y t) = «y.bvar» t` inside `ℙ[π](…)`) are drawn in the normal colour.
     */
    latexArgs(syntax) {
        const bnd = this.bound;
        if (
            this.scope &&
            bnd instanceof L.LeanArgsSpaceSeparated && bnd.args.length === 2 &&
            bnd.args[0] instanceof L.LeanDoubleAngleQuotation
        ) {
            const base = bnd.args[0].boundValueLhs();
            if (base instanceof L.LeanToken) {
                const key = strStmt(bnd).trim();
                const seen = new Set();
                const walk = (n) => {
                    if (!n || typeof n !== 'object' || seen.has(n)) return;
                    seen.add(n);
                    if (n instanceof L.LeanEq && strStmt(n.rhs).trim() === key) {
                        let l = n.lhs;
                        while (l instanceof L.LeanParenthesis) l = l.arg;
                        if (l instanceof L.LeanArgsSpaceSeparated) l = l.args[0];
                        if (l instanceof L.LeanToken && l.text === base.text) l.kwargs.neverRed = true;
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
        if (this.args.length === 1) return `${this.operator} [%s]`;
        return `${this.operator} [%s]${sep}%s`;
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
            return rest.length === 1 && rest[0] instanceof L.Lean_partial ? rest[0] : null;
        }
        if (s instanceof L.LeanArgsSpaceSeparated) {
            for (let i = s.args.length - 1; i >= 0; i--) {
                if (s.args[i] instanceof L.LeanCaret) continue;
                return s.args[i] instanceof L.Lean_partial ? s.args[i] : null;
            }
            return null;
        }
        if (s != null && s.rhs instanceof L.LeanArgsSpaceSeparated) {
            const args = s.rhs.args;
            for (let i = args.length - 1; i >= 0; i--) {
                if (args[i] instanceof L.LeanCaret) continue;
                return args[i] instanceof L.Lean_partial ? args[i] : null;
            }
        }
        if (s instanceof Lean_int) {
            const innerPartial = s.measurePartial();
            if (!innerPartial) return null;
            const a = innerPartial.arg;
            if (a instanceof L.LeanArgsSpaceSeparated) {
                for (let i = a.args.length - 1; i >= 0; i--) {
                    if (a.args[i] instanceof L.LeanCaret) continue;
                    return a.args[i] instanceof L.Lean_partial ? a.args[i] : null;
                }
            }
            return null;
        }
        return null;
    }

    integrandLatex(syntax, partial) {
        if (!partial) return this.scope ? this.scope.toLatex(syntax) : '';
        if (this.scope instanceof L.LeanArgsIndented && this.scope.rhs instanceof L.LeanArgsNewLineSeparated &&
            this.scope.rhs.args.includes(partial))
            return this.scope.lhs.toLatex(syntax);
        if (this.scope instanceof L.LeanArgsSpaceSeparated) {
            const args = this.scope.args
                .filter((a) => a !== partial && !(a instanceof L.LeanCaret));
            return args.map((a) => `{${a.toLatex(syntax)}}`).join('\\ ');
        }
        // Binary operator scope (e.g. `c • f x ∂μ`): partial is in scope.rhs
        if (this.scope != null && this.scope.rhs instanceof L.LeanArgsSpaceSeparated &&
            this.scope.rhs.args.includes(partial)) {
            const filteredRhs = this.scope.rhs.args
                .filter((a) => a !== partial && !(a instanceof L.LeanCaret));
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
        if (dom instanceof L.LeanUpto) return `${op}\\limits_{%s}^{%s} %s\\, ${tail}`;
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
            : v && !(v instanceof L.LeanCaret)
                ? v.toLatex(syntax)
                : '';
        const dom = this.intDomain();
        if (dom instanceof L.LeanUpto) {
            return [dom.lhs.toLatex(syntax), dom.rhs.toLatex(syntax), body, tail];
        }
        if (dom != null) return [dom.toLatex(syntax), body, tail];
        return [body, tail];
    }
}

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
