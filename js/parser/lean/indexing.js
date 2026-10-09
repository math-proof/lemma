/**
 * Indexing: `LeanGetElem`, `LeanGetWhiteSquareBracket`, `LeanGetElemQue`,
 * `LeanGetElemQuote`.
 *
 * The `LeanGetElemBase` / `LeanGetElemBaseBinary` mixins live in `utility.js`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanGetElemBase, LeanGetElemBaseBinary } from './utility.js';
import { LeanArgs, LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanGetElem extends LeanGetElemBaseBinary(LeanBinary) {
    static { this.register(); }

    static input_priority = 67;

    collectGetElemChain() {
        const indices = [];
        let node = /** @type {Lean} */ (this);
        while (node instanceof LeanGetElem) {
            indices.unshift(node.rhs);
            node = node.lhs;
        }
        return {base: node, indices};
    }

    /**
     * `max[y : T] f y` / `min[…]` / `sup[…]` / `inf[…]` — a big operator whose bound
     * variable is drawn under the operator, not as a subscript.
     * @returns {string | null} the LaTeX command (`\\max`, …)
     */
    static limitsOperator(base, indices) {
        if (!(base instanceof L.LeanToken) || indices.length !== 1) return null;
        return ['max', 'min', 'sup', 'inf'].includes(base.text) ? `\\${base.text}` : null;
    }

    static expectBinderIndexLatex(ix, syntax) {
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
        // Nested segment of a longer chain: outer node owns multi-index LaTeX.
        if (this.parent instanceof LeanGetElem) return super.latexArgs(syntax);

        const {base, indices} = this.collectGetElemChain();
        if (base instanceof L.LeanToken && base.text === '𝔼') {
            return [
                base.toLatex(syntax),
                ...indices.map((ix) => LeanGetElem.expectBinderIndexLatex(ix, syntax)),
            ];
        }
        if (LeanGetElem.limitsOperator(base, indices))
            return [LeanGetElem.expectBinderIndexLatex(indices[0], syntax)];
        if (indices.length === 1 && indices[0] instanceof L.LeanCondBar)
            return [base.toLatex(syntax), indices[0].arg.toLatex(syntax)];
        const condExp = indices.length === 1 ? LeanGetElem.condExpLatex(indices[0], syntax) : null;
        if (condExp) return [base.toLatex(syntax), ...condExp];
        const indexParts = indices.map((ix) => ix.toLatex(syntax));
        const indexLatex = indexParts.join(', ');

        if (base instanceof L.LeanProperty && base.rhs instanceof L.LeanToken) {
            const fmt = base.latexFormat();
            const args = base.latexArgs(syntax);
            if (args.length && fmt.includes('%s')) {
                args[0] = `{${base.lhs.toLatex(syntax)}}_{${indexLatex}}`;
                return args;
            }
        }

        if (indices.length >= 2) return [base.toLatex(syntax), ...indexParts];

        const spec = this.propertyGetElemLatex(syntax, this.rhs.toLatex(syntax));
        if (spec) return spec.args;
        return super.latexArgs(syntax);
    }

    /**
     * `μ[f | m]` — Mathlib conditional expectation `condExp m μ f`. The `|` may sit inside a
     * lambda body (`μ[fun ω => f ω | ℱ n]`), since `fun` extends as far as possible.
     * @returns {[string, string] | null} LaTeX of `f` and `m`
     */
    static condExpLatex(ix, syntax) {
        if (ix instanceof L.LeanBitOr) return [ix.lhs.toLatex(syntax), ix.rhs.toLatex(syntax)];
        if (ix instanceof L.Lean_fun && ix.arg instanceof L.LeanBinary && ix.arg.rhs instanceof L.LeanBitOr) {
            const arrow = ix.arg;
            const bar = arrow.rhs;
            const saved = arrow.args[1];
            arrow.args[1] = bar.lhs;
            let fn;
            try {
                fn = ix.toLatex(syntax);
            } finally {
                arrow.args[1] = saved;
            }
            return [fn, bar.rhs.toLatex(syntax)];
        }
        return null;
    }

    latexFormat() {
        if (this.parent instanceof LeanGetElem) return '{%s}_{%s}';

        const {base, indices} = this.collectGetElemChain();
        // `μ[|s]` — conditional measure `cond μ s`
        const limitsOp = LeanGetElem.limitsOperator(base, indices);
        if (limitsOp) return `${limitsOp}\\limits_{%s}`;
        if (indices.length === 1 && indices[0] instanceof L.LeanCondBar)
            return '{%s}\\left[\\,\\cdot \\,\\middle|\\, {%s}\\right]';
        if (indices.length === 1 && !(base instanceof L.LeanToken && base.text === '𝔼') &&
            (indices[0] instanceof L.LeanBitOr ||
                (indices[0] instanceof L.Lean_fun && indices[0].arg instanceof L.LeanBinary && indices[0].arg.rhs instanceof L.LeanBitOr)))
            return '\\mathbb{E}_{%s}\\left[{%s} \\,\\middle|\\, {%s}\\right]';
        if (base instanceof L.LeanProperty && base.rhs instanceof L.LeanToken) {
            const fmt = base.latexFormat();
            if (fmt.includes('%s')) return fmt;
        }
        if (base instanceof L.LeanToken && base.text === '𝔼') {
            if (indices.length >= 2)
                return `\\mathop{{%s}}\\limits_{${indices.map(() => '%s').join(', ')}}`;
            return '\\mathop{{%s}}\\limits_{%s}';
        }
        if (indices.length >= 2) {
            return `{%s}_{${indices.map(() => '%s').join(', ')}}`;
        }

        const spec = this.propertyGetElemLatex(null, '');
        if (spec) return spec.format;
        return '{%s}_{%s}';
    }

    strFormat() {
        return '%s[%s]';
    }
}

/** `P⟦s | m⟧` — Mathlib `ProbabilityTheory` conditional notation; glued like `GetElem`. */
export class LeanGetWhiteSquareBracket extends LeanGetElemBaseBinary(LeanBinary) {
    static { this.register(); }

    static input_priority = 67;

    latexFormat() {
        return '{%s}\\left\\llbracket {%s} \\right\\rrbracket';
    }

    strFormat() {
        return '%s⟦%s⟧';
    }

    push_right(funcName) {
        if (funcName === 'LeanWhiteSquareBracket') return this;
        return super.push_right(funcName);
    }
}

export class LeanGetElemQue extends LeanGetElemBaseBinary(LeanBinary) {
    static { this.register(); }

    static input_priority = 67;

    latexArgs(syntax) {
        const spec = this.propertyGetElemLatex(syntax, `${this.rhs.toLatex(syntax)}?`);
        if (spec) return spec.args;
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const spec = this.propertyGetElemLatex(null, '');
        if (spec) return spec.format;
        return '{%s}_{%s?}';
    }

    strFormat() {
        return '%s[%s]?';
    }
}

export class LeanGetElemQuote extends LeanGetElemBase(LeanArgs) {
    static { this.register(); }

    static input_priority = 67;

    latexArgs(syntax) {
        const idx = `${this.args[1].toLatex(syntax)}{\\color{red}\\text{'}}${this.args[2].toLatex(syntax)}`;
        const spec = this.propertyGetElemLatex(syntax, idx);
        if (spec) return spec.args;
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const spec = this.propertyGetElemLatex(null, '');
        if (spec) return spec.format;
        return "{%s}_{%s{\\color{red}\\text{'}}%s}";
    }

    strFormat() {
        return "%s[%s]'%s";
    }
}
