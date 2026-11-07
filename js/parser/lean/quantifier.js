/**
 * Quantifiers: `LeanQuantifier`, `∀` (`Lean_forall`), and `∃` (`Lean_exists`).
 *
 * They extend `LeanProp(LeanBigOperator)`. `LeanBigOperator` and the concrete
 * big operators live in `bigops.js`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanProp } from './utility.js';
import { LeanBigOperator } from './bigops.js';
import { Lean } from './base.js';
import { wrapHoleOpt, storedHoleOpt } from './pathChoices.js';

const L = Lean.classes;

/**
 * Quantifier stored group. `forall` peels `k ≠ 0 →` and spells a hole body as `All__`.
 * @param {object} node
 * @param {string} tag
 * @param {object} opts
 * @param {Set<string>} binders
 * @param {boolean} forall
 * @returns {string|null}
 */
function storedQuantRegex(node, tag, opts, binders) {
    const forall = tag === "All";
    if (typeof opts.noteQuantBinders === "function") {
        opts.noteQuantBinders(node, binders);
        if (!opts.quantNames) opts.quantNames = new Set();
        opts.noteQuantBinders(node, opts.quantNames);
    }
    let body = node.scope ?? node.args?.[node.args.length - 1];
    if (forall && typeof opts.peelGuardForalls === "function") body = opts.peelGuardForalls(body);
    if (forall && typeof opts.peelQuantRelGuard === "function") body = opts.peelQuantRelGuard(body, opts.quantNames);
    if (forall && typeof opts.isHole === "function" && opts.isHole(body, opts, binders)) return "All__";
    const inner = typeof opts.decomp === "function" ? opts.decomp(body, binders) : null;
    if (!inner) return null;
    if (inner === tag || inner.startsWith(tag + "_")) return inner;
    return tag + "_" + storedHoleOpt(inner);
}

/** Port of `LeanQuantifier`. */
export class LeanQuantifier extends LeanProp(LeanBigOperator) {
    static { this.register(); }

    static input_priority = 24;

    /** @returns {string|null} */
    get holeRegexTag() {
        return null;
    }

    /**
     * Hole-regex: All_/Any_ + optional body (Body t344).
     * opts.peelGuards peels forall-guard binders (lemmaPath peelGuardForalls).
     * @param {object} [opts]
     * @returns {string|null}
     */
    holeRegex(opts = {}) {
        const tag = this.holeRegexTag;
        if (!tag) return super.holeRegex?.(opts) ?? null;
        let bodyNode = this.scope ?? this.args[this.args.length - 1];
        if (tag === "All" && typeof opts.peelGuards === "function")
            bodyNode = opts.peelGuards(bodyNode);
        const body = bodyNode?.holeRegex?.(opts) ?? null;
        if (body == null || body === "") return tag;
        if (body === tag || body.startsWith(tag + "_")) return body;
        return tag + "_" + wrapHoleOpt(body);
    }


    measurePartial() {
        if (this.superscript !== 'ᵐ') return null;
        const b = this.bound;
        if (!(b instanceof L.LeanArgsSpaceSeparated)) return null;
        for (let i = b.args.length - 1; i >= 0; i--) {
            if (b.args[i] instanceof L.LeanCaret) continue;
            return b.args[i] instanceof L.Lean_partial ? b.args[i] : null;
        }
        return null;
    }

    latexFormat() {
        const sup = this.superscript === 'ᶠ' ? '\\mathrm{f}' : this.superscript;
        const cmd = this.superscript
            ? `${this.command}^{${sup}}\\,`
            : `${this.command}\\ `;
        if (this.args.length === 1) return `${cmd}{%s},`;
        return `${cmd}{%s}, {%s}`;
    }

    latexArgs(syntax) {
        // `∀ᶠ x in l, p` — `in` is a keyword, not a product of the letters i and n
        if (this.superscript === 'ᶠ' && this.bound instanceof L.LeanArgsSpaceSeparated && this.scope) {
            const bound = this.bound.args
                .filter((a) => !(a instanceof L.LeanCaret))
                .map((a) => (a instanceof L.LeanIn ? `\\text{ in }{${a.arg.toLatex(syntax)}}` : a.toLatex(syntax)))
                .join('\\ ');
            return [bound, this.scope.toLatex(syntax)];
        }
        const partial = this.measurePartial();
        if (!partial) return super.latexArgs(syntax);
        const bound = this.bound.args
            .filter((a) => a !== partial && !(a instanceof L.LeanCaret))
            .map((a) => a.toLatex(syntax))
            .join(' ');
        // keep the measure: `∀ᵐ a ∂μ, p` → `∀ᵐ a ∂μ, p`
        return [`${bound}\\ \\partial {${partial.bound.toLatex(syntax)}}`, this.scope.toLatex(syntax)];
    }

    get stack_priority() {
        return L.LeanColon.input_priority - 1;
    }
}

export class Lean_forall extends LeanQuantifier {
    static { this.register(); }

    get holeRegexTag() {
        return "All";
    }

    /** `∀ k, P` stored as `All_(P)`. A binder guard `k ≠ 0 →` stays out. */
    storedHoleRegex(opts, binders) {
        return storedQuantRegex(this, "All", opts, binders);
    }

    get baseOperator() {
        return '∀';
    }
}

export class Lean_exists extends LeanQuantifier {
    static { this.register(); }

    get holeRegexTag() {
        return "Any";
    }

    /** `∃ x, P` stored as `Any_(P)`. */
    storedHoleRegex(opts, binders) {
        return storedQuantRegex(this, "Any", opts, binders);
    }


    unique = false;

    get baseOperator() {
        return this.unique ? '∃!' : '∃';
    }

    get command() {
        return this.unique ? '\\exists!' : '\\exists';
    }
}
