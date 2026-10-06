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

const L = Lean.classes;

/** Port of `LeanQuantifier`. */
export class LeanQuantifier extends LeanProp(LeanBigOperator) {
    static { this.register(); }

    static input_priority = 24;

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
        return [`${bound}\\ \\partial {${partial.arg.toLatex(syntax)}}`, this.scope.toLatex(syntax)];
    }

    get stack_priority() {
        return L.LeanColon.input_priority - 1;
    }
}

export class Lean_forall extends LeanQuantifier {
    static { this.register(); }

    get baseOperator() {
        return '∀';
    }
}

export class Lean_exists extends LeanQuantifier {
    static { this.register(); }

    unique = false;

    get baseOperator() {
        return this.unique ? '∃!' : '∃';
    }

    get command() {
        return this.unique ? '\\exists!' : '\\exists';
    }
}
