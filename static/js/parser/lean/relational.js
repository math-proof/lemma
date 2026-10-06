/**
 * Relational comparisons: `LeanRelational` and `>` / `<` / `≥` / `≤` / `=` /
 * `==` / `!=` / `≠` / `≡` / `≢` / `≃` / `≈` / `≍` / `∣` / `⟂`, plus JS `≪` / `≫`.
 *
 * `LeanFilterRelational` stays in this module (only `≥` / `≤` use it).
 * PHP `Lean_ll` / `Lean_gg` stay in the arithmetic module: there they extend
 * `LeanArithmetic`, not `LeanRelational`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { escapeSpecialsForLatex } from './utility.js';
import { LeanBinaryBoolean } from './boolean.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanRelational extends LeanBinaryBoolean {
    static { this.register(); }

    static input_priority = 50;

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    latexArgs(syntax = null) {
        const [lhs, rhs] = this.strip_parenthesis();
        return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
    }
}

/** Relational / equality binary nodes (`>`, `≥`, `=`, `≃`, `∣`, …). */
export class Lean_gt extends LeanRelational {
    static { this.register(); }

    get operator() {
        return '>';
    }
}
/**
 * `≤ᵐ[μ]` / `≥ᶠ[l]` — relation with an optional `ᵐ`/`ᶠ` superscript and bracketed measure/filter.
 * @template {typeof LeanRelational} T
 * @param {T} Base
 */
function LeanFilterRelational(Base) {
    return class extends Base {
        superscript = '';
        modifier = '';

        opStr() {
            let op = this.operator + (this.superscript || '');
            if (this.modifier) op += `[${this.modifier}]`;
            return op;
        }

        /** Like `LeanEq.opLatex`: the ambient measure of `ᵐ` is elided, a filter `ᶠ[l]` is shown. */
        opLatex() {
            let op = this.command;
            if (this.superscript) {
                const map = L.LeanToken.supscript;
                op += `^{${[...this.superscript].map((ch) => (map[ch] !== undefined ? map[ch] : ch)).join('')}}`;
                if (this.superscript === 'ᶠ' && this.modifier)
                    op += `_{${escapeSpecialsForLatex(this.modifier.trim())}}`;
            }
            return op;
        }

        strFormat() {
            if (!this.superscript) return super.strFormat();
            return `%s ${this.opStr()}${this.sep()}%s`;
        }

        latexFormat() {
            if (!this.superscript) return super.latexFormat();
            return `{%s} ${this.opLatex()}${this.sep()}{%s}`;
        }
    };
}

export class Lean_ge extends LeanFilterRelational(LeanRelational) {
    static { this.register(); }

    get operator() {
        return '≥';
    }
}
export class Lean_lt extends LeanRelational {
    static { this.register(); }

    get operator() {
        return '<';
    }
}
export class Lean_le extends LeanFilterRelational(LeanRelational) {
    static { this.register(); }

    get operator() {
        return '≤';
    }
}

export class LeanEq extends LeanRelational {
    static { this.register(); }

    /** @type {string} unicode superscript glyph(s), e.g. `ᵐ` */
    superscript = '';
    /** @type {string} bracketed measure, e.g. `ν` — required by Lean notation, elided in LaTeX */
    modifier = '';

    get command() {
        return '=';
    }

    get operator() {
        return '=';
    }

    /** Echo operator: `=` + superscript + optional `[modifier]`. */
    opStr() {
        let op = this.operator + (this.superscript || '');
        if (this.modifier) op += `[${this.modifier}]`;
        return op;
    }

    /** LaTeX operator: `=` + mapped superscript; measure bracket omitted. */
    opLatex() {
        let op = this.command;
        if (this.superscript) {
            const map = L.LeanToken.supscript;
            const inner = [...this.superscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            op += `^{${inner}}`;
        }
        // `=ᶠ[l]` — the filter is not implied by context (unlike the ambient measure of `=ᵐ[μ]`)
        if (this.superscript === 'ᶠ' && this.modifier)
            op += `_{${escapeSpecialsForLatex(this.modifier.trim())}}`;
        return op;
    }

    latexArgs(syntax) {
        if (syntax) syntax[this.opStr().split('[')[0]] = true;
        return super.latexArgs(syntax);
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.opStr()}${sep}%s`;
    }

    latexFormat() {
        const sep = this.sep();
        return `{%s} ${this.opLatex()}${sep}{%s}`;
    }
}

/**
 * `x ⟂ᵢ[π] y` / `x ⟂ᵢ[π] (y, z)` — independence (`\perp` from the class name).
 * Optional unicode `subscript` (e.g. `ᵢ`) and bracketed `modifier` measure (echo only).
 * Conditional form `x ⟂ᵢ[π] y | z` is `(x ⟂ᵢ[π] y) | z` via `LeanBitOr` (priority 33).
 */
export class Lean_perp extends LeanRelational {
    static { this.register(); }

    /** @type {string} unicode subscript glyph(s), e.g. `ᵢ` */
    subscript = '';
    /** @type {string} bracketed measure, e.g. `π` / `𝕡` — required by Lean notation, elided in LaTeX */
    modifier = '';

    get operator() {
        return '⟂';
    }

    /** Echo operator: `⟂` + subscript + optional `[modifier]`. */
    opStr() {
        let op = this.operator + (this.subscript || '');
        if (this.modifier) op += `[${this.modifier}]`;
        return op;
    }

    /** LaTeX operator: `\perp` + `_{i}` from subscript; measure bracket omitted. */
    opLatex() {
        let op = this.command; // `\perp` via Lean_* naming
        if (this.subscript) {
            const map = L.LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            op += `_{${inner}}`;
        }
        return op;
    }

    /** `⟂ᵢ` is (conditional) independence: both operands are random variables. */
    get isIndependence() {
        return this.subscript === 'ᵢ';
    }

    /**
     * The `⟂ᵢ` node a CondIndep `| Z` attaches to: `n` itself, or the only line of a one-line
     * block (a `∀ …,` body starting on a new line parses as `LeanArgsNewLineSeparated[⟂ᵢ]`).
     * @returns {Lean_perp | null}
     */
    static independenceOf(n) {
        while (n instanceof L.LeanArgsNewLineSeparated && n.args.length === 1) n = n.args[0];
        return n instanceof Lean_perp && n.isIndependence ? n : null;
    }

    /**
     * Colour a random-variable operand of `⟂ᵢ` red, head only (`Lean.headTokens`): `r[t + 1:]` → `r`,
     * `(s t, a t)` → `s`, `a`; indices and arguments stay black. Red wins over an enclosing ℙ/𝔼's
     * magenta: inside `⟂ᵢ` the term is a random variable, not a random argument. `neverRed`
     * (big-operator indices) is respected at render time.
     */
    static markRandomVariableTerm(x) {
        for (const h of Lean.headTokens(x)) {
            h.kwargs.isRandomVariable = true;
            delete h.kwargs.isRandomArgument;
        }
    }

    latexArgs(syntax) {
        if (syntax) syntax['⟂'] = true;
        if (this.isIndependence) for (const a of this.args) Lean_perp.markRandomVariableTerm(a);
        // keep a parenthesized pair rhs `(y, z)` intact — it is an argument, not grouping
        return this.args.map((a) => a.toLatex(syntax));
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.opStr()}${sep}%s`;
    }

    latexFormat() {
        const sep = this.sep();
        return `{%s} ${this.opLatex()}${sep}{%s}`;
    }
}

export class LeanBEq extends LeanRelational {
    static { this.register(); }

    get command() {
        return '\\!\\!=';
    }

    get operator() {
        return '==';
    }
}
export class Lean_bne extends LeanRelational {
    static { this.register(); }

    get command() {
        return '!=';
    }

    get operator() {
        return '!=';
    }
}
export class Lean_ne extends LeanRelational {
    static { this.register(); }

    get operator() {
        return '≠';
    }
}
export class Lean_equiv extends LeanRelational {
    static { this.register(); }

    static input_priority = 32;

    get operator() {
        return '≡';
    }
}
export class LeanNotEquiv extends LeanRelational {
    static { this.register(); }

    static input_priority = 32;

    get command() {
        return '\\not\\equiv';
    }

    get operator() {
        return '≢';
    }
}
export class Lean_simeq extends LeanRelational {
    static { this.register(); }

    static input_priority = 50;

    /** @type {string | null} unicode superscript glyph, e.g. `ᵐ` (measurable equivalence) */
    superscript = null;
    /** @type {string} right-script suffix letter, e.g. `L` in `≃L[ℝ]` (continuous linear equivalence) */
    subscript = '';
    /** @type {string} bracketed scalar ring, e.g. `ℝ` — required by Lean notation, elided in LaTeX */
    modifier = '';

    /** Plain `≃`, measurable `≃ᵐ`, or continuous linear `≃L[ℝ]`. */
    opStr() {
        let op = '≃';
        if (this.subscript) {
            op += this.subscript;
            if (this.modifier) op += `[${this.modifier}]`;
        } else if (this.superscript) {
            op += this.superscript;
        }
        return op;
    }

    get operator() {
        return this.opStr();
    }

    get command() {
        return '\\simeq';
    }

    /** `≃L[ℝ]` renders as `\simeq_L`; the scalar bracket is omitted (same convention as `⟂ᵢ[π]`). */
    opLatex() {
        let op = this.command;
        if (this.subscript) op += `_{${this.subscript}}`;
        return op;
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.opStr()}${sep}%s`;
    }

    latexFormat() {
        const sep = this.sep();
        return `{%s} ${this.opLatex()}${sep}{%s}`;
    }

    latexArgs(syntax) {
        if (syntax) syntax[this.operator] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_approx extends LeanRelational {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '≈';
    }

    latexArgs(syntax) {
        if (syntax) syntax['≈'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_asymp extends LeanRelational {
    static { this.register(); }

    static input_priority = 50;

    get operator() {
        return '≍';
    }

    latexArgs(syntax) {
        if (syntax) syntax['≍'] = true;
        return super.latexArgs(syntax);
    }
}
export class LeanDvd extends LeanRelational {
    static { this.register(); }

    static input_priority = 50;

    get command() {
        return '{\\color{red}{\\ \\mid\\ }}';
    }

    get operator() {
        return '∣';
    }
}

export class Lean_ll extends LeanRelational {
    static { this.register(); }

    get operator() {
        return '≪';
    }
}

export class Lean_gg extends LeanRelational {
    static { this.register(); }

    get operator() {
        return '≫';
    }
}
