/**
 * Quantifiers: `LeanQuantifier`, `∀` (`Lean_forall`), and `∃` (`Lean_exists`).
 *
 * They extend `LeanProp(LeanBigOperator)`. `LeanBigOperator` and the concrete
 * big operators live in `bigops.js` and are created before this factory.
 * `Lean_partial` is filled on `quantifierLate` after the arithmetic
 * factory returns; methods only use it via `instanceof`.
 * This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanProp
 * @param {Function} deps.LeanBigOperator
 * @param {Function} deps.LeanArgsSpaceSeparated
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanIn
 * @param {Function} deps.LeanColon
 * @param {object} deps.quantifierLate
 */
export function createQuantifierFamily(deps) {
    const {
        LeanProp,
        LeanBigOperator,
        LeanArgsSpaceSeparated,
        LeanCaret,
        LeanIn,
        LeanColon,
        quantifierLate,
    } = deps;
    function lateClass(name) {
        function Ctor() {}
        Object.defineProperty(Ctor, Symbol.hasInstance, {
            value(inst) {
                const real = quantifierLate[name];
                if (real == null) throw new Error(`${name} used before quantifier registration`);
                return inst instanceof real;
            },
        });
        return Ctor;
    }
    const Lean_partial = lateClass('Lean_partial');

    /** Port of `LeanQuantifier`. */
    class LeanQuantifier extends LeanProp(LeanBigOperator) {
        static input_priority = 24;

        measurePartial() {
            if (this.superscript !== 'ᵐ') return null;
            const b = this.bound;
            if (!(b instanceof LeanArgsSpaceSeparated)) return null;
            for (let i = b.args.length - 1; i >= 0; i--) {
                if (b.args[i] instanceof LeanCaret) continue;
                return b.args[i] instanceof Lean_partial ? b.args[i] : null;
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
            if (this.superscript === 'ᶠ' && this.bound instanceof LeanArgsSpaceSeparated && this.scope) {
                const bound = this.bound.args
                    .filter((a) => !(a instanceof LeanCaret))
                    .map((a) => (a instanceof LeanIn ? `\\text{ in }{${a.arg.toLatex(syntax)}}` : a.toLatex(syntax)))
                    .join('\\ ');
                return [bound, this.scope.toLatex(syntax)];
            }
            const partial = this.measurePartial();
            if (!partial) return super.latexArgs(syntax);
            const bound = this.bound.args
                .filter((a) => a !== partial && !(a instanceof LeanCaret))
                .map((a) => a.toLatex(syntax))
                .join(' ');
            // keep the measure: `∀ᵐ a ∂μ, p` → `∀ᵐ a ∂μ, p`
            return [`${bound}\\ \\partial {${partial.arg.toLatex(syntax)}}`, this.scope.toLatex(syntax)];
        }

        get stack_priority() {
            return LeanColon.input_priority - 1;
        }
    }

    class Lean_forall extends LeanQuantifier {
        get baseOperator() {
            return '∀';
        }
    }

    class Lean_exists extends LeanQuantifier {
        unique = false;

        get baseOperator() {
            return this.unique ? '∃!' : '∃';
        }

        get command() {
            return this.unique ? '\\exists!' : '\\exists';
        }
    }


    return {
        LeanQuantifier,
        Lean_forall,
        Lean_exists,
    };
}
