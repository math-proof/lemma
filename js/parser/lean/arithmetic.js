/**
 * Arithmetic operator family: binaries under `LeanArithmetic` (add, sub, mul,
 * div, pow, matmul, `×`, bit ops, modular, append) plus the unary helpers
 * that only serve this family.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import '../../py.js';
import { LeanBinary, LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanArithmetic extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;

    insert_newline(caret, newline_count, indent, next) {
        if (caret instanceof L.LeanCaret)
            return caret;
        return this.parent.insert_newline(this, newline_count, indent, next);
    }

    sep() {
        return ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanAdd extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 65;

    get command() {
        return '+';
    }

    get operator() {
        return '+';
    }
}

export class LeanSub extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 65;

    get command() {
        return '-';
    }

    get operator() {
        return '-';
    }
}

export class LeanMul extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 70;

    get command() {
        if (this.subscript) {
            const map = L.LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return this.isLeftSubscript
                ? `\\;{}_${inner}\\!{\\color{red}*}`
                : `{\\color{red}*}_${inner}`;
        }
        const lhs = this.lhs;
        const rhs = this.rhs;
        if (
            (rhs instanceof L.LeanParenthesis && rhs.arg instanceof LeanDiv) ||
            (rhs instanceof L.LeanToken && /^\d+$/.test(rhs.text)) ||
            (rhs instanceof LeanMul && rhs.command) ||
            (lhs instanceof LeanMul && lhs.command) ||
            lhs.is_space_separated() ||
            lhs instanceof LeanFDiv ||
            rhs instanceof LeanPow || 
            lhs instanceof LeanModular ||
            // juxtaposition would read as function application / swallow the lambda
            rhs instanceof L.Lean_fun ||
            (lhs instanceof L.LeanParenthesis && lhs.arg instanceof L.Lean_fun) ||
            (rhs.is_space_separated() && !(lhs instanceof L.LeanToken)) ||
            // `x.item * y.item` — two field accesses side by side read as one term
            (lhs instanceof L.LeanProperty && rhs instanceof L.LeanProperty)
        ) {
            return '\\cdot';
        }
        if (
            (lhs instanceof L.LeanToken &&
                (rhs.is_space_separated() || (rhs instanceof L.LeanToken && rhs.starts_with_2_letters()))) ||
            (lhs instanceof L.LeanToken && lhs.ends_with_2_letters() && rhs instanceof L.LeanToken) ||
            lhs instanceof L.LeanProperty ||
            rhs instanceof L.LeanProperty
        ) {
            return '\\ ';
        }
        return '';
    }

    get operator() {
        if (!this.subscript) return '*';
        return this.isLeftSubscript ? `${this.subscript}*` : `*${this.subscript}`;
    }

    latexArgs(syntax) {
        let lhs = this.lhs;
        let rhs = this.rhs;
        const level = this.level;
        if (rhs instanceof L.LeanParenthesis && rhs.arg instanceof LeanDiv) {
            rhs = rhs.arg;
        } else if (rhs instanceof LeanNeg) {
            rhs = new L.LeanParenthesis(rhs, this.indent, level);
            rhs.is_closed = true;
        }
        if (lhs instanceof L.LeanParenthesis && lhs.arg instanceof LeanDiv) {
            lhs = lhs.arg;
        } else if (lhs instanceof LeanNeg) {
            lhs = new L.LeanParenthesis(lhs, this.indent, level);
            lhs.is_closed = true;
        }
        return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
    }

    latexFormat() {
        const {command} = this;
        return `%s ${command} %s`;
    }
}

export class Lean_times extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 72;

    /** @type {string | null} */
    superscript = null;

    /** `×ₖ` — the subscript letter (e.g. the `ₖ` in the kernel product). */
    subscript = '';

    get operator() {
        if (this.superscript) return `×${this.superscript}`;
        return this.subscript ? `×${this.subscript}` : '×';
    }

    get command() {
        if (!this.subscript) return '\\times';
        const map = L.LeanToken.subscript;
        const inner = [...this.subscript]
            .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
            .join('');
        return `\\times_{${inner}}`;
    }
}

export class LeanMatMul extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 70;

    get operator() {
        return '@';
    }

    get command() {
        return '{\\color{red}\\times}';
    }

    isMatMulContext() {
        return true;
    }
}

export class Lean_bullet extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 73;

    get operator() {
        return '•';
    }
}

export class Lean_odot extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 73;

    get operator() {
        return '⊙';
    }
}

export class Lean_otimes extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 32;

    /** `⊗ₘ` — the subscript letter (e.g. the `ₘ` in the kernel tensor product). */
    subscript = '';

    get operator() {
        return this.subscript ? `⊗${this.subscript}` : '⊗';
    }

    get command() {
        if (!this.subscript) return '\\otimes';
        const map = L.LeanToken.subscript;
        const inner = [...this.subscript]
            .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
            .join('');
        return `\\otimes_{${inner}}`;
    }
}

/** Mathlib `⊗ₘ` / `⊗ₖ` (`infixl:100`): binds tighter than `*` and relations, unlike the repo's bare `⊗`. */
export class Lean_otimesSub extends Lean_otimes {
    static { this.register(); }

    static input_priority = 72;
}

export class Lean_oplus extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 30;

    get operator() {
        return '⊕';
    }
}

export class LeanDiv extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 70;

    get operator() {
        return '/';
    }

    latexArgs(syntax) {
        let lhs = this.lhs.peelLatexCoe();
        let rhs = this.rhs.peelLatexCoe();
        if (!(lhs instanceof LeanDiv)) {
            if (lhs instanceof L.LeanParenthesis && !(lhs.arg instanceof L.LeanColon))
                lhs = lhs.arg;
            if (rhs instanceof L.LeanParenthesis && !(rhs.arg instanceof L.LeanColon))
                rhs = rhs.arg;
        }
        const rhsLatex = rhs instanceof LeanDiv
            ? '\\left. {%s} \\right/ {%s}'.format(...rhs.latexArgs(syntax))
            : rhs.toLatex(syntax);
        return [lhs.toLatex(syntax), rhsLatex];
    }

    latexFormat() {
        if (this.lhs instanceof LeanDiv) {
            return '\\left. {%s} \\right/ {%s}';
        }
        return '\\frac {%s} {%s}';
    }
}

export class LeanFDiv extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 70;

    get command() {
        return '/\\!\\!/';
    }

    get operator() {
        return '//';
    }
}

export class LeanBitAnd extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 68;

    get command() {
        return '\\&';
    }

    get operator() {
        return '&';
    }
}

export class LeanBitwiseAnd extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 60;

    get command() {
        return '\\&\\!\\!\\&\\!\\!\\&';
    }

    get operator() {
        return '&&&';
    }
}

export class LeanBitwiseXor extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 60;

    get command() {
        return '\\^\\^\\^';
    }

    get operator() {
        return '^^^';
    }
}

export class LeanBitOr extends LeanArithmetic {
    static { this.register(); }

    // Below Eq (50) and ∧ (35): Prob conditional `x = «x.bvar» | y = «y.bvar»`
    // must wrap whole equations, not nest `|` inside the first `=`.
    static input_priority = 33;

    get stack_priority() {
        return 32;
    }

    get operator() {
        return '|';
    }

    get command() {
        return '|';
    }

    insert_bar(caret, prevToken, next) {
        if (caret instanceof L.LeanToken) {
            const newCaret = new L.LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanBitOr(caret, newCaret, this.indent, caret.level));
            return newCaret;
        }
        if (caret instanceof L.LeanCaret) {
            this.replace(caret, new L.LeanAbs(caret, this.indent, caret.level));
            return caret;
        }
        throw new Error(`LeanBitOr.insert_bar: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
    }

    isProp(vars) {
        return this.lhs instanceof L.Lean_perp && this.lhs.isProp(vars);
    }

    latexArgs(syntax = null) {
        if (this.parent instanceof L.LeanQuantifier) {
            if (!syntax) syntax = {};
            syntax.setOf = true;
        }
        // CondIndep `X ⟂ᵢ[π] Y | Z` is `(X ⟂ᵢ[π] Y) | Z`: the conditioner `Z` is a random variable
        // too (red); `X` / `Y` are coloured by `Lean_perp.latexArgs`. Other `|` uses are untouched.
        if (L.Lean_perp.independenceOf(this.lhs)) L.Lean_perp.markRandomVariableTerm(this.rhs);
        return super.latexArgs(syntax);
    }

    tokens_bar_separated() {
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanBitOr) tokens.push(...arg.tokens_bar_separated());
            else if (arg instanceof L.LeanAngleBracket) {
                const ts = arg.tokens_comma_separated();
                tokens.push(ts.length === 1 ? ts[0] : new L.LeanArgsCommaSeparated(ts, this.indent, this.level));
            }
            else tokens.push(arg);
        }
        return tokens;
    }

    unique_token(indent) {
        let tokens = this.tokens_bar_separated();
        tokens = tokens.map((t) =>
            Array.isArray(t) ? t.filter((x) => x.text !== 'rfl') : t,
        );
        const key = (t) =>
            t instanceof L.LeanToken ? t.text : t.map((x) => x.text).join(',');
        const keys = tokens.map(key);
        if (new Set(keys).size !== 1) return;
        let token = tokens[0];
        if (Array.isArray(token) && token.length === 1) token = token[0];
        if (Array.isArray(token)) {
            const mapped = token.map((x) => {
                const c = x.clone();
                c.indent = indent;
                return c;
            });
            return new L.LeanArgsCommaSeparated(mapped, indent, 0);
        }
        const c = token.clone();
        c.indent = indent;
        return c;
    }
}

export class LeanBitwiseOr extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 55;

    get command() {
        return '|\\!\\!|\\!\\!|';
    }

    get operator() {
        return '|||';
    }
}

export class LeanPow extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 80;

    get operator() {
        return '^';
    }

    get command() {
        return '^';
    }

    get stack_priority() {
        return 79;
    }

    strFormat() {
        if (this.rhs instanceof L.LeanBracket)
            return '%s^%s';
        return super.strFormat();
    }

    latexArgs(syntax) {
        let lhs = this.lhs.peelLatexCoe();
        let rhs = this.rhs.peelLatexCoe();
        if (lhs instanceof L.LeanParenthesis) {
            const inner = lhs.arg;
            if (inner instanceof Lean_sqrt || inner instanceof L.LeanPairedGroup ||
                (inner instanceof L.LeanArgsSpaceSeparated && (inner.is_Abs() || inner.is_Bool())))
                lhs = inner;
        }
        if (rhs instanceof L.LeanParenthesis)
            rhs = rhs.arg;
        const rhsLatex = rhs instanceof LeanDiv
            ? '\\left. {%s} \\right/ {%s}'.format(...rhs.latexArgs(syntax))
            : rhs.toLatex(syntax);
        return [lhs.toLatex(syntax), rhsLatex];
    }
}

export class Lean_lll extends LeanArithmetic {
    static { this.register(); }

    get operator() {
        return '<<<';
    }
}

export class Lean_ggg extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 75;

    get operator() {
        return '>>>';
    }
}

export class LeanModular extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 70;

    get command() {
        return '\\%';
    }

    get operator() {
        return '%';
    }
}

export class LeanConstruct extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 67;

    get command() {
        if (!this.subscript) return '::';
        const map = L.LeanToken.subscript;
        const inner = [...this.subscript]
            .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
            .join('');
        return `::_${inner}`;
    }

    get operator() {
        return this.subscript ? `::${this.subscript}` : '::';
    }
}

export class LeanAppend extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 65;

    get command() {
        return '+\\!\\!+';
    }

    get operator() {
        return '++';
    }

    flattenAppend() {
        return this.lhs.flattenAppend().concat(this.rhs.flattenAppend());
    }

    latexArgs(syntax) {
        return this.matrixLatexArgs(syntax) ?? super.latexArgs(syntax);
    }

    latexFormat() {
        const rows = this.matrixLatexSpec();
        if (rows) return LeanAppend.bmatrixFormat(rows.length, rows[0].length);
        return super.latexFormat();
    }

    static bmatrixFormat(nrows, ncols) {
        const row = Array(ncols).fill('%s').join(' & ');
        return '\\begin{bmatrix} ' + Array(nrows).fill(row).join(' \\\\ ') + ' \\end{bmatrix}';
    }
}

export class Lean_sqcup extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 68;

    get operator() {
        return '⊔';
    }
}

export class Lean_sqcap extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 69;

    get operator() {
        return '⊓';
    }
}

export class Lean_cdotp extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 71;

    get operator() {
        return this.subscript ? `⬝${this.subscript}` : '⬝';
    }

    get command() {
        const base = '{\\color{red}\\cdotp}';
        if (!this.subscript) return base;
        const map = L.LeanToken.subscript;
        const inner = [...this.subscript]
            .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
            .join('');
        return `${base}_${inner}`;
    }
}

export class Lean_circ extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 90;

    /** `∘ₘ` — the subscript letter (e.g. the `ₘ` in subscript composition). */
    subscript = '';

    get operator() {
        return this.subscript ? `∘${this.subscript}` : '∘';
    }

    get command() {
        if (!this.subscript) return '\\circ';
        const map = L.LeanToken.subscript;
        const inner = [...this.subscript]
            .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
            .join('');
        return `\\circ_{${inner}}`;
    }
}

export class Lean_blacktriangleright extends LeanArithmetic {
    static { this.register(); }

    static input_priority = 75;

    get operator() {
        return '▸';
    }

    is_indented() {
        const p = this.parent;
        if (p instanceof L.LeanArgsNewLineSeparated) return true;
        // `LeanModule` subclasses `LeanStatements`; only non-module statement blocks get body indent.
        if (p instanceof L.LeanStatements && !(p instanceof L.LeanModule) && this.indent > 0) return true;
        return false;
    }
}

export class LeanUnaryArithmetic extends LeanUnary {
    static { this.register(); }
}

export class LeanUnaryArithmeticPost extends LeanUnaryArithmetic {
    static { this.register(); }

    static input_priority = 72;

    get stack_priority() {
        return 60;
    }
    strFormat() {
        return `%s${this.operator}`;
    }
    latexFormat() {
        return `{%s}${this.command}`;
    }
    latexArgs(syntax) {
        let arg = this.arg;
        // Parens around a self-delimiting expression (`|x|`, `Bool.toNat x`,
        // `\sqrt{x}`, `{…}`) are redundant before a postfix operator (`²`, `³`, `!`, …).
        if (arg instanceof L.LeanParenthesis) {
            const inner = arg.arg;
            if (inner instanceof Lean_sqrt || inner instanceof L.LeanPairedGroup ||
                (inner instanceof L.LeanArgsSpaceSeparated && (inner.is_Abs() || inner.is_Bool())))
                arg = inner;
        }
        return [arg.toLatex(syntax)];
    }

    replace(oldNode, newNode) {
        if (
            oldNode === this.arg &&
            newNode instanceof L.LeanArgsSpaceSeparated &&
            newNode.args[0] === oldNode
        ) {
            // Capture parent *before* constructing `app`: Args ctor reparents `this`.
            const parent = this.parent;
            if (!parent) throw new Error('LeanUnaryArithmeticPost.replace: no parent');
            // Keep operand under the postfix; lift juxtaposition above it.
            this.arg = oldNode;
            oldNode.parent = this;
            const app = new L.LeanArgsSpaceSeparated(
                [this, ...newNode.args.slice(1)],
                this.indent,
                this.level,
            );
            return parent.replace(this, app);
        }
        return super.replace(oldNode, newNode);
    }

    insert(caret, func, type) {
        if (this.arg === caret)
            return this.parent.insert(this, func, type);
        return super.insert(caret, func, type);
    }

    append($new, _func) {
        const {indent, level} = this;
        if (typeof $new === 'string') {
            const Ctor = L[$new];
            const caret = new L.LeanCaret(indent, level);
            const node = new Ctor(caret, indent, level);
            if (this.parent instanceof L.LeanArgsSpaceSeparated) {
                this.parent.push(node);
            } else {
                this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, node], indent, level));
            }
            return caret;
        }
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, $new], indent, level));
        return $new;
    }
}

export class LeanUnaryArithmeticPre extends LeanUnaryArithmetic {
    static { this.register(); }

    strFormat() {
        return `${this.operator}%s`;
    }
    latexFormat() {
        return `${this.command}{%s}`;
    }
}

/** Leading bar of `μ[|s]` (Mathlib `ProbabilityTheory.cond`); lives directly inside the `[…]`. */
export class LeanCondBar extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 10;
    get stack_priority() {
        return 5;
    }
    get operator() {
        return '|';
    }
    get command() {
        return '\\mid ';
    }
}

export class Lean_partial extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 75;
    get operator() {
        return '∂';
    }
    insert_comma(caret) {
        if (this.parent) return this.parent.insert_comma(this);
        throw new Error('Lean_partial.insert_comma: unexpected');
    }
}

/** Unary minus. */
export class LeanNeg extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 75;
    get operator() {
        return '-';
    }
    get command() {
        return '-';
    }
    sep() {
        return this.arg instanceof LeanNeg ? ' ' : '';
    }
    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }
    latexArgs(syntax) {
        let arg = this.arg;
        if (arg instanceof L.LeanParenthesis) {
            if (
                arg.arg instanceof LeanDiv ||
                (arg.arg instanceof LeanMul && !arg.arg.command)
            )
                arg = arg.arg;
        }
        return [arg.toLatex(syntax)];
    }
}

/** Unary plus. */
export class LeanPlus extends LeanUnaryArithmeticPre {
    static { this.register(); }

    get operator() {
        return '+';
    }
    get command() {
        return '+';
    }
}

/** Postfix inverse `⁻¹`. Lean `postfix:max` (tighter than `^`). */
export class LeanInv extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 1024;
    get operator() {
        return '⁻¹';
    }
    get command() {
        return '^{-1}';
    }
    latexArgs(syntax) {
        return [this.arg.peelLatexCoe().toLatex(syntax)];
    }
}

/** Postfix preimage `⁻¹'`. Lean `postfix:max` (same tightness as `⁻¹`). */
export class LeanPreimage extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 1024;
    get operator() {
        return "⁻¹'";
    }
    get command() {
        return '^{-1}';
    }
    latexArgs(syntax) {
        const {arg} = this;
        // `(s t)⁻¹` — an applied function must be bracketed, or it reads as `s (t⁻¹)`
        if (arg instanceof L.LeanArgsSpaceSeparated) return [`\\left(${arg.toLatex(syntax)}\\right)`];
        return [arg.peelLatexCoe().toLatex(syntax)];
    }
    strFormat() {
        return this.spaced ? "%s ⁻¹'" : "%s⁻¹'";
    }
}

/** Postfix factorial `n !`. */
export class LeanFactorial extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 10000;
    get operator() {
        return '!';
    }
    get command() {
        return '!';
    }
    strFormat() {
        return '%s !';
    }
}

/** Postfix positive part `⁺`. */
export class LeanPosPart extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 71;
    get operator() {
        return '⁺';
    }
    get command() {
        return '^{+}';
    }
}

/** Postfix negative part `⁻`. */
export class LeanNegPart extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 71;
    get operator() {
        return '⁻';
    }
    get command() {
        return '^{-}';
    }
}

/** Square root `√`. */
export class Lean_sqrt extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 72;
    get stack_priority() {
        return 71;
    }
    get operator() {
        return '√';
    }
    latexArgs(syntax) {
        let arg = this.arg.peelLatexCoe();
        if (arg instanceof L.LeanParenthesis) arg = arg.arg;
        return [arg.toLatex(syntax)];
    }
}

/** Prefix conjugate `~z` (`starRingEnd ℂ` / SymPy `~z`). */
export class LeanConj extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 1024;
    get operator() {
        return '~';
    }
    get command() {
        return '\\overline';
    }
}

/** Postfix square `²`. */
export class LeanSquare extends LeanUnaryArithmeticPost {
    static { this.register(); }

    static input_priority = 66;
    get operator() {
        return '²';
    }
    get command() {
        return '^2';
    }
}

/** Cube root `∛`. */
export class LeanCubicRoot extends LeanUnaryArithmeticPre {
    static { this.register(); }

    get stack_priority() {
        return 71;
    }
    get operator() {
        return '∛';
    }
    get command() {
        return '\\sqrt[3]';
    }
    latexArgs(syntax) {
        let arg = this.arg;
        if (arg instanceof L.LeanParenthesis) arg = arg.arg;
        return [arg.toLatex(syntax)];
    }
}

/** Up arrow `↑`. */
export class Lean_uparrow extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 1024;
    get stack_priority() {
        return 70;
    }
    get operator() {
        return '↑';
    }
    peelLatexCoe() {
        return this.arg.peelLatexCoe();
    }
}

/** Double up arrow `⇑`. */
export class LeanUparrow extends LeanUnaryArithmeticPre {
    static { this.register(); }

    static input_priority = 1024;
    get stack_priority() {
        return 71;
    }
    get operator() {
        return '⇑';
    }
}

/** Postfix cube `³`. */
export class LeanCube extends LeanUnaryArithmeticPost {
    static { this.register(); }

    get operator() {
        return '³';
    }
    get command() {
        return '^3';
    }
}

/** Quartic root `∜`. */
export class LeanQuarticRoot extends LeanUnaryArithmeticPre {
    static { this.register(); }

    get stack_priority() {
        return 71;
    }
    get operator() {
        return '∜';
    }
    get command() {
        return '\\sqrt[4]';
    }
    latexArgs(syntax) {
        let arg = this.arg;
        if (arg instanceof L.LeanParenthesis) arg = arg.arg;
        return [arg.toLatex(syntax)];
    }
}

/** Postfix fourth power `⁴`. */
export class LeanTesseract extends LeanUnaryArithmeticPost {
    static { this.register(); }

    get operator() {
        return '⁴';
    }
    get command() {
        return '^4';
    }
}

/** Postfix transpose `ᵀ`. */
export class LeanTranspose extends LeanUnaryArithmeticPost {
    static { this.register(); }

    get operator() {
        return 'ᵀ';
    }
    get command() {
        return '^{T}';
    }
}

/** Pipeline `|>`. */
export class LeanPipeForward extends LeanUnaryArithmeticPost {
    static { this.register(); }

    get operator() {
        return '|>';
    }
    strFormat() {
        return `%s ${this.operator}`;
    }
}
