import '../../std.js';

/**
 * Arithmetic operator family: binaries under `LeanArithmetic` (add, sub, mul,
 * div, pow, matmul, `×`, bit ops, modular, append) plus the unary helpers
 * that only serve this family.
 *
 * `LeanBinary` / `LeanUnary` and the class registry stay in `lean.js`. The
 * factory runs after those exist. A static import of the router from here
 * would cycle: the router evaluates this module before `extends` targets
 * are initialized.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanUnary
 * @param {{map: object|null}} deps.classRegistry filled with `LEAN_CLASSES` after this returns
 */
export function createArithmeticFamily(deps) {
    const {
        LeanBinary,
        LeanUnary,
        LeanCaret,
        LeanParenthesis,
        LeanToken,
        Lean_fun,
        LeanProperty,
        LeanColon,
        LeanQuantifier,
        LeanAbs,
        Lean_perp,
        LeanAngleBracket,
        LeanArgsCommaSeparated,
        LeanBracket,
        LeanPairedGroup,
        LeanArgsSpaceSeparated,
        LeanArgsNewLineSeparated,
        LeanStatements,
        LeanModule,
        classRegistry,
    } = deps;
    // `LEAN_CLASSES` is assembled in the router after these classes exist.
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before arithmetic registration');
            return map[key];
        },
    });

    class LeanArithmetic extends LeanBinary {
        static input_priority = 67;

        insert_newline(caret, newline_count, indent, next) {
            if (caret instanceof LeanCaret)
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

    class LeanAdd extends LeanArithmetic {
        static input_priority = 65;

        get command() {
            return '+';
        }

        get operator() {
            return '+';
        }
    }

    class LeanSub extends LeanArithmetic {
        static input_priority = 65;

        get command() {
            return '-';
        }

        get operator() {
            return '-';
        }
    }

    class LeanMul extends LeanArithmetic {
        static input_priority = 70;

        get command() {
            if (this.subscript) {
                const map = LeanToken.subscript;
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
                (rhs instanceof LeanParenthesis && rhs.arg instanceof LeanDiv) ||
                (rhs instanceof LeanToken && /^\d+$/.test(rhs.text)) ||
                (rhs instanceof LeanMul && rhs.command) ||
                (lhs instanceof LeanMul && lhs.command) ||
                lhs.is_space_separated() ||
                lhs instanceof LeanFDiv ||
                rhs instanceof LeanPow || 
                lhs instanceof LeanModular ||
                // juxtaposition would read as function application / swallow the lambda
                rhs instanceof Lean_fun ||
                (lhs instanceof LeanParenthesis && lhs.arg instanceof Lean_fun) ||
                (rhs.is_space_separated() && !(lhs instanceof LeanToken)) ||
                // `x.item * y.item` — two field accesses side by side read as one term
                (lhs instanceof LeanProperty && rhs instanceof LeanProperty)
            ) {
                return '\\cdot';
            }
            if (
                (lhs instanceof LeanToken &&
                    (rhs.is_space_separated() || (rhs instanceof LeanToken && rhs.starts_with_2_letters()))) ||
                (lhs instanceof LeanToken && lhs.ends_with_2_letters() && rhs instanceof LeanToken) ||
                lhs instanceof LeanProperty ||
                rhs instanceof LeanProperty
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
            if (rhs instanceof LeanParenthesis && rhs.arg instanceof LeanDiv) {
                rhs = rhs.arg;
            } else if (rhs instanceof LeanNeg) {
                rhs = new LeanParenthesis(rhs, this.indent, level);
                rhs.is_closed = true;
            }
            if (lhs instanceof LeanParenthesis && lhs.arg instanceof LeanDiv) {
                lhs = lhs.arg;
            } else if (lhs instanceof LeanNeg) {
                lhs = new LeanParenthesis(lhs, this.indent, level);
                lhs.is_closed = true;
            }
            return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
        }

        latexFormat() {
            const {command} = this;
            return `%s ${command} %s`;
        }
    }

    class Lean_times extends LeanArithmetic {
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
            const map = LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return `\\times_{${inner}}`;
        }
    }

    class LeanMatMul extends LeanArithmetic {
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

    class Lean_bullet extends LeanArithmetic {
        static input_priority = 73;

        get operator() {
            return '•';
        }
    }

    class Lean_odot extends LeanArithmetic {
        static input_priority = 73;

        get operator() {
            return '⊙';
        }
    }

    class Lean_otimes extends LeanArithmetic {
        static input_priority = 32;

        /** `⊗ₘ` — the subscript letter (e.g. the `ₘ` in the kernel tensor product). */
        subscript = '';

        get operator() {
            return this.subscript ? `⊗${this.subscript}` : '⊗';
        }

        get command() {
            if (!this.subscript) return '\\otimes';
            const map = LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return `\\otimes_{${inner}}`;
        }
    }

    /** Mathlib `⊗ₘ` / `⊗ₖ` (`infixl:100`): binds tighter than `*` and relations, unlike the repo's bare `⊗`. */
    class Lean_otimesSub extends Lean_otimes {
        static input_priority = 72;
    }

    class Lean_oplus extends LeanArithmetic {
        static input_priority = 30;

        get operator() {
            return '⊕';
        }
    }

    class LeanDiv extends LeanArithmetic {
        static input_priority = 70;

        get operator() {
            return '/';
        }

        latexArgs(syntax) {
            let lhs = this.lhs.peelLatexCoe();
            let rhs = this.rhs.peelLatexCoe();
            if (!(lhs instanceof LeanDiv)) {
                if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon))
                    lhs = lhs.arg;
                if (rhs instanceof LeanParenthesis && !(rhs.arg instanceof LeanColon))
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

    class LeanFDiv extends LeanArithmetic {
        static input_priority = 70;

        get command() {
            return '/\\!\\!/';
        }

        get operator() {
            return '//';
        }
    }

    class LeanBitAnd extends LeanArithmetic {
        static input_priority = 68;

        get command() {
            return '\\&';
        }

        get operator() {
            return '&';
        }
    }

    class LeanBitwiseAnd extends LeanArithmetic {
        static input_priority = 60;

        get command() {
            return '\\&\\!\\!\\&\\!\\!\\&';
        }

        get operator() {
            return '&&&';
        }
    }

    class LeanBitwiseXor extends LeanArithmetic {
        static input_priority = 60;

        get command() {
            return '\\^\\^\\^';
        }

        get operator() {
            return '^^^';
        }
    }

    class LeanBitOr extends LeanArithmetic {
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
            if (caret instanceof LeanToken) {
                const newCaret = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanBitOr(caret, newCaret, this.indent, caret.level));
                return newCaret;
            }
            if (caret instanceof LeanCaret) {
                this.replace(caret, new LeanAbs(caret, this.indent, caret.level));
                return caret;
            }
            throw new Error(`LeanBitOr.insert_bar: unexpected for ${this.constructor.name}`);
        }

        is_indented() {
            return false;
        }

        isProp(vars) {
            return this.lhs instanceof Lean_perp && this.lhs.isProp(vars);
        }

        latexArgs(syntax = null) {
            if (this.parent instanceof LeanQuantifier) {
                if (!syntax) syntax = {};
                syntax.setOf = true;
            }
            return super.latexArgs(syntax);
        }

        tokens_bar_separated() {
            const tokens = [];
            for (const arg of this.args) {
                if (arg instanceof LeanBitOr) tokens.push(...arg.tokens_bar_separated());
                else if (arg instanceof LeanAngleBracket) {
                    const ts = arg.tokens_comma_separated();
                    tokens.push(ts.length === 1 ? ts[0] : new LeanArgsCommaSeparated(ts, this.indent, this.level));
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
                t instanceof LeanToken ? t.text : t.map((x) => x.text).join(',');
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
                return new LeanArgsCommaSeparated(mapped, indent, 0);
            }
            const c = token.clone();
            c.indent = indent;
            return c;
        }
    }

    class LeanBitwiseOr extends LeanArithmetic {
        static input_priority = 55;

        get command() {
            return '|\\!\\!|\\!\\!|';
        }

        get operator() {
            return '|||';
        }
    }

    class LeanPow extends LeanArithmetic {
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
            if (this.rhs instanceof LeanBracket)
                return '%s^%s';
            return super.strFormat();
        }

        latexArgs(syntax) {
            let lhs = this.lhs.peelLatexCoe();
            let rhs = this.rhs.peelLatexCoe();
            if (lhs instanceof LeanParenthesis) {
                const inner = lhs.arg;
                if (inner instanceof Lean_sqrt || inner instanceof LeanPairedGroup ||
                    (inner instanceof LeanArgsSpaceSeparated && (inner.is_Abs() || inner.is_Bool())))
                    lhs = inner;
            }
            if (rhs instanceof LeanParenthesis)
                rhs = rhs.arg;
            const rhsLatex = rhs instanceof LeanDiv
                ? '\\left. {%s} \\right/ {%s}'.format(...rhs.latexArgs(syntax))
                : rhs.toLatex(syntax);
            return [lhs.toLatex(syntax), rhsLatex];
        }
    }

    class Lean_lll extends LeanArithmetic {
        get operator() {
            return '<<<';
        }
    }

    class Lean_ggg extends LeanArithmetic {
        static input_priority = 75;

        get operator() {
            return '>>>';
        }
    }

    class LeanModular extends LeanArithmetic {
        static input_priority = 70;

        get command() {
            return '\\%';
        }

        get operator() {
            return '%';
        }
    }

    class LeanConstruct extends LeanArithmetic {
        static input_priority = 67;

        get command() {
            if (!this.subscript) return '::';
            const map = LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return `::_${inner}`;
        }

        get operator() {
            return this.subscript ? `::${this.subscript}` : '::';
        }
    }

    class LeanAppend extends LeanArithmetic {
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

    class Lean_sqcup extends LeanArithmetic {
        static input_priority = 68;

        get operator() {
            return '⊔';
        }
    }

    class Lean_sqcap extends LeanArithmetic {
        static input_priority = 69;

        get operator() {
            return '⊓';
        }
    }

    class Lean_cdotp extends LeanArithmetic {
        static input_priority = 71;

        get operator() {
            return this.subscript ? `⬝${this.subscript}` : '⬝';
        }

        get command() {
            const base = '{\\color{red}\\cdotp}';
            if (!this.subscript) return base;
            const map = LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return `${base}_${inner}`;
        }
    }

    class Lean_circ extends LeanArithmetic {
        static input_priority = 90;

        /** `∘ₘ` — the subscript letter (e.g. the `ₘ` in subscript composition). */
        subscript = '';

        get operator() {
            return this.subscript ? `∘${this.subscript}` : '∘';
        }

        get command() {
            if (!this.subscript) return '\\circ';
            const map = LeanToken.subscript;
            const inner = [...this.subscript]
                .map((ch) => (map[ch] !== undefined ? map[ch] : ch))
                .join('');
            return `\\circ_{${inner}}`;
        }
    }

    class Lean_blacktriangleright extends LeanArithmetic {
        static input_priority = 75;

        get operator() {
            return '▸';
        }

        is_indented() {
            const p = this.parent;
            if (p instanceof LeanArgsNewLineSeparated) return true;
            // `LeanModule` subclasses `LeanStatements`; only non-module statement blocks get body indent.
            if (p instanceof LeanStatements && !(p instanceof LeanModule) && this.indent > 0) return true;
            return false;
        }
    }

    class LeanUnaryArithmetic extends LeanUnary {}

    class LeanUnaryArithmeticPost extends LeanUnaryArithmetic {
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
            if (arg instanceof LeanParenthesis) {
                const inner = arg.arg;
                if (inner instanceof Lean_sqrt || inner instanceof LeanPairedGroup ||
                    (inner instanceof LeanArgsSpaceSeparated && (inner.is_Abs() || inner.is_Bool())))
                    arg = inner;
            }
            return [arg.toLatex(syntax)];
        }

        replace(oldNode, newNode) {
            if (
                oldNode === this.arg &&
                newNode instanceof LeanArgsSpaceSeparated &&
                newNode.args[0] === oldNode
            ) {
                // Capture parent *before* constructing `app`: Args ctor reparents `this`.
                const parent = this.parent;
                if (!parent) throw new Error('LeanUnaryArithmeticPost.replace: no parent');
                // Keep operand under the postfix; lift juxtaposition above it.
                this.arg = oldNode;
                oldNode.parent = this;
                const app = new LeanArgsSpaceSeparated(
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
                const Ctor = LEAN_CLASSES[$new];
                const caret = new LeanCaret(indent, level);
                const node = new Ctor(caret, indent, level);
                if (this.parent instanceof LeanArgsSpaceSeparated) {
                    this.parent.push(node);
                } else {
                    this.parent.replace(this, new LeanArgsSpaceSeparated([this, node], indent, level));
                }
                return caret;
            }
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, $new], indent, level));
            return $new;
        }
    }

    class LeanUnaryArithmeticPre extends LeanUnaryArithmetic {
        strFormat() {
            return `${this.operator}%s`;
        }
        latexFormat() {
            return `${this.command}{%s}`;
        }
    }

    /** Leading bar of `μ[|s]` (Mathlib `ProbabilityTheory.cond`); lives directly inside the `[…]`. */
    class LeanCondBar extends LeanUnaryArithmeticPre {
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

    class Lean_partial extends LeanUnaryArithmeticPre {
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
    class LeanNeg extends LeanUnaryArithmeticPre {
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
            if (arg instanceof LeanParenthesis) {
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
    class LeanPlus extends LeanUnaryArithmeticPre {
        get operator() {
            return '+';
        }
        get command() {
            return '+';
        }
    }

    /** Postfix inverse `⁻¹`. Lean `postfix:max` (tighter than `^`). */
    class LeanInv extends LeanUnaryArithmeticPost {
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
    class LeanPreimage extends LeanUnaryArithmeticPost {
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
            if (arg instanceof LeanArgsSpaceSeparated) return [`\\left(${arg.toLatex(syntax)}\\right)`];
            return [arg.peelLatexCoe().toLatex(syntax)];
        }
        strFormat() {
            return this.spaced ? "%s ⁻¹'" : "%s⁻¹'";
        }
    }

    /** Postfix factorial `n !`. */
    class LeanFactorial extends LeanUnaryArithmeticPost {
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
    class LeanPosPart extends LeanUnaryArithmeticPost {
        static input_priority = 71;
        get operator() {
            return '⁺';
        }
        get command() {
            return '^{+}';
        }
    }

    /** Postfix negative part `⁻`. */
    class LeanNegPart extends LeanUnaryArithmeticPost {
        static input_priority = 71;
        get operator() {
            return '⁻';
        }
        get command() {
            return '^{-}';
        }
    }

    /** Square root `√`. */
    class Lean_sqrt extends LeanUnaryArithmeticPre {
        static input_priority = 72;
        get stack_priority() {
            return 71;
        }
        get operator() {
            return '√';
        }
        latexArgs(syntax) {
            let arg = this.arg.peelLatexCoe();
            if (arg instanceof LeanParenthesis) arg = arg.arg;
            return [arg.toLatex(syntax)];
        }
    }

    /** Prefix conjugate `~z` (`starRingEnd ℂ` / SymPy `~z`). */
    class LeanConj extends LeanUnaryArithmeticPre {
        static input_priority = 1024;
        get operator() {
            return '~';
        }
        get command() {
            return '\\overline';
        }
    }

    /** Postfix square `²`. */
    class LeanSquare extends LeanUnaryArithmeticPost {
        static input_priority = 66;
        get operator() {
            return '²';
        }
        get command() {
            return '^2';
        }
    }

    /** Cube root `∛`. */
    class LeanCubicRoot extends LeanUnaryArithmeticPre {
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
            if (arg instanceof LeanParenthesis) arg = arg.arg;
            return [arg.toLatex(syntax)];
        }
    }

    /** Up arrow `↑`. */
    class Lean_uparrow extends LeanUnaryArithmeticPre {
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
    class LeanUparrow extends LeanUnaryArithmeticPre {
        static input_priority = 1024;
        get stack_priority() {
            return 71;
        }
        get operator() {
            return '⇑';
        }
    }

    /** Postfix cube `³`. */
    class LeanCube extends LeanUnaryArithmeticPost {
        get operator() {
            return '³';
        }
        get command() {
            return '^3';
        }
    }

    /** Quartic root `∜`. */
    class LeanQuarticRoot extends LeanUnaryArithmeticPre {
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
            if (arg instanceof LeanParenthesis) arg = arg.arg;
            return [arg.toLatex(syntax)];
        }
    }

    /** Postfix fourth power `⁴`. */
    class LeanTesseract extends LeanUnaryArithmeticPost {
        get operator() {
            return '⁴';
        }
        get command() {
            return '^4';
        }
    }

    /** Postfix transpose `ᵀ`. */
    class LeanTranspose extends LeanUnaryArithmeticPost {
        get operator() {
            return 'ᵀ';
        }
        get command() {
            return '^{T}';
        }
    }

    /** Pipeline `|>`. */
    class LeanPipeForward extends LeanUnaryArithmeticPost {
        get operator() {
            return '|>';
        }
        strFormat() {
            return `%s ${this.operator}`;
        }
    }

    return {
        LeanArithmetic,
        LeanAdd,
        LeanSub,
        LeanMul,
        Lean_times,
        LeanMatMul,
        Lean_bullet,
        Lean_odot,
        Lean_otimes,
        Lean_otimesSub,
        Lean_oplus,
        LeanDiv,
        LeanFDiv,
        LeanBitAnd,
        LeanBitwiseAnd,
        LeanBitwiseXor,
        LeanBitOr,
        LeanBitwiseOr,
        LeanPow,
        Lean_lll,
        Lean_ggg,
        LeanModular,
        LeanConstruct,
        LeanAppend,
        Lean_sqcup,
        Lean_sqcap,
        Lean_cdotp,
        Lean_circ,
        Lean_blacktriangleright,
        LeanUnaryArithmetic,
        LeanUnaryArithmeticPost,
        LeanUnaryArithmeticPre,
        LeanCondBar,
        Lean_partial,
        LeanNeg,
        LeanPlus,
        LeanInv,
        LeanPreimage,
        LeanFactorial,
        LeanPosPart,
        LeanNegPart,
        Lean_sqrt,
        LeanConj,
        LeanSquare,
        LeanCubicRoot,
        Lean_uparrow,
        LeanUparrow,
        LeanCube,
        LeanQuarticRoot,
        LeanTesseract,
        LeanTranspose,
        LeanPipeForward,
    };
}
