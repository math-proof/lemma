/**
 * Leaf Lean nodes: caret, token, comments, and the empty binary token classes.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { escapeSpecialsForLatex } from './utility.js';
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanCaret extends Lean {
    static { this.register(); }

    append($new) {
        if (typeof $new === 'string') {
            $new = L[$new];
            this.parent.replace(this, new $new(this, this.indent, this.level));
            return this;
        }
        this.parent.replace(this, $new);
        return $new;
    }

    is_indented() {
        return this.parent instanceof L.LeanArgsNewLineSeparated;
    }

    is_outsider() {
        return true;
    }

    toJSON() {
        return '';
    }

    latexFormat() {
        return '';
    }

    push_accessibility($new, $accessibility) {
        const Ctor = L[$new];
        if (!Ctor) {
            throw new Error(`push_accessibility: unknown class "${$new}" (accessibility modifier "${$accessibility}")`);
        }
        this.parent.replace(this, new Ctor($accessibility, this, this.indent, this.level));
        return this;
    }

    push_block_comment(comment, docstring) {
        const parent = this.parent;
        const Cls = docstring ? LeanDocString : LeanBlockComment;
        parent.replace(this, new Cls(comment, this.indent, this.level));
        parent.push(this);
        return this;
    }

    push_left(func) {
        func = L[func];
        this.parent.replace(this, new func(this, this.indent, this.level));
        return this;
    }

    push_line_comment(comment) {
        const parent = this.parent;
        const $new = new LeanLineComment(comment, this.indent, this.level);
        parent.replace(this, $new);
        return $new;
    }

    strFormat() {
        return '';
    }
}

export class LeanToken extends Lean {
    static { this.register(); }

    /** @type {string} */
    text;

    /** @type {Record<string, unknown> | null} */
    cache = null;

    static subscript = {
        'ₐ': 'a',
        'ₑ': 'e',
        'ₕ': 'h',
        'ᵢ': 'i',
        'ⱼ': 'j',
        'ₖ': 'k',
        'ₗ': 'l',
        'ₘ': 'm',
        'ₙ': 'n',
        'ₒ': 'o',
        'ₚ': 'p',
        'ᵣ': 'r',
        'ₛ': 's',
        'ₜ': 't',
        'ᵤ': 'u',
        'ᵥ': 'v',
        'ₓ': 'x',
        '₀': '0',
        '₁': '1',
        '₂': '2',
        '₃': '3',
        '₄': '4',
        '₅': '5',
        '₆': '6',
        '₇': '7',
        '₈': '8',
        '₉': '9',
        'ᵦ': '\\beta',
        'ᵧ': '\\gamma',
        'ᵨ': '\\rho',
        'ᵩ': '\\phi',
        'ᵪ': '\\chi',
    };

    /** @type {RegExp | null} */
    static subscript_keys = null;

    static supscript = {
        '⁰': '0',
        '¹': '1',
        '²': '2',
        '³': '3',
        '⁴': '4',
        '⁵': '5',
        '⁶': '6',
        '⁷': '7',
        '⁸': '8',
        '⁹': '9',
        'ᵐ': '\\mathrm{m}',
        'ᶠ': '\\mathrm{f}',
        'ᵅ': 'alpha',
        'ᵝ': 'beta',
        'ᵞ': 'gamma',
        'ᵟ': 'delta',
        'ᵋ': 'epsilon',
        'ᵑ': 'eta',
        'ᶿ': 'theta',
        'ᶥ': 'iota',
        'ᶺ': 'lambda',
        'ᵚ': 'omega',
        'ᶹ': 'upsilon',
        'ᵠ': 'phi',
        'ᵡ': 'chi',
    };

    /** @type {RegExp | null} */
    static supscript_keys = null;

    static {
        const escClass = (/** @type {Record<string, string>} */ m) =>
            Object.keys(m)
                .map((k) => {
                    const ch = [...k][0];
                    return /[\]\\^-]/.test(ch) ? `\\${ch}` : k;
                })
                .join('');
        LeanToken.subscript_keys = new RegExp(`[${escClass(LeanToken.subscript)}]+`, 'u');
        LeanToken.supscript_keys = new RegExp(`[${escClass(LeanToken.supscript)}]+`, 'u');
    }

    /**
     * @param {string} text
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(text, indent, level, parent = null) {
        super(indent, level, parent);
        this.text = text;
    }

    clone() {
        const copy = super.clone();
        copy.cache = null;
        return copy;
    }

    append($new, $func) {
        // `f fun a ↦ body` / `lintegral_congr fun a ↦ …` — expr keywords arrive via
        // append(Lean_fun,'expr'), not push_token. Climbing to LeanAssign drops the
        // lambda (echo becomes `f ↦ body`). Mirror push_token: space-separate onto this.
        if (typeof $new === 'string' && ($func === 'expr' || $func === 'operator')) {
            const Ctor = L[$new];
            if (Ctor && this.parent) {
                const c = new LeanCaret(this.indent, this.level);
                const node = new Ctor(c, this.indent, this.level);
                this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, node], this.indent, this.level));
                return c;
            }
        }
        if (this.parent) return this.parent.insert(this, $new, $func);
    }

    ends_with_2_letters() {
        return /[a-zA-Z]{2,}$/.test(this.text);
    }

    equals(other) {
        if (other instanceof LeanToken) return this.text === other.text;
    }

    is_parallel_operator() {
        return /_\?+$/.test(this.text);
    }

    isProp(vars) {
        return (vars[this.text] ?? null) === 'Prop';
    }

    is_TypeStar() {
        switch (this.text) {
            case 'Sort':
            case 'Type':
            case 'ℝ':
                return true;
        }
    }

    is_variable() {
        return /^[a-zA-Z_][a-zA-Z_0-9]*$/.test(this.text);
    }

    toJSON() {
        return this.text;
    }

    latexArgs(_syntax) {
        return [];
    }

    latexFormat() {
        if (this.text === '∞') return '\\infty';
        if (/^[ℝℚ]≥0∞?$/u.test(this.text))
            return `${this.text[0]}_{\\ge 0}${this.text.endsWith('∞') ? '^{\\infty}' : ''}`;
        let text = escapeSpecialsForLatex(this.text);
        if (text === this.text) {
            const sk = LeanToken.subscript_keys;
            const spk = LeanToken.supscript_keys;
            const sub = LeanToken.subscript;
            const sup = LeanToken.supscript;
            if (sk) {
                text = text.replace(sk, (m) => {
                    const inner = [...m].map((ch) => (sub[ch] !== undefined ? sub[ch] : ch)).join('');
                    return `_{${inner}}`;
                });
            }
            if (spk) {
                text = text.replace(spk, (m) => {
                    const inner = [...m].map((ch) => (sup[ch] !== undefined ? sup[ch] : ch)).join('');
                    return `^{${inner}}`;
                });
            }
            if (text.startsWith('_')) text = `\\${text}`;
        }
        if (text.includes('%')) text = text.replace(/%/g, '\\%'); // `rv%` (rv-lifting sugar): `%` starts a LaTeX comment
        if (this.kwargs.isRandomArgument) return `{\\color{magenta} {${text}}}`;
        if (this.kwargs.isRandomVariable && !this.kwargs.neverRed) return `{\\color{red} {${text}}}`;
        return text;
    }

    lower() {
        this.text = this.text.toLowerCase();
        return this;
    }

    operand_count() {
        const m = /\?*$/.exec(this.text);
        return m ? m[0].length : 0;
    }

    push_quote(quote) {
        this.text += quote;
        return this;
    }

    push_token(word) {
        const level = this.level;
        const $new = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, $new], this.indent, level));
        return $new;
    }

    regexp() {
        return ['_'];
    }

    starts_with_2_letters() {
        return /^[a-zA-Z]{2,}/.test(this.text);
    }

    strFormat() {
        return this.text;
    }

    tactic_block_info() {
        const map = [];
        map[0] = [this];
        this.cache ??= {};
        this.cache.size = 1;
        return map;
    }

    tokens_space_separated() {
        return [this];
    }
}

export class LeanLineComment extends Lean {
    static { this.register(); }

    /**
     * @param {string} text
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(text, indent, level, parent = null) {
        super(indent, level, parent);
        this.text = text;
    }

    get operator() {
        return '--';
    }

    get command() {
        return '%';
    }

    is_comment() {
        return true;
    }

    is_indented() {
        switch (this.text) {
            case 'given': {
                let parent = this.parent;
                if (
                    parent instanceof L.LeanArgsNewLineSeparated &&
                    (parent = parent.parent) instanceof L.LeanArgsIndented &&
                    (parent = parent.parent) instanceof L.LeanColon &&
                    (parent = parent.parent) instanceof L.LeanAssign &&
                    parent.parent instanceof L.Lean_lemma
                )
                    return false;
                break;
            }
            case 'proof': {
                let parent = this.parent;
                if (parent instanceof L.LeanStatements) {
                    if (parent.parent instanceof L.LeanBy) parent = parent.parent;
                    if ((parent = parent.parent) instanceof L.LeanAssign && parent.parent instanceof L.Lean_lemma)
                        return false;
                } else if (parent instanceof L.LeanArgsNewLineSeparated) {
                    if ((parent = parent.parent) instanceof L.LeanAssign && parent.parent instanceof L.Lean_lemma)
                        return false;
                }
            }
            case 'imply': {
                let parent = this.parent;
                if (
                    parent instanceof L.LeanStatements &&
                    (parent = parent.parent) instanceof L.LeanColon &&
                    (parent = parent.parent) instanceof L.LeanAssign &&
                    parent.parent instanceof L.Lean_lemma
                )
                    return false;
                break;
            }
            default:
                if (this.parent instanceof L.LeanTactic) return false;
        }
        return true;
    }

    is_outsider() {
        return /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.test(this.text);
    }

    /** Stable fingerprint for `-- proof` / `-- imply` / `-- given`: indent can differ after re-parse. */
    toJSON() {
        const t = this.text;
        if (t === 'proof' || t === 'imply' || t === 'given') {
            return `  -- ${t}`;
        }
        const body = typeof t === 'string' ? t.trim() : t;
        return `${this.operator}${this.sep()}${body}`;
    }

    latexFormat() {
        if (this.text === 'imply' || this.text === 'given' || this.text === 'proof') return '';
        return `\\%${this.sep()}${this.text}`;
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `${this.operator}${this.sep()}${this.text}`;
    }
}

export class LeanBlockComment extends Lean {
    static { this.register(); }

    /**
     * @param {string} text
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(text, indent, level, parent = null) {
        super(indent, level, parent);
        this.text = text;
    }

    is_comment() {
        return true;
    }

    is_indented() {
        return true;
    }

    sep() {
        return '';
    }

    set_line(line) {
        this.line = line;
        return line + (this.text.match(/\n/g)?.length ?? 0);
    }

    strFormat() {
        return `/-${this.text}-/`;
    }

    toJSON() {
        return String(this);
    }
}

export class LeanDocString extends LeanBlockComment {
    static { this.register(); }

    /**
     * @param {string} text
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(text, indent, level, parent = null) {
        super(text, indent, level, parent);
    }

    is_indented() {
        return false;
    }

    set_line(line) {
        this.line = line;
        let lineNo = line + 1;
        lineNo += this.text.match(/\n/g)?.length ?? 0;
        return lineNo + 1;
    }

    strFormat() {
        return `/--\n${this.text}\n-/`;
    }
}

export class Lean_ominus extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_oslash extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_circledcirc extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_circledast extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_circleeq extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_circleddash extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_boxplus extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_boxminus extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_boxtimes extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class Lean_dotsquare extends LeanBinary {
    static { this.register(); }

    static input_priority = 67;
}

export class LeanEDiv extends LeanBinary {
    static { this.register(); }

    static input_priority = 70;
}
