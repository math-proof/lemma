import '../std.js';
import { IndentedNode, AbstractParser, Closable } from './node.js';
import { tactics } from '../../codemirror/mode/lean/tactics.js';
import { createArithmeticFamily } from './lean/arithmetic.js';
import { createPairedFamily } from './lean/paired.js';
import { createLogicFamily } from './lean/logic.js';
import { createSetFamily } from './lean/set.js';
import { createRelationalFamily } from './lean/relational.js';
import { createMembershipFamily } from './lean/membership.js';
import { createQuantifierFamily } from './lean/quantifier.js';
import { createBigOpsFamily } from './lean/bigops.js';
import { createIndexingFamily } from './lean/indexing.js';
import { createArrowsFamily } from './lean/arrows.js';
import { createNegationFamily } from './lean/negation.js';
import { createMatchFamily } from './lean/match.js';
import { createIteFamily } from './lean/ite.js';
import { createArgsFamily } from './lean/args.js';
import { createTacticFamily } from './lean/tactic.js';
import { createDeclFamily } from './lean/decl.js';
import { createFunFamily } from './lean/fun.js';
import { createBaseFamily } from './lean/base.js';

/** Relational / comparison ops; reused by token2classname and leanInfixContinue. */
const leanRelationalTokens = Object.freeze({
    '∈': 'Lean_in',
    '∉': 'Lean_notin',
    '<': 'Lean_lt',
    '≪': 'Lean_ll',
    '<=': 'Lean_le',
    '>': 'Lean_gt',
    '≫': 'Lean_gg',
    '>=': 'Lean_ge',
    '⊆': 'Lean_subseteq',
    '⊂': 'Lean_subset',
    '⊇': 'Lean_supseteq',
    '⊃': 'Lean_supset',
    '↔': 'Lean_leftrightarrow',
    '≠': 'Lean_ne',
    '≡': 'Lean_equiv',
    '≢': 'LeanNotEquiv',
    '≍': 'Lean_asymp',
    '≃': 'Lean_simeq',
    '≈': 'Lean_approx',
    '∣': 'LeanDvd',
});

export const token2classname = Object.freeze({
    '+': 'LeanAdd',
    '-': 'LeanSub',
    '*': 'LeanMul',
    '/': 'LeanDiv',
    '÷': 'LeanEDiv',
    '//': 'LeanFDiv',
    '%': 'LeanModular',
    '×': 'Lean_times',
    '@': 'LeanMatMul',
    '•': 'Lean_bullet',
    '⬝': 'Lean_cdotp',
    '∘': 'Lean_circ',
    '▸': 'Lean_blacktriangleright',
    '⊙': 'Lean_odot',
    '⊕': 'Lean_oplus',
    '⊖': 'Lean_ominus',
    '⊗': 'Lean_otimes',
    '⊘': 'Lean_oslash',
    '⊚': 'Lean_circledcirc',
    '⊛': 'Lean_circledast',
    '⊜': 'Lean_circleeq',
    '⊝': 'Lean_circleddash',
    '⊞': 'Lean_boxplus',
    '⊟': 'Lean_boxminus',
    '⊠': 'Lean_boxtimes',
    '⊡': 'Lean_dotsquare',
    '|': 'LeanBitOr',
    '&': 'LeanBitAnd',
    '||': 'LeanLogicOr',
    '|||': 'LeanBitwiseOr',
    '&&': 'LeanLogicAnd',
    '&&&': 'LeanBitwiseAnd',
    '^': 'LeanPow',
    '^^': 'LeanLogicXor',
    '^^^': 'LeanBitwiseXor',
    '<<<': 'Lean_lll',
    '>>>': 'Lean_ggg',
    '∨': 'Lean_lor',
    '∧': 'Lean_land',
    '∪': 'Lean_cup',
    '∩': 'Lean_cap',
    '\\': 'Lean_setminus',
    '|>.': 'LeanMethodChaining',
    '<|': 'Lean_lazy',
    '⊔': 'Lean_sqcup',
    '⊓': 'Lean_sqcap',
    '++': 'LeanAppend',
    '::': 'LeanConstruct',
    '→': 'Lean_rightarrow',
    '↦': 'Lean_mapsto',
    ...leanRelationalTokens,
});

/**
 * Infix tokens that continue a prior expression after a newline (`lhs\n  op rhs`).
 * `leanRelationalTokens` plus specials parsed outside token2classname.
 */
export const leanInfixContinue = Object.freeze({
    '=': 'LeanEq',
    '≤': 'Lean_le',
    '≥': 'Lean_ge',
    '∼': 'Lean_simeq',
    '⟂': 'Lean_perp',
    ...leanRelationalTokens,
});

function leanIsInfixContinue(next) {
    return Object.hasOwn(leanInfixContinue, next);
}


/** Lean identifier continuation token (supports Unicode letters like Ξ). */
function isIdentContinueToken(s) {
    if ('ᵀ²³⁴'.includes(s)) return false;
    return /^[\p{L}\p{N}_'!?₀-₉]+$/u.test(s);
}

function escapeSpecialsForLatex(token) {
    let s = String(token);
    if (s.startsWith('.')) return s.replace(/_/g, '\\_');
    // leading underscores (`_hPxy_z`) are part of the name, never a subscript
    const m = /^(_*)([^\W_]\w*?)_(.+)$/.exec(s);
    if (m) {
        const [, lead, head, tail] = m;
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        const escLead = lead.replace(/_/g, '\\_');
        return !lead && head.length === 1 ? `${head}_{${escTail}}` : `${escLead}${head}\\_${escTail}`;
    }
    if (/\w_$/.test(s)) return s.slice(0, -1) + '\\_';
    return s;
}

/**
 * Whether `target` appears in the Lean subtree rooted at `node` (args / arg / lhs / rhs).
 * @param {unknown} node
 * @param {unknown} target
 */
function leanSubtreeContains(node, target) {
    if (node == null || typeof node !== 'object') return false;
    if (node === target) return true;
    const o = node;
    if (Array.isArray(o.args)) {
        for (const a of o.args) if (leanSubtreeContains(a, target)) return true;
    }
    if (o.arg != null && leanSubtreeContains(o.arg, target)) return true;
    if (o.lhs != null && leanSubtreeContains(o.lhs, target)) return true;
    if (o.rhs != null && leanSubtreeContains(o.rhs, target)) return true;
    return false;
}

/**
 * When `,` is typed after a token whose parent is `LeanArgsSpaceSeparated` under a `LeanTactic`
 * (e.g. `use 0, head` inside a `match` arm), `Lean.insert_comma` would bubble the space-separated
 * node and hit `LeanBar.insert_comma` on the enclosing `LeanRightarrow`. Forward the **leaf** to
 * the tactic only in this one-hop shape (not every tactic ancestor — that breaks binders elsewhere).
 * @param {import('./node.js').Node} leaf
 */
function leanInsertComma(leaf) {
    const p = leaf.parent;
    if (
        p instanceof LeanArgsSpaceSeparated &&
        p.parent instanceof LeanTactic &&
        leanSubtreeContains(p.parent.arg, leaf)
    ) {
        return p.parent.insert_comma(leaf);
    }
    if (leaf.parent) return leaf.parent.insert_comma(leaf);
}

/**
 * Innermost still-open `LeanAbs` whose inner subtree contains `caret` (walk up from `from`).
 * Used so a second `|` closes `|a|` instead of starting another abs when `next` is not ` ` / `)` / EOF.
 * @param {import('./node.js').Node} from
 * @param {unknown} caret
 */
function findInnermostOpenLeanAbsAncestor(from, caret) {
    for (let p = from; p; p = p.parent) {
        if (!(p instanceof LeanAbs)) continue;
        if (p.is_closed === true) continue;
        if (caret != null && leanSubtreeContains(p.arg, caret)) return p;
    }
    return null;
}

const baseLate = {};
const arithmeticClassRegistry = { map: null };
const baseFamily = createBaseFamily({
    IndentedNode,
    token2classname,
    tactics,
    findInnermostOpenLeanAbsAncestor,
    isIdentContinueToken,
    leanInsertComma,
    strStmt,
    classRegistry: arithmeticClassRegistry,
    baseLate,
});
export const Lean = baseFamily.Lean;

export class LeanCaret extends Lean {
    append($new) {
        if (typeof $new === 'string') {
            $new = LEAN_CLASSES[$new];
            this.parent.replace(this, new $new(this, this.indent, this.level));
            return this;
        }
        this.parent.replace(this, $new);
        return $new;
    }

    is_indented() {
        return this.parent instanceof LeanArgsNewLineSeparated;
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
        const Ctor = LEAN_CLASSES[$new];
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
        func = LEAN_CLASSES[func];
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
            const Ctor = LEAN_CLASSES[$new];
            if (Ctor && this.parent) {
                const c = new LeanCaret(this.indent, this.level);
                const node = new Ctor(c, this.indent, this.level);
                this.parent.replace(this, new LeanArgsSpaceSeparated([this, node], this.indent, this.level));
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
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, $new], this.indent, level));
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
                    parent instanceof LeanArgsNewLineSeparated &&
                    (parent = parent.parent) instanceof LeanArgsIndented &&
                    (parent = parent.parent) instanceof LeanColon &&
                    (parent = parent.parent) instanceof LeanAssign &&
                    parent.parent instanceof Lean_lemma
                )
                    return false;
                break;
            }
            case 'proof': {
                let parent = this.parent;
                if (parent instanceof LeanStatements) {
                    if (parent.parent instanceof LeanBy) parent = parent.parent;
                    if ((parent = parent.parent) instanceof LeanAssign && parent.parent instanceof Lean_lemma)
                        return false;
                } else if (parent instanceof LeanArgsNewLineSeparated) {
                    if ((parent = parent.parent) instanceof LeanAssign && parent.parent instanceof Lean_lemma)
                        return false;
                }
            }
            case 'imply': {
                let parent = this.parent;
                if (
                    parent instanceof LeanStatements &&
                    (parent = parent.parent) instanceof LeanColon &&
                    (parent = parent.parent) instanceof LeanAssign &&
                    parent.parent instanceof Lean_lemma
                )
                    return false;
                break;
            }
            default:
                if (this.parent instanceof LeanTactic) return false;
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

class LeanBlockComment extends Lean {
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

class LeanDocString extends LeanBlockComment {
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
        let L = line + 1;
        L += this.text.match(/\n/g)?.length ?? 0;
        return L + 1;
    }

    strFormat() {
        return `/--\n${this.text}\n-/`;
    }
}

/**
 * @template {typeof LeanArgs} T
 * @param {T} Base
 */
export function LeanMultipleLine(Base) {
    return class extends Base {
        set_line(line) {
            this.line = line;
            for (const arg of this.args) {
                line = arg.set_line(line) + 1;
            }
            return line - 1;
        }
    };
}

/**
 * @template {typeof Lean} T
 * @param {T} Base
 */
export function LeanProp(Base) {
    return class extends Base {
        /**
         * @param {Record<string, unknown>} [_vars]
         */
        isProp(_vars) {
            return true;
        }
    };
}

/**
 * @template {typeof LeanArgs} T
 * @param {T} Base
 */
export function LeanGetElemBase(Base) {
    return class extends Base {
        insert_comma(caret) {
            let $new = new LeanCaret(this.indent, caret.level);
            const commaSep = new LeanArgsCommaSeparated([caret, $new], this.indent, $new.level);
            this.args[1] = commaSep;
            commaSep.parent = this;
            return $new;
        }

        push_token(word) {
            const level = this.level;
            const newTok = new LeanToken(word, this.indent, level);
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
            return newTok;
        }

        /** `Measurable[m] fun ω => …` — like `LeanToken.append`: the `fun`/`match` is the next argument. */
        append($new, $func) {
            if (typeof $new === 'string' && ($func === 'expr' || $func === 'operator')) {
                const Ctor = LEAN_CLASSES[$new];
                if (Ctor && this.parent) {
                    const c = new LeanCaret(this.indent, this.level);
                    const node = new Ctor(c, this.indent, this.level);
                    this.parent.replace(this, new LeanArgsSpaceSeparated([this, node], this.indent, this.level));
                    return c;
                }
            }
            return super.append($new, $func);
        }

        is_space_separated() {
            const prop = this.args[0];
            if (!(prop instanceof LeanProperty)) return false;
            if (prop.is_space_separated()) return true;
            const spec = this.propertyGetElemLatex(null, '');
            return spec != null && (spec.format.match(/%s/g) || []).length === 1;
        }

        /**
         * `θ.f[i]` — index belongs on `θ`, not as a subscript of the already-rendered `θ.f`.
         * Uses `f`'s own property LaTeX, with the first argument replaced by `θ_i`.
         */
        propertyGetElemLatex(syntax, indexLatex) {
            const prop = this.args[0];
            if (!(prop instanceof LeanProperty) || !(prop.rhs instanceof LeanToken)) return null;
            const fmt = prop.latexFormat();
            const args = prop.latexArgs(syntax);
            if (!args.length || !fmt.includes('%s')) return null;
            args[0] = `{${prop.lhs.toLatex(syntax)}}_{${indexLatex}}`;
            return {format: fmt, args};
        }

        push_right(funcName) {
            if (funcName === 'LeanBracket') return this;
            return super.push_right(funcName);
        }
    };
}

/**
 * @template {typeof LeanBinary} T
 * @param {T} Base
 */
export function LeanGetElemBaseBinary(Base) {
    return class extends LeanGetElemBase(Base) {
        get stack_priority() {
            return 18;
        }

        sep() {
            return '';
        }
    };
}

/**
 * Cartesian product of string columns (port of `itertools\product` in `LeanArgs::regexp`).
 * @param {string[][]} cols
 * @returns {string[][]}
 */
function regexpProductCols(cols) {
    if (cols.length === 0) return [[]];
    const [first, ...rest] = cols;
    const tail = regexpProductCols(rest);
    const out = [];
    for (const x of first) {
        for (const t of tail) {
            out.push([x, ...t]);
        }
    }
    return out;
}

export class LeanArgs extends Lean {
    static input_priority = 47;

    /**
     * Deep-clone `args` and reparent children (same pattern as `LeanArgs::__clone` / `Lean.prototype.clone`).
     * @returns {this}
     */
    clone() {
        const copy = Object.create(Object.getPrototypeOf(this));
        Object.assign(copy, this);
        copy.parent = null;
        copy.args = this.args.map((a) => {
            if (a == null) return a;
            if (typeof a.clone === 'function') return a.clone();
            return a;
        });
        for (const a of copy.args) {
            if (a && typeof a === 'object') a.parent = copy;
        }
        return copy;
    }

    /**
     * @param {Lean[]} args
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(args, indent, level, parent = null) {
        super(indent, level, parent);
        this.args = args;
        for (const a of args) if (a) a.parent = this;
    }

    get func() {
        return this.constructor.name.replace(/^Lean_?/, '');
    }

    get command() {
        return '\\' + this.func;
    }

    insert_calc(caret) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            this.replace(caret, new LeanCalc(caret, caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_calc: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, func) {
        if (caret instanceof LeanCaret) {
            this.replace(caret, new LeanTactic(func, caret, caret.indent, caret.level));
            return caret;
        }
        return this.insert_word(caret, func);
    }

    toJSON() {
        const mapped = this.args.map((a) => (a == null ? a : a.toJSON()));
        let i = 0;
        while (i < mapped.length && mapped[i] === '') i++;
        let j = mapped.length;
        while (j > i && mapped[j - 1] === '') j--;
        return i === 0 && j === mapped.length ? mapped : mapped.slice(i, j);
    }

    push_args_indented(indent, newline_count, functionCall = true) {
        const end = this.args[this.args.length - 1];
        if (
            !functionCall ||
            end instanceof LeanToken ||
            end instanceof LeanProperty ||
            end instanceof LeanParenthesis
        ) {
            const caret = new LeanCaret(indent, end.level);
            const nl = new LeanArgsNewLineSeparated([caret], indent, caret.level);
            const c = nl.push_newlines(newline_count - 1);
            this.replace(end, new LeanArgsIndented(end, nl, this.indent, c.level));
            return c;
        }
    }

    regexp() {
        const f = this.func;
        const head = f.length > 0 ? f.charAt(0).toUpperCase() + f.slice(1) : f;
        const cols = this.args.map((arg) => [...arg.regexp(), '_']);
        return regexpProductCols(cols).map((list) => head + list.join(''));
    }

    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            if (arg != null) line = arg.set_line(line);
        }
        return line;
    }

    /**
     * @returns {Lean[]}
     */
    strip_parenthesis() {
        return this.args.map((arg) => {
            if (!(arg instanceof LeanParenthesis)) return arg;
            const inner = arg.arg;
            if (
                inner instanceof LeanMethodChaining ||
                inner instanceof Lean_rightarrow ||
                inner instanceof LeanColon
            )
                return arg;
            return inner;
        });
    }

    *traverse() {
        yield this;
        for (const arg of this.args) {
            if (arg != null) yield* arg.traverse();
        }
    }
}

export class LeanUnary extends LeanArgs {
    static input_priority = 47;

    constructor(arg, indent, level, parent = null) {
        super([], indent, level, parent);
        this.args = [arg];
        arg.parent = this;
    }

    get arg() {
        return this.args[0];
    }
    set arg(v) {
        this.args[0] = v;
        v.parent = this;
    }

    insert_if(caret) {
        if (this.arg === caret && caret instanceof LeanCaret) {
            this.arg = new LeanIte([caret], caret.indent, caret.level);
            return caret;
        }
        if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    toJSON() {
        return this.arg.toJSON();
    }

    replace(oldNode, newNode) {
        if (this.arg !== oldNode) {
            throw new Error(`replace: assert failed in ${this.constructor.name}`);
        }
        this.arg = newNode;
    }
}

// Paired delimiters live in ./lean/paired.js and are registered beside LEAN_CLASSES.

export class LeanBinary extends LeanArgs {
    static input_priority = 47;

    /**
     * @param {Lean} lhs
     * @param {Lean} rhs
     * @param {number} indent
     * @param {number} level
     */
    constructor(lhs, rhs, indent, level) {
        super([lhs, rhs], indent, level);
    }

    get lhs() {
        return this.args[0];
    }

    set lhs(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get rhs() {
        return this.args[1];
    }

    set rhs(v) {
        this.args[1] = v;
        if (v) v.parent = this;
    }

    insert_if(caret) {
        if (this instanceof LeanArgsIndented && caret instanceof LeanCaret) {
            const last = this.args[this.args.length - 1];
            if (last === caret) return caret.parent.insert_ite(caret);
            if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
            throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
        }
        if (this.rhs === caret || (this.rhs != null && leanSubtreeContains(this.rhs, caret))) {
            return caret.parent.insert_ite(caret);
        }
        if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, func) {
        // consider the case where `arg` is a tactic within (LeanColon/LeanAdd):
        // (h : arg x + arg y ∈ Ioc (-Real.pi) Real.pi) :
        return this.insert_word(caret, func);
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }

    latexFormat() {
        return `{%s} ${this.command} {%s}`;
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    set_line(line) {
        this.line = line;
        line = this.lhs.set_line(line);
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.rhs.set_line(line);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.parent instanceof LeanTactic && indent > this.indent) {
            return this.parent.push_args_indented(indent, newline_count, false);
        }
        if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
    }

    /** Source-code operator token; derived from token2classname reverse lookup. */
    get operator() {
        const name = this.constructor.name;
        const pair = Object.entries(token2classname).find(([, cls]) => cls === name);
        return pair ? pair[0] : null;
    }

    /** String format using operator token. */
    strFormat() {
        const op = this.operator;
        if (op == null) return super.strFormat();
        const sep = this.sep();
        return `%s ${op}${sep}%s`;
    }
}

/**
 * Interval notation `a..b` used by `∫ x in a..b, f x` (Mathlib `notation3 "a".."b"`).
 * Binds looser than arithmetic/relational nodes, matching the term-level parsing of the bounds.
 */
export class LeanUpto extends LeanBinary {
    static input_priority = 49; // LeanRelational::$input_priority - 1

    get operator() {
        return '..';
    }

    get command() {
        return '..';
    }

    strFormat() {
        return '%s' + this.sep() + '..%s';
    }

    latexFormat() {
        return '%s' + this.sep() + '..%s';
    }

    sep() {
        return this.rhs instanceof LeanCaret ? ' ' : '';
    }
}

export class LeanProperty extends LeanBinary {
    static input_priority = 81; // LeanPow::$input_priority + 1

    get stack_priority() {
        return 87;
    }

    get operator() {
        return '.';
    }

    get command() {
        return '.';
    }

    equals(other) {
        if (other instanceof LeanProperty) {
            return this.lhs.equals(other.lhs) && this.rhs.equals(other.rhs);
        }
        return false;
    }

    insert(caret, func, type) {
        if (this.rhs === caret) {
            if (caret instanceof LeanCaret) {
                if (func.startsWith('Lean_')) {
                    return this.insert_word(caret, func.slice(5));
                }
            } else if (type === 'modifier') {
                return this.parent.insert(this, func, type);
            } else {
                const newCaret = new LeanCaret(this.indent, caret.level);
                this.parent.replace(
                    this,
                    new LeanArgsSpaceSeparated(
                        [this, new (LEAN_CLASSES[func])(newCaret, newCaret.indent, newCaret.level)],
                        this.indent,
                        newCaret.level
                    )
                );
                return newCaret;
            }
        }
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }

    insert_left(caret, func, prevToken = '') {
        if (func === 'LeanDoubleAngleQuotation') {
            return caret.push_left(func, prevToken);
        }
        if (this.parent) {
            return this.parent.insert_left(this, func, prevToken);
        }
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.parent instanceof LeanTactic && indent > this.indent) {
            return this.parent.push_args_indented(indent, newline_count, false);
        }
        return this.parent.insert_newline(this, newline_count, indent, next);
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    insert_unary(caret, func) {
        if (this.parent) {
            return this.parent.insert_unary(this, func);
        }
    }

    insert_word(caret, word) {
        if (caret instanceof LeanCaret) {
            return super.insert_word(caret, word);
        }
        if (this.parent) {
            return this.parent.insert_word(this, word);
        }
    }

    is_indented() {
        const parent = this.parent;
        return parent instanceof LeanArgsCommaNewLineSeparated ||
            parent instanceof LeanArgsNewLineSeparated ||
            parent instanceof LeanStatements ||
            (parent instanceof LeanArgsIndented && parent.rhs === this) ||
            (parent instanceof LeanIte && !parent.inline && parent.else === this);
    }

    isProp(vars) {
        const rhs = this.rhs;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'Infinite':
                case 'Infinitesimal':
                case 'InfinitePos':
                case 'InfiniteNeg':
                    return true;
            }
        }
    }

    is_space_separated() {
        const rhs = this.rhs;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    return true;
            }
        }
        return false;
    }

    latexArgs(syntax = null) {
        const [lhs, rhs] = this.args;
        var arg;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    arg = '%s';
                    if (lhs instanceof LeanToken) {
                        switch (lhs.text) {
                            case 'Real':
                            case 'Complex':
                            case 'Exp':
                                arg = null;
                        }
                    }
                    if (arg) {
                        const exponent = this.lhs instanceof LeanParenthesis ? this.lhs.arg : this.lhs;
                        return [exponent.toLatex(syntax)];
                    }
                    break;
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    arg = '%s';
                    if (lhs instanceof LeanToken) {
                        switch (lhs.text) {
                            case 'Real':
                            case 'Complex':
                            case 'Cos':
                            case 'Sin':
                            case 'Tan':
                            case 'Log':
                                arg = null;
                        }
                    }
                    if (arg)
                        return [this.lhs.toLatex(syntax)];
                    break;
                case 'fmod':
                    return [this.lhs.toLatex(syntax)];
                case 'card':
                    if (!(lhs instanceof LeanToken && this.parent instanceof LeanArgsSpaceSeparated && this.parent.args[0] === this)) {
                        let arg = this.lhs;
                        if (arg instanceof LeanParenthesis && !(arg.arg instanceof LeanColon))
                            arg = arg.arg;
                        return [arg.toLatex(syntax)];
                    }
                    break;
                case 'softmax':
                    if (syntax) syntax.softmax = true;
                    break;
                case 'sigmoid':
                    return [this.lhs.toLatex(syntax)];
                case 'factorial':
                    return [this.lhs.toLatex(syntax)];
                case 'det': {
                    let arg = this.lhs;
                    if (arg instanceof LeanParenthesis && !(arg.arg instanceof LeanColon))
                        arg = arg.arg;
                    return [arg.toLatex(syntax)];
                }
                case 'natAbs': {
                    let arg = this.lhs;
                    if (arg instanceof LeanParenthesis) arg = arg.arg;
                    if (arg instanceof LeanColon) arg = arg.lhs;
                    return [arg.toLatex(syntax)];
                }
            }
        }
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const [lhs, rhs] = this.args;
        var arg;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    arg = '%s';
                    if (lhs instanceof LeanToken) {
                        switch (lhs.text) {
                            case 'Real':
                            case 'Complex':
                            case 'Exp':
                                arg = null;
                        }
                    }
                    if (arg) {
                        return '{\\color{RoyalBlue} e} ^ {%s}';
                    }
                    break;
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    arg = '%s';
                    if (lhs instanceof LeanToken) {
                        switch (lhs.text) {
                            case 'Real':
                            case 'Complex':
                            case 'Cos':
                            case 'Sin':
                            case 'Tan':
                            case 'Log':
                                arg = null;
                        }
                    }
                    if (arg)
                        return `\\\\${rhs.text} {%s}`;
                    break;
                case 'fmod':
                    return '{%s} {\\color{red}\\%%}';
                case 'card':
                    if (!(lhs instanceof LeanToken && this.parent instanceof LeanArgsSpaceSeparated && this.parent.args[0] === this)) {
                        return '\\left|{%s}\\right|';
                    }
                    break;
                case 'epsilon':
                    if (lhs instanceof LeanToken && lhs.text === 'Hyperreal') {
                        return '0^+';
                    }
                    break;
                case 'omega':
                    if (lhs instanceof LeanToken && lhs.text === 'Hyperreal') {
                        return '\\infty';
                    }
                    break;
                case 'sigmoid':
                    return '{\\color{RoyalBlue}\\sigma}\\left(%s\\right)';
                case 'factorial':
                    return '{%s}!';
                case 'det':
                    return '\\left|{%s}\\right|';
                case 'natAbs':
                    return '\\left|{%s}\\right|';
            }
        }
        return `{%s}${this.command}{%s}`;
    }

    push_attr(caret) {
        return super.push_attr(caret);
    }

    push_token(word) {
        const level = this.level;
        const newToken = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newToken], this.indent, level));
        return newToken;
    }

    regexp() {
        const str = String(this.rhs);
        const func = str.charAt(0).toUpperCase() + str.slice(1);
        let regexp = this.lhs.regexp().map(expr => `${func}${expr}`);
        regexp.push(`${func}_`);
        return regexp;
    }

    sep() {
        return '';
    }

    strFormat() {
        return `%s${this.operator}%s`;
    }

    // JS-only extensions (alphabetical order)

    /** Unwrap LeanArgsSpaceSeparated to get the actual token (handles import/open dotted names). */
    strArgs() {
        let rhs = this.rhs;
        if (rhs instanceof LeanArgsSpaceSeparated && rhs.args.length === 2 && rhs.args[0] instanceof LeanCaret) {
            rhs = rhs.args[1];
        }
        return [this.lhs, rhs];
    }
}

/** Type ascription / declaration colon. */
export class LeanColon extends LeanBinary {
    static input_priority = 19;

    get operator() {
        return ':';
    }

    get command() {
        return ':';
    }

    insert(caret, func, type) {
        if (this.rhs === caret && !(caret instanceof LeanCaret) && type !== 'modifier') {
            const c = new LeanCaret(this.indent, caret.level);
            const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
            this.rhs = new LeanArgsSpaceSeparated(
                [caret, new Ctor(c, this.indent, caret.level)],
                this.indent,
                caret.level,
            );
            return c;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.rhs === caret) {
            if (!(caret instanceof LeanCaret) && indent > this.indent && leanIsInfixContinue(next)) {
                return caret;
            }
            if (caret instanceof LeanCaret && indent >= this.indent) {
                if (indent === this.indent) indent = this.indent + 2;
                caret.indent = indent;
                const stmts = new LeanStatements([caret], indent, caret.level);
                this.replace(caret, stmts);
                return caret;
            }
            if (caret instanceof LeanStatements && indent === this.indent && this.parent instanceof LeanParenthesis)
                return caret;
            // `have h : Tendsto (f)\n      atTop (𝓝 0) := …` — a deeper line continues a complete type;
            // without this the line escapes to the enclosing statements and `:=` binds outside the `have`.
            if (
                this.parent instanceof Lean_let && indent > this.indent && next !== ':' &&
                (caret instanceof LeanArgsSpaceSeparated || caret instanceof LeanToken ||
                    caret instanceof LeanProperty || caret instanceof LeanParenthesis)
            ) {
                const $new = new LeanCaret(indent, caret.level);
                const nl = new LeanArgsNewLineSeparated([$new], indent, $new.level);
                const c = nl.push_newlines(newline_count - 1);
                this.replace(caret, new LeanArgsIndented(caret, nl, caret.indent, c.level));
                return c;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        return false;
    }

    peelLatexCoe() {
        return this.lhs.peelLatexCoe();
    }

    /**
     * `(0 : Tensor α [n, m])` / `(1 : Tensor α [n, m])` → shape cells for `\mathbf{0}_{n,m}`.
     * @returns {Lean[] | null}
     */
    tensorTypeShape() {
        let ty = this.rhs;
        if (ty instanceof LeanParenthesis) ty = ty.arg;
        if (!(ty instanceof LeanArgsSpaceSeparated)) return null;
        const args = ty.args.filter((a) => !(a instanceof LeanCaret));
        if (args.length < 2) return null;
        const head = args[0];
        if (!(head instanceof LeanToken) || head.text !== 'Tensor') return null;
        const shape = args[args.length - 1];
        if (shape instanceof LeanBracket) {
            const inner = shape.arg;
            if (!inner || inner instanceof LeanCaret) return [];
            if (inner instanceof LeanArgsCommaSeparated)
                return inner.args.filter((a) => !(a instanceof LeanCaret));
            return [inner];
        }
        return [shape];
    }

    isZeroOneTensor() {
        const lhs = this.lhs;
        return (
            lhs instanceof LeanToken &&
            (lhs.text === '0' || lhs.text === '1') &&
            this.tensorTypeShape() != null
        );
    }

    latexFormat() {
        if (this.isZeroOneTensor()) return `\\mathbf{${this.lhs.text}}_{%s}`;
        return super.latexFormat();
    }

    latexArgs(syntax) {
        if (this.isZeroOneTensor()) {
            const dims = this.tensorTypeShape();
            return [dims.map((d) => d.toLatex(syntax)).join(',')];
        }
        return super.latexArgs(syntax);
    }

    sep() {
        const rhs = this.rhs;
        return rhs instanceof LeanStatements ? '\n' : (rhs instanceof LeanCaret || this.parent instanceof LeanGetElem ? '' : ' ');
    }

    strArgs() {
        let lhs = this.lhs;
        const rhs = this.rhs;
        if (lhs instanceof LeanArgsNewLineSeparated) {
            const la = lhs.args;
            const tail = la.slice(1).map((arg) => String(arg));
            lhs = [String(la[0]), ...tail].join('\n');
        }
        return [lhs, rhs];
    }

    strFormat() {
        const sep = this.sep();
        let first = '%s';
        if (!(this.parent instanceof LeanGetElem)) {
            if (sep === ' ') {
                first += ' ';
            } else if (sep === '\n') {
                const L = this.lhs;
                // `lemma main:\n-- imply` stays tight; `{binders} :\n-- imply` and indented binder blocks
                // `  (h : …) :\n-- imply` keep a space before `:`.
                if (L instanceof LeanBrace || L instanceof LeanParenthesis || L instanceof LeanArgsIndented)
                    first += ' ';
            }
        }
        return `${first}${this.operator}${sep}%s`;
    }
}

export class LeanAssign extends LeanBinary {
    static input_priority = 18;

    get operator() {
        return ':=';
    }

    get command() {
        return ':=';
    }

    echo() {
        this.rhs.echo();
        if (this.lhs && typeof this.lhs.echo === 'function') this.lhs.echo();
    }

    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent < indent) {
            if (caret === this.rhs) {
                let out = caret;
                if (caret instanceof LeanCaret) {
                    caret.indent = indent;
                    this.rhs = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                    out = this.rhs.push_newlines(newline_count - 1);
                } else if (caret instanceof LeanArgsNewLineSeparated) {
                    if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
                } else {
                    if (this.parent instanceof LeanCalc)
                        return this.parent.insert_newline(this, newline_count, indent, next);
                    const p = this.parent;
                    const brace = p instanceof LeanBrace ? p
                        : (p instanceof LeanStatements && p.parent instanceof LeanBrace) ? p.parent
                        : null;
                    if (brace && brace.indent < indent)
                        return brace.insert_newline(this, newline_count, indent, next);
                    out = this.push_args_indented(indent, newline_count, false);
                }
                return out;
            }
            throw new Error(`insert_newline is unexpected for ${this.constructor.name}`);
        }
        if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
    }

    insert_tactic(caret, type) {
        return this.insert_word(caret, type);
    }

    is_indented() {
        const p = this.parent;
        if (!p || p instanceof LeanArgsNewLineSeparated) return true;
        if (p instanceof LeanArgsIndented && p.rhs === this) return true;
        // Structure-instance fields inside a brace: `{ toFun := …, map_add' := … }`
        if (p instanceof LeanStatements && p.parent instanceof LeanBrace) return true;
        return false;
    }

    relocate_last_comment() {
        this.rhs.relocate_last_comment();
    }

    sep() {
        const rhs = this.rhs;
        if (rhs instanceof LeanArgsNewLineSeparated) {
            const lines = rhs.args;
            const l0 = lines[0];
            const l1 = lines[1];
            if (lines.length > 2 || !(l1 instanceof LeanArgsNewLineSeparated) || l0 instanceof LeanLineComment) {
                return '\n';
            }
        }
        if (rhs instanceof LeanArgsIndented) {
            return '\n';
        }
        if (
            rhs instanceof Lean_blacktriangleright &&
            rhs.lhs instanceof LeanArgsNewLineSeparated &&
            rhs.lhs.args[0] instanceof LeanLineComment
        ) {
            return '\n';
        }
        return ' ';
    }

    split(syntax) {
        const {rhs} = this;
        if (rhs instanceof LeanBy && rhs.arg instanceof LeanStatements) {
            const self = this.clone();
            const stmts = rhs.arg;
            self.rhs.arg = new LeanCaret(rhs.indent, rhs.level);
            const statements = [self];
            stmts.swap_echo_star(syntax, statements);
            return statements;
        }
        if (rhs instanceof LeanCalc) {
            if (syntax) syntax.calc = true;
            const self = this.clone();
            const calc = self.rhs;
            const statements = calc.split(syntax);
            calc.arg = new LeanCaret(calc.indent, calc.level);
            statements[0] = self;
            return statements;
        }
        return [this];
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanBinaryBoolean extends LeanProp(LeanBinary) {
    append(new_, type) {
        const {indent, level} = this;
        const caret = new LeanCaret(indent, level);
        if (typeof new_ === 'string') {
            const Ctor = LEAN_CLASSES[new_];
            const newNode = new Ctor(caret, indent, level);
            this.rhs = new LeanArgsSpaceSeparated([this.rhs, newNode], indent, level);
            return caret;
        } else {
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, new_], indent, level));
            return new_;
        }
    }

    insert_colon(caret) {
        if (caret === this.rhs) {
            const newCaret = new LeanCaret(caret.indent, caret.level);
            this.parent.replace(this, new LeanColon(this, newCaret, caret.indent, caret.level));
            return newCaret;
        }
        return caret.push_binary(LeanColon);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.rhs === caret && caret instanceof LeanCaret && indent >= this.indent) {
            caret.indent = indent;
            return caret;
        }
        if (this.rhs === caret && indent > this.indent) {
            return this.parent.push_args_indented(indent, newline_count, false);
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    is_indented() {
        const {parent} = this;
        return parent instanceof LeanStatements || (parent instanceof LeanArgsNewLineSeparated && this.indent > 0);
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

const relationalFamily = createRelationalFamily({
    LeanBinaryBoolean,
    LeanToken,
    escapeSpecialsForLatex,
});
export const LeanRelational = relationalFamily.LeanRelational;
export const Lean_gt = relationalFamily.Lean_gt;
export const Lean_ge = relationalFamily.Lean_ge;
export const Lean_lt = relationalFamily.Lean_lt;
export const Lean_le = relationalFamily.Lean_le;
export const LeanEq = relationalFamily.LeanEq;
export const Lean_perp = relationalFamily.Lean_perp;
export const LeanBEq = relationalFamily.LeanBEq;
export const Lean_bne = relationalFamily.Lean_bne;
export const Lean_ne = relationalFamily.Lean_ne;
export const Lean_equiv = relationalFamily.Lean_equiv;
export const LeanNotEquiv = relationalFamily.LeanNotEquiv;
export const Lean_simeq = relationalFamily.Lean_simeq;
export const Lean_approx = relationalFamily.Lean_approx;
export const Lean_asymp = relationalFamily.Lean_asymp;
export const LeanDvd = relationalFamily.LeanDvd;
export const Lean_ll = relationalFamily.Lean_ll;
export const Lean_gg = relationalFamily.Lean_gg;

const membershipLate = {};
const membershipFamily = createMembershipFamily({
    LeanBinaryBoolean,
    LeanColon,
    membershipLate,
});
export const Lean_in = membershipFamily.Lean_in;
export const Lean_notin = membershipFamily.Lean_notin;
export const Lean_leftrightarrow = membershipFamily.Lean_leftrightarrow;

// Arithmetic operators live in ./lean/arithmetic.js and are registered beside LEAN_CLASSES.

/** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
export class Lean_lazy extends LeanBinary {
    static input_priority = 20;
    get stack_priority() {
        return 19;
    }
}

/** Pipeline `|>.`. */
export class LeanMethodChaining extends LeanBinary {
    static input_priority = 67;

    get stack_priority() {
        return 59;
    }

    latexFormat() {
        return '%s\\ \\texttt{|>.}%s';
    }

    sep() {
        return '';
    }

    strFormat() {
        return '%s |>.%s';
    }
}

const indexingLate = {};
const indexingFamily = createIndexingFamily({
    LeanGetElemBase,
    LeanGetElemBaseBinary,
    LeanBinary,
    LeanArgs,
    LeanToken,
    LeanColon,
    LeanProperty,
    indexingLate,
});
export const LeanGetElem = indexingFamily.LeanGetElem;
export const LeanGetWhiteSquareBracket = indexingFamily.LeanGetWhiteSquareBracket;
export const LeanGetElemQue = indexingFamily.LeanGetElemQue;
export const LeanGetElemQuote = indexingFamily.LeanGetElemQuote;

/** `is`. */
export class Lean_is extends LeanBinary {
    static input_priority = 62;

    get operator() {
        return 'is';
    }

    get command() {
        return '{\\color{blue}\\text{is}}';
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    latexFormat() {
        return `{%s}\\ ${this.command}\\ {%s}`;
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

/** `is not`. */
export class Lean_is_not extends LeanBinary {
    static input_priority = 62;

    get command() {
        return '{\\color{blue}\\text{is not}}';
    }

    get operator() {
        return 'is not';
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

const logicLate = {};
const logicFamily = createLogicFamily({
    LeanBinaryBoolean,
    LeanCaret,
    logicLate,
});
export const LeanLogic = logicFamily.LeanLogic;
export const LeanLogicAnd = logicFamily.LeanLogicAnd;
export const LeanLogicOr = logicFamily.LeanLogicOr;
export const LeanLogicXor = logicFamily.LeanLogicXor;
export const Lean_lor = logicFamily.Lean_lor;
export const Lean_land = logicFamily.Lean_land;

const setFamily = createSetFamily({
    LeanBinary,
    LeanBinaryBoolean,
    LeanLogic,
});
export const LeanSetOperator = setFamily.LeanSetOperator;
export const Lean_setminus = setFamily.Lean_setminus;
export const Lean_cup = setFamily.Lean_cup;
export const Lean_cap = setFamily.Lean_cap;
export const Lean_subseteq = setFamily.Lean_subseteq;
export const Lean_subset = setFamily.Lean_subset;
export const Lean_supseteq = setFamily.Lean_supseteq;
export const Lean_supset = setFamily.Lean_supset;


/**
 * Conjuncts of a `∧` chain whose source breaks a line after some `∧`, else null.
 * @param {unknown} node
 */
function landMultilineConjuncts(node) {
    if (!(node instanceof Lean_land)) return null;
    const out = [];
    let multiline = false;
    const walk = (n) => {
        if (n instanceof Lean_land) {
            if (n.hanging_indentation) multiline = true;
            walk(n.lhs);
            walk(n.rhs);
        } else out.push(n instanceof LeanParenthesis ? n.arg : n); // own line: parentheses are redundant
    };
    walk(node);
    return multiline && out.length > 1 ? out : null;
}

/**
 * LaTeX for an `imply` conclusion: a `∧` chain written on several lines renders one conjunct per line.
 * @param {any} node
 * @param {any} syntax
 */
function implyConclusionLatex(node, syntax) {
    const parts = landMultilineConjuncts(node);
    if (!parts) return node.toLatex ? node.toLatex(syntax) : strStmt(node);
    const rows = parts.map(
        (c, i) => `&${c.toLatex ? c.toLatex(syntax) : strStmt(c)}${i < parts.length - 1 ? ' \\land' : ''}`,
    );
    return '\\begin{align*}\n' + rows.join('\\\\\n') + '\n\\end{align*}';
}

/**
 * `align*` for imply statements that start with `have`/`let`: one row per statement, and a
 * `∧` chain written on several lines contributes one row per conjunct.
 * @param {any[]} imply
 * @param {any} syntax
 */
function implyLetAlignLatex(imply, syntax) {
    const tex = (n) => (n.toLatex ? n.toLatex(syntax) : strStmt(n));
    const rows = [];
    for (const st of imply) {
        const parts = landMultilineConjuncts(st);
        if (parts) parts.forEach((c, i) => rows.push(`&${tex(c)}${i < parts.length - 1 ? ' \\land' : ''}&& `));
        else rows.push(`&${tex(st)}&& `);
    }
    return '\\begin{align*}\n' + rows.join('\\\\\n') + '\n\\end{align*}';
}

/**
 * Multiline `LeanStatements` is used both for proof scripts (`by …`) and for proposition/type text after `:`.
 * Tactic names that overlap with term names (e.g. `arg`) must parse as words in the latter case.
 * @param {LeanStatements} stmts
 */
function leanStatementsPreferWordOverTactic(stmts) {
    for (let p = stmts.parent; p; p = p.parent) {
        if (p instanceof LeanBy || p instanceof LeanFrom) {
            return false;
        }
        let ch = stmts;
        while (ch.parent !== p) {
            if (!ch.parent) break;
            ch = ch.parent;
        }
        if (ch.parent !== p) continue;
        if (p instanceof LeanColon && p.rhs === ch) return true;
        if (p instanceof LeanBrace && p.arg === ch) {
            /** `repeat { simp only … }` / `try { … }` — tactic block, not a term `{ … }`. */
            let q = p.parent;
            while (q instanceof LeanArgsSpaceSeparated) q = q.parent;
            return !(q instanceof LeanTactic && q.is_inline_tactic_block());
        }
        if ((p instanceof Lean_rightarrow || p instanceof Lean_mapsto) && p.rhs === ch) return true;
    }
    return false;
}



export class LeanStatements extends LeanMultipleLine(LeanArgs) {
    get stack_priority() {
        return LeanColon.input_priority;
    }

    push_binary(Ctor) {
        const parent = this.parent;
        if (!parent) return undefined;
        let idx = this.args.length - 1;
        while (idx >= 0) {
            const c = this.args[idx];
            if (c instanceof LeanCaret || c instanceof LeanLineComment || c instanceof LeanBlockComment) {
                idx--;
                continue;
            }
            break;
        }

        if (Ctor.input_priority > this.stack_priority) {
            if (idx >= 0) {
                const origin = this.args[idx];
                while (
                    this.args.length - 1 > idx &&
                    this.args[this.args.length - 1] instanceof LeanCaret
                ) {
                    this.args.pop();
                }
                const caret = new LeanCaret(origin.indent, origin.level);
                this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
                return caret;
            }
            return super.push_binary(Ctor);
        }

        if ((Ctor !== LeanAssign && Ctor !== LeanColon) || !(parent instanceof LeanBrace))
            return super.push_binary(Ctor);
        if (idx < 0) return super.push_binary(Ctor);
        const origin = this.args[idx];
        const caret = new LeanCaret(origin.indent, origin.level);
        this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
        return caret;
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret && leanStatementsPreferWordOverTactic(this)) {
            return this.insert_word(caret, token);
        }
        return super.insert_tactic(caret, token);
    }

    insert_semicolon(caret) {
        if (caret instanceof LeanTactic) return caret.insert_semicolon(caret.arg);
        return super.insert_semicolon(caret);
    }

    echo() {
        const {args} = this;
        let count = args.length;
        let void_lines = 0;
        while (count > 0) {
            const last = args[count - 1];
            if (last instanceof LeanCaret || last instanceof LeanLineComment || last instanceof LeanBlockComment) {
                count--;
                void_lines++;
            } else break;
        }
        let index = 0;
        for (; index < args.length - void_lines - 1; ++index) {
            const result = args[index].echo();
            if (Array.isArray(result)) {
                const length = result.shift();
                if (
                    index + 1 < args.length - void_lines &&
                    args[index + 1] instanceof LeanTactic &&
                    args[index + 1].tacticName === 'try' &&
                    result.length === 2 &&
                    result[0] === args[index] &&
                    result[1] instanceof LeanTactic &&
                    result[1].tacticName === 'echo'
                ) {
                    const e = result[1];
                    result[1] = new LeanTactic('try', e, e.indent, e.level);
                }
                for (const echo of result) echo.parent = this;
                // A head tactic followed by statement-level `LeanBitOr` lines
                // forms one multi-line alternative group (`first | …`,
                // `rcases … | …`): trailing `echo` placeholders must stay after
                // the whole group, never between the head and its `|` branches
                // (the latter generates invalid Lean: `first echo ⊢ | …`).
                let barRun = 0;
                for (let j = index + length; j < args.length - void_lines && args[j] instanceof LeanBitOr; j++) barRun++;
                const trailingEchoes = [];
                if (barRun) {
                    while (result.length > 1 && result[result.length - 1] instanceof LeanTactic && result[result.length - 1].tacticName === 'echo') {
                        trailingEchoes.unshift(result.pop());
                    }
                }
                const increment = result.indexOf(args[index]);
                args.splice(index, length, ...result);
                if (trailingEchoes.length) {
                    args.splice(index + result.length + barRun, 0, ...trailingEchoes);
                }
                index += increment;
            }
        }
        const tactic = args[index];
        if (tactic instanceof LeanTactic || tactic instanceof Lean_match) {
            const result = tactic.echo();
            if (Array.isArray(result)) {
                const length = result.shift();
                const pos = result.indexOf(tactic);
                if (pos >= 0) {
                    while (result.length > pos + 1) {
                        const tail = result[result.length - 1];
                        if (tail instanceof LeanTactic && tail.tacticName === 'echo') result.pop();
                        else break;
                    }
                }
                for (const echo of result) echo.parent = this;
                args.splice(index, length, ...result);
            } else if (tactic.tacticName === 'case') {
                const arrow = tactic.arrow;
                if (arrow && arrow.rhs instanceof LeanStatements) arrow.rhs.echo();
            } else {
                const w = tactic.with;
                if (w) {
                    if (w.sep() === '\n') {
                        for (const c of w.args) c.echo();
                    } else if (tactic.sequential_tactic_combinator) {
                        const block = tactic.sequential_tactic_combinator.arg;
                        if (block instanceof LeanTacticBlock) block.echo();
                        else tactic.sequential_tactic_combinator.echo();
                    }
                } else if (tactic.sequential_tactic_combinator) {
                    tactic.sequential_tactic_combinator.echo();
                } else {
                    const rb = tactic.repeat_block();
                    if (rb) rb.echo();
                    const {using} = tactic;
                    if (using) using.echo();
                }
            }
        } else if (tactic instanceof LeanTacticBlock || tactic instanceof LeanIte || tactic instanceof LeanCalc) {
            tactic.echo();
        }
    }

    insert_if(caret) {
        if (!(caret instanceof LeanCaret)) return undefined;
        const last = this.args[this.args.length - 1];
        if (last !== caret) return undefined;
        this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
        return caret;
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent > indent) return super.insert_newline(caret, newline_count, indent, next);
        if (this.indent < indent) {
            if (!leanIsInfixContinue(next)) {
                const c = this.push_args_indented(indent, newline_count);
                if (c) return c;
            }
            // See `LeanModule.insert_newline` — fall through when last arg cannot be wrapped.
        }
        for (let k = 0; k < newline_count; ++k) {
            caret = new LeanCaret(indent, caret.level);
            this.push(caret);
        }
        return caret;
    }

    is_indented() {
        return false;
    }

    isProp(vars) {
        const args = this.args;
        if (args.length === 1) return args[0].isProp(vars);
    }

    toJSON() {
        let args = super.toJSON();
        if (this.args.length && this.args[this.args.length - 1] instanceof LeanCaret) {
            args = args.slice(0, -1);
        }
        if (args.length === 1) return args[0];
        return args;
    }

    latexFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        if (n === 1) return '%s';
        const stmt = Array(n).fill('&{%s}&& ').join('\\\\\n');
        const p = this.parent;
        if (p && p instanceof LeanBy) return stmt;
        let align =  (p instanceof LeanRelational || p instanceof LeanBinary || p instanceof LeanStack || p instanceof LeanIte) ? 'aligned': 'align*';
        return `\\begin{${align}}\n${stmt}\n\\end{${align}}`;
    }

    relocate_last_comment() {
        for (let index = this.args.length - 1; index >= 0; --index) {
            const end = this.args[index];
            if (end.is_outsider()) {
                let self = this;
                let parent = null;
                while (self) {
                    parent = self.parent;
                    if (parent instanceof LeanStatements) break;
                    self = parent;
                }
                if (parent) {
                    const last = this.args.pop();
                    const index = parent.args.indexOf(self);
                    parent.args.splice(index + 1, 0, last);
                    last.parent = parent;
                    last.indent = parent.indent;
                    parent.relocate_last_comment();
                    break;
                }
            } else {
                if (end.is_comment()) {
                    let lemma = null;
                    let j = 0;
                    for (j = index - 1; j >= 0; --j) {
                        const stmt = this.args[j];
                        if (stmt instanceof Lean_lemma) {
                            lemma = stmt;
                            break;
                        }
                        if (stmt.is_comment()) continue;
                        break;
                    }
                    if (lemma) {
                        const assignment = lemma.assignment;
                        if (assignment instanceof LeanAssign) {
                            let proof = assignment.rhs;
                            if (proof instanceof LeanBy || proof instanceof LeanCalc) {
                                proof = proof.arg;
                                if (proof instanceof LeanStatements) {
                                    for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                    this.args.splice(j + 1, index - j);
                                    break;
                                }
                            } else if (proof instanceof LeanArgsNewLineSeparated) {
                                for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                this.args.splice(j + 1, index - j);
                                break;
                            }
                        }
                    }
                }
                end.relocate_last_comment();
                break;
            }
        }
    }

    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        let format = Array(n).fill('%s').join('\n');
        if (this.parent instanceof LeanBrace) {
            format = `\n${format}\n${' '.repeat(this.parent.indent)}`;
        }
        return format;
    }

    swap_echo_star(syntax, statements) {
        const args = this.args;
        for (let i = 0; i < args.length; ++i) {
            const echo = args[i];
            if (
                echo instanceof LeanTactic &&
                echo.tacticName === 'echo' &&
                echo.arg instanceof LeanToken &&
                echo.arg.text === '*'
            ) {
                [args[i], args[i + 1]] = [args[i + 1], args[i]];
                i++;
            }
        }
        for (const stmt of this.args) statements.push(...stmt.split(syntax));
    }

    /** Port of LeanStatements::push_line_comment. Stops bubbling to root. */
    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }
}

/**
 * Echo-style `:= by` proofs: `LeanTactic` may indent continuation lines (nested tactics under
 * `intro`); `LeanModule` then applies `indentText(proofInd)` to the whole string, doubling those
 * spaces and changing how the next parse groups tactics. Remove the common leading whitespace
 * from lines after the first so outer indent is applied once.
 * @param {string} s
 */
function dedentEchoProofTacticLines(s) {
    const lines = s.split('\n');
    if (lines.length < 2) return s;
    let minLead = Infinity;
    for (let i = 1; i < lines.length; i++) {
        const line = lines[i];
        if (line === '') continue;
        const lead = /^ */.exec(line);
        if (lead) minLead = Math.min(minLead, lead[0].length);
    }
    if (!Number.isFinite(minLead) || minLead === 0) return s;
    const out = [lines[0]];
    for (let i = 1; i < lines.length; i++) {
        const line = lines[i];
        if (line === '') out.push(line);
        else out.push(line.slice(minLead));
    }
    return out.join('\n');
}

function dedentEchoProofTermBlock(s) {
    const lines = s.split('\n');
    let minLead = Infinity;
    for (const line of lines) {
        if (line === '') continue;
        const lead = /^ */.exec(line);
        if (lead) minLead = Math.min(minLead, lead[0].length);
    }
    if (!Number.isFinite(minLead) || minLead === 0) return s;
    return lines.map((line) => (line === '' ? line : line.slice(minLead))).join('\n');
}

/**
 * Scan module args after `LeanAssign`/`Lean_def` with empty rhs caret: optional carets, line comments,
 * then `LeanTactic`, space-separated term, a single `LeanToken`, or `Lean_fun` proof. Used for echo `:= by` serialization.
 * @param {Lean[]} moduleArgs
 * @param {number} startJ
 * @param {(s: string, indent: number) => string} indentText
 * @returns {{ cmts: Lean[], proofStr: string, endJ: number, proofIsTactic: boolean } | null}
 */
function consumeEchoAssignProofTail(moduleArgs, startJ, indentText) {
    let j = startJ;
    while (j < moduleArgs.length && moduleArgs[j] instanceof LeanCaret) j++;
    const cmts = [];
    while (j < moduleArgs.length && moduleArgs[j].is_comment()) {
        cmts.push(moduleArgs[j]);
        j++;
    }
    const proof = j < moduleArgs.length ? moduleArgs[j] : null;
    const proofOk =
        proof &&
        (proof instanceof LeanTactic ||
            proof instanceof LeanArgsSpaceSeparated ||
            proof instanceof LeanToken ||
            proof instanceof Lean_fun ||
            proof instanceof LeanAngleBracket);
    if (!proofOk) return null;
    let endJ = j;
    let proofStr = String(proof);
    let proofInd = proof.indent ?? 0;
    for (const c of cmts) proofInd = Math.max(proofInd, c.indent ?? 0);
    const proofIsTactic = proof instanceof LeanTactic;
    if (proofIsTactic) {
        const tacticProofRaw = dedentEchoProofTacticLines(String(proof));
        let danglingStc = false;
        for (let k = 0; k < proof.args.length; k++) {
            const x = proof.args[k];
            if (x instanceof LeanSequentialTacticCombinator && x.arg instanceof LeanCaret) {
                danglingStc = true;
                break;
            }
        }
        if (danglingStc && endJ + 1 < moduleArgs.length && moduleArgs[endJ + 1] instanceof LeanTacticBlock) {
            endJ++;
            const ps = indentText(tacticProofRaw, proofInd);
            const tb = String(moduleArgs[endJ]);
            const join = ps.endsWith('\n') ? '' : '\n';
            proofStr = `${ps}${join}${tb}`;
        } else {
            proofStr = indentText(tacticProofRaw, proofInd);
        }
    } else {
        proofStr = indentText(dedentEchoProofTermBlock(String(proof)), proofInd);
    }
    return { cmts, proofStr, endJ, proofIsTactic };
}

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function strStmt(node) {
    return String(node).replace(/\n$/, '');
}

/** Normalize import path: trim, collapse space-around-dot to dot, then spaces to dots to match PHP. */
function normalizeImportStr(s) {
    return s.trim().replace(/\s*\.\s*/g, '.').replace(/\s+/g, '.');
}

/** Normalize type string: collapse spaces, fix bracket interior spacing to match Lean source e.g. [n, n]. */
function normalizeTypeStr(s) {
    return s
        .trim()
        .replace(/\s+/g, ' ')
        .replace(/\[\s+/g, '[')
        .replace(/\s+\]/g, ']');
}

/** PHP `preg_replace("/^  /m", "", …)` */
function unindentTwo(s) {
    return s.replace(/^  /gm, '');
}

/** Normalize instImplicit to match PHP: "[NeZero (l : ℕ)]" not "[ NeZero ( l  ℕ)]". */
function normalizeInstImplicit(s) {
    if (!s || !s.trim()) return s;
    return s
        .split('\n')
        .map((line) =>
            line
                .trim()
                .replace(/\s{2,}/g, ' ')
                .replace(/\[\s+/g, '[')
                .replace(/\s+\]/g, ']')
                .replace(/\(\s+/g, '(')
                .replace(/\s+\)/g, ')'),
        )
        .join('\n');
}

/**
 * Extract attribute names from LeanAttribute (e.g. @[main] → ['main'], @[main, fin] → ['main','fin']).
 * Handles LeanBracket contents as LeanArgsCommaSeparated, LeanArgsSpaceSeparated, or LeanToken.
 */
function extractAttribute(attr) {
    if (!attr) return null;
    let a = attr.arg;
    if (a instanceof LeanArgsSpaceSeparated) {
        const bracket = a.args.find((x) => x instanceof LeanBracket);
        a = bracket || null;
    }
    if (!a || !(a instanceof LeanBracket)) return null;
    a = a.arg;
    if (a instanceof LeanArgsCommaSeparated || a instanceof LeanArgsSpaceSeparated)
        return a.args.map((x) => strStmt(x)).filter(Boolean);
    if (a instanceof LeanToken) return [strStmt(a)];
    return null;
}

/**
 * `(hS : StochasticIrreducible P)` / `(h₁ : Measurable Y)` — a hypothesis-named binder whose
 * type is a predicate application (capitalized head, not a known type former). `isProp` cannot
 * see the declaration of such predicates, so the naming convention decides.
 * @param {Lean} name
 * @param {Lean} type
 */
function looksLikeClassHypothesis(name, type) {
    if (!(name instanceof LeanToken)) return false;
    let head = type instanceof LeanArgsSpaceSeparated ? type.args[0] : type;
    if (head instanceof LeanProperty && head.rhs instanceof LeanToken) head = head.rhs;
    if (!(head instanceof LeanToken) || !/^[A-Z]/.test(head.text)) return false;
    // Well-known Prop-valued predicates: a hypothesis whatever the binder is called
    // (`(mono : Monotone t)`, `(f_mono : Monotone f)`).
    if (/^(Monotone|Antitone|StrictMono|StrictAnti|MonotoneOn|AntitoneOn|StrictMonoOn|StrictAntiOn|Summable|HasSum|Continuous|ContinuousOn|ContinuousAt|Differentiable|DifferentiableOn|DifferentiableAt|HasDerivAt|Integrable|IntegrableOn|Measurable|AEMeasurable|StronglyMeasurable|AEStronglyMeasurable|Injective|Surjective|Bijective|Tendsto|Nonempty|Convex|ConvexOn|ConcaveOn|IsCompact|IsOpen|IsClosed|Pairwise|Irreducible|Prime|Even|Odd|Squarefree|Coprime|IsUnit)$/.test(head.text))
        return true;
    // Otherwise rely on the naming convention: `h`, `h₁`, `hf`, `hmono`, `hμ`, …
    if (!/^h/u.test(name.text)) return false;
    return !/^(Type|Sort|Prop|Fin|Set|Finset|Multiset|List|Array|Vector|Matrix|Tensor|Measure|MeasurableSpace|Option|Nat|Int|Real|Complex|Bool|String|Prod|Sum|Sigma|Subtype|Filter|EuclideanSpace|PMF|ProbabilityMeasure|FiniteMeasure)$/.test(head.text);
}

/**
 * `(f : S → α)`: a function-valued data argument (codomain is a type), not a hypothesis.
 * `Lean_rightarrow.isProp` defaults undeclared tokens to `Prop`, which misfiles such binders
 * as givens while `(n : ℕ)` stays explicit.
 * @param {Lean} type
 * @param {Record<string, unknown>} vars
 * @param {Set<string>} typeVars
 */
function looksLikeDataArrow(type, vars, typeVars) {
    if (!(type instanceof Lean_rightarrow)) return false;
    let cod = type;
    while (cod instanceof Lean_rightarrow) cod = cod.rhs;
    if (!(cod instanceof LeanToken)) return false;
    const t = cod.text;
    if (vars[t] === 'Prop') return false;
    return typeVars.has(t) ||
        /^(ℕ|ℤ|ℚ|ℝ|ℂ|Bool|Prop|Type|Nat|Int|Rat|Real|Complex|ENNReal|NNReal|EReal|ℝ≥0|ℝ≥0∞)$/u.test(t);
}

/**
 * PHP `escape_specials` (php/parser/lean.php ~9331–9341).
 * @param {string} token
 */
function escapeSpecials(token) {
    return token.replace(/^(_*)([^\W_]\w*?)_(.+)/, (_m, lead, head, tail) => {
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        const escLead = lead.replace(/_/g, '\\_');
        return !lead && head.length === 1 ? `${head}_{${escTail}}` : `${escLead}${head}\\_${escTail}`;
    });
}

/**
 * PHP `latex_tag` (php/parser/lean.php ~9344–9352).
 * @param {string} tag
 */
function latexTag(tag) {
    return tag
        .split('.')
        .map((t) => escapeSpecials(t))
        .join('.');
}

/**
 * PHP `std\setitem` via path segments (last segment is the value).
 * @param {Record<string, unknown>} data
 * @param {string[]} segs
 */
function setItemFromPath(data, segs) {
    if (segs.length === 1) {
        data[segs[0]] = segs[0];
        return;
    }
    const value = segs[segs.length - 1];
    const keys = segs.slice(0, -1);
    /** @type {Record<string, unknown>} */
    let cur = data;
    for (let i = 0; i < keys.length; i++) {
        const k = keys[i];
        if (i === keys.length - 1) {
            cur[k] = value;
            return;
        }
        if (cur[k] == null || typeof cur[k] !== 'object') cur[k] = {};
        cur = /** @type {Record<string, unknown>} */ (cur[k]);
    }
}

/**
 * PHP `LeanModule::array_push` (php/parser/lean.php ~4867–4877).
 * @param {unknown[][]} vars
 * @param {import('../../../static/js/parser/lean.js').Lean} lhs
 * @param {import('../../../static/js/parser/lean.js').Lean} rhs
 */
function arrayPushVars(vars, lhs, rhs) {
    if (lhs instanceof LeanToken) {
        /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
        let args = [lhs, rhs];
        while (args.length && args[args.length - 1] instanceof Lean_rightarrow) {
            const end = args[args.length - 1];
            args.splice(args.length - 1, 1, end.lhs, end.rhs);
        }
        vars.push(args);
    } else if (lhs instanceof LeanArgsSpaceSeparated) {
        for (const sub of lhs.args) arrayPushVars(vars, sub, rhs);
    }
}

/**
 * @param {unknown[]} implicit
 */
function parseVars(implicit) {
    const vars = [];
    // `{S : Type*} [Fintype S]` on one line arrives as a single space-separated node
    const flat = [];
    for (const b of implicit) {
        if (b instanceof LeanArgsSpaceSeparated) flat.push(...b.args);
        else flat.push(b);
    }
    for (const brace of flat) {
        if (brace instanceof LeanBrace) {
            const colon = brace.arg;
            if (colon instanceof LeanColon) arrayPushVars(vars, colon.lhs, colon.rhs);
        }
    }
    /** @type {Record<string, unknown>} */
    const kwargs = {};
    for (const v of vars) {
        const segs = v.map((a) => strStmt(a));
        setItemFromPath(kwargs, segs);
    }
    return kwargs;
}

function collectRandomVarNames(binderRoots) {
    const nodes = [];
    const gather = (n) => {
        if (!n || typeof n !== 'object') return;
        nodes.push(n);
        if (Array.isArray(n.args)) for (const k of n.args) gather(k);
    };
    for (const r of binderRoots) gather(r);

    /** @type {Map<string, string>} measure name -> domain text */
    const measures = new Map();
    for (const n of nodes) {
        if (!(n instanceof LeanBrace)) continue;
        const cols = [];
        const a = n.arg;
        if (a instanceof LeanColon) cols.push(a);
        else if (a instanceof LeanArgsSpaceSeparated)
            for (const c of a.args) if (c instanceof LeanColon) cols.push(c);
        for (const col of cols) {
            const rhs = col.rhs.peelGroup();
            if (rhs.headIs('Measure') && rhs instanceof LeanArgsSpaceSeparated
                && rhs.args.length >= 2) {
                const dom = strStmt(rhs.args[1].peelGroup()).trim();
                if (dom) measures.set(strStmt(col.lhs).trim(), dom);
            }
        }
    }
    const probMeasureApp = (n0) => {
        const a = n0?.peelGroup?.() ?? n0;
        if (!(a instanceof LeanArgsSpaceSeparated) || a.args.length < 2) return null;
        if (!a.headIs('IsProbabilityMeasure') && !a.headIs('PSpace')) return null;
        return a.args[1];
    };

    const probDomains = new Set();
    const addProbMeasure = (measureName) => {
        if (measureName == null) return;
        const m = strStmt(measureName.peelGroup()).trim();
        if (measures.has(m)) probDomains.add(measures.get(m));
    };
    for (const n of nodes) {
        if (n instanceof LeanBracket) {
            addProbMeasure(probMeasureApp(n.arg));
        } else if (n instanceof LeanParenthesis && n.arg instanceof LeanColon) {
            addProbMeasure(probMeasureApp(n.arg.rhs));
        }
    }

    /** @type {Set<string>} */
    const rvs = new Set();
    for (const n of nodes) {
        if (!(n instanceof LeanParenthesis) && !(n instanceof LeanBrace)) continue;
        const cols = [];
        const a = n.arg;
        if (a instanceof LeanColon) cols.push(a);
        else if (a instanceof LeanArgsSpaceSeparated)
            for (const c of a.args) if (c instanceof LeanColon) cols.push(c);
        for (const col of cols) {
            const ty = col.rhs.peelGroup();
            if (!(ty instanceof Lean_rightarrow)) continue;
            const dom = strStmt(ty.lhs.peelGroup()).trim();
            if (!probDomains.has(dom)) continue;
            const addNames = (x) => {
                const y = x.peelGroup();
                if (y instanceof LeanToken) rvs.add(y.text);
                else if (y instanceof LeanArgsSpaceSeparated) y.args.forEach(addNames);
            };
            addNames(col.lhs);
        }
    }
    return rvs;
}

/**
 * Mark a sequence of statements in order: a top-level `let q := …` hides `q`
 * for every following statement (the shared `letBound` frame accumulates).
 * @param {unknown[]} stmts
 * @param {Set<string>} rvNames
 */
function markRandomVarSequence(stmts, rvNames) {
    const letBound = [];
    for (const st of stmts) st.markRandomVarNames(rvNames, letBound);
}

function zipped(a, b) {
    const n = Math.min(a.length, b.length);
    /** @type {[T, U][]} */
    const out = [];
    for (let i = 0; i < n; ++i) out.push([a[i], b[i]]);
    return out;
}

function buildLetBindings(implyStmts) {
    const bindings = {};
    if (!implyStmts.length) return bindings;
    for (const stmt of implyStmts) {
        if (!(stmt instanceof Lean_let)) continue;
        const arg = stmt.arg;
        if (!arg) continue;
        let nameNode = null;
        let rhsNode = null;
        if (arg instanceof LeanAssign) {
            if (arg.lhs instanceof LeanColon) {
                nameNode = arg.lhs.lhs;
                rhsNode = arg.rhs;
            } else {
                nameNode = arg.lhs;
                rhsNode = arg.rhs;
            }
        } else if (arg instanceof LeanColon && arg.rhs instanceof LeanAssign) {
            nameNode = arg.rhs.lhs;
            rhsNode = arg.rhs.rhs;
        }
        if (nameNode && rhsNode) {
            const name = strStmt(nameNode).trim();
            if (name) bindings[name] = rhsNode;
        }
    }
    return bindings;
}

function leanModuleMergeProof(proof, echo, syntax = {}) {
    let list = proof.args;
    if (list[0] instanceof LeanLineComment && list[0].text === 'proof') list = list.slice(1);
    list = list.filter((s) => !(s instanceof LeanCaret));

    const statements = [];
    for (const s of list) statements.push(...s.split(syntax));

    const code = [];
    let last = [];
    // Separator inserted BEFORE each statement in `last` (' ' for the rhs of a
    // same-line `<;>` chain, '\n' otherwise).
    let seps = [];
    let nextSep = '\n';
    // Goal LaTeX captured by an inline `<;> echo ⊢` marker for the open step.
    let inlineLatex;

    const echoLatex = (echoNode) => {
        const {line} = echoNode;
        return Number.isInteger(line) ? null : line == null ? null : line;
    };
    // A same-line `<;> echo ⊢` combinator (newlineBehind === false) is a goal
    // snapshot INSIDE one source line, e.g. `split_ifs <;> echo ⊢ <;> first | …`:
    // it must not become its own step nor print its marker text. The surrounding
    // chain is glued onto one step and the snapshot is attached as its LaTeX.
    const isInlineEchoMark = (stmt, echoNode) =>
        !!echoNode
        && stmt instanceof LeanSequentialTacticCombinator
        && stmt.newlineBehind === false;

    if (echo) {
        for (const stmt of statements) {
            const echoNode = stmt.getEcho();
            if (isInlineEchoMark(stmt, echoNode)) {
                if (inlineLatex === undefined || inlineLatex === null)
                    inlineLatex = echoLatex(echoNode);
                nextSep = ' ';
            } else if (echoNode) {
                code.push([last, inlineLatex !== undefined ? inlineLatex : echoLatex(echoNode), seps]);
                last = [];
                seps = [];
                nextSep = '\n';
                inlineLatex = undefined;
            } else {
                seps.push(nextSep);
                last.push(stmt);
                nextSep = '\n';
            }
        }
    } else {
        for (const stmt of statements) {
            if (stmt instanceof Lean_let || stmt instanceof LeanTactic) {
                last.push(stmt);
                code.push([last, null, seps]);
                last = [];
            } else last.push(stmt);
        }
    }
    if (last.length) {
        let finalLatex = inlineLatex !== undefined ? inlineLatex : null;
        if (finalLatex === null && last[0] instanceof LeanCalc && last[0].originalCalc)
            finalLatex = last[0].originalCalc.toLatex(syntax);
        code.push([last, finalLatex, seps]);
    }

    return code.map(([stmts, latex, ss]) => {
        let text = '';
        stmts.forEach((st, i) => {
            text += (i === 0 ? '' : (ss && ss[i] ? ss[i] : '\n')) + strStmt(st);
        });
        return {lean: unindentTwo(text), latex};
    });
}

function leanModuleRender2vue(mod, echo, modify = null, syntax = {}) {
    if (!echo) mod.relocate_last_comment();
    const $import = [];
    const open = [];
    const set_option = [];
    const preamble = [];
    const lemma = [];
    const date = {};
    const error = [];
    let comment = null;

    const args = mod.args;
    for (let idx = 0; idx < args.length; idx++) {
        const stmt = args[idx];
        if (stmt instanceof Lean_import)
            $import.push(normalizeImportStr(strStmt(stmt.arg)));
        else if (stmt instanceof Lean_lemma) {
            let assignment = stmt.assignment instanceof LeanAssign ? stmt.assignment : null;

            let assignIdx = -1;
            if (!assignment) {
                let proofStart = args.length;
                for (let k = idx + 1; k < args.length; k++) {
                    const x = args[k];
                    if (x instanceof LeanLineComment && x.text === 'proof') {
                        proofStart = k;
                        break;
                    }
                    if (x instanceof LeanTactic) {
                        proofStart = k;
                        break;
                    }
                }
                for (let j = idx + 1; j < proofStart; j++) {
                    const cand = args[j];
                    if (cand instanceof LeanAssign) {
                        const lhs = cand.lhs;
                        if (lhs instanceof Lean_let) continue;
                        assignment = cand;
                        assignIdx = j;
                    }
                }
                if (!assignment) {
                    for (let j = idx + 1; j < args.length; j++) {
                        const cand = args[j];
                        if (cand instanceof LeanAssign) {
                            assignment = cand;
                            assignIdx = j;
                            break;
                        }
                    }
                }
            }
            if (assignment instanceof LeanAssign) {
                const accessibility = stmt.accessibility;
                let innerAssign = assignment;
                while (innerAssign.lhs instanceof LeanAssign) innerAssign = innerAssign.lhs;
                let declspec = innerAssign.lhs;
                while (declspec instanceof LeanAssign) declspec = declspec.lhs;
                let flatInstImplicit = [];
                let flatExplicit = '';
                let flatGiven = null;

                let flatImplyStmts = [];
                let flatRvNames = new Set();
                if (assignIdx >= 0) {
                    let firstAssign = assignIdx;
                    for (let k = idx + 1; k < assignIdx; k++) {
                        if (args[k] instanceof LeanAssign) {
                            firstAssign = k;
                            break;
                        }
                    }
                    // semantic pass: random-variable names + free-occurrence
                    // marking, before any given/imply latex is generated
                    const flatBinderNodes = args.slice(idx + 1, firstAssign);
                    flatRvNames = collectRandomVarNames(flatBinderNodes);
                    for (const s of flatBinderNodes) s.markRandomVarNames(flatRvNames);
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (s instanceof Lean_let) {
                            flatImplyStmts.push(s);
                        }
                    }
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (s instanceof LeanBracket) {
                            flatInstImplicit.push(strStmt(s));
                            continue;
                        }
                        const collectParenColons = (/** @type {*} */ n) => {
                            if (!n) return;
                            if (n instanceof LeanParenthesis && n.arg instanceof LeanColon) {
                                const col = n.arg;
                                if (col.lhs && col.rhs) {
                                    if (flatGiven === null) flatGiven = [];
                                    flatGiven.push({
                                        lean: `(${strStmt(col.lhs).trim()} : ${normalizeTypeStr(strStmt(col.rhs))})`,
                                        latex: col.toLatex ? col.toLatex(syntax) : null,
                                    });
                                }
                                return;
                            }
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            for (const child of a) collectParenColons(child);
                        };
                        if (s instanceof LeanParenthesis && s.arg instanceof LeanColon) {
                            collectParenColons(s);
                            continue;
                        }
                        if (s instanceof LeanArgsSpaceSeparated || s instanceof LeanArgsNewLineSeparated) {
                            collectParenColons(s);
                            continue;
                        }
                        if (s instanceof LeanColon && s.lhs) {
                            const lb = s.lhs;
                            if (lb instanceof LeanBracket) {
                                const inner = lb.arg;
                                const lhsStr = inner ? strStmt(inner).trim() : strStmt(lb).trim();
                                const rhsStr = s.rhs ? strStmt(s.rhs).trim() : '';
                                const parts = lhsStr.split(/\s+/).filter(Boolean);
                                const varPart = parts.length > 1 ? parts[parts.length - 1] : parts[0] || '';
                                const headPart = parts.length > 1 ? parts.slice(0, -1).join(' ') : lhsStr;
                                const repr =
                                    rhsStr && varPart
                                        ? `[${headPart} (${varPart} : ${rhsStr})]`
                                        : `[${lhsStr}${rhsStr ? ` : ${rhsStr}` : ''}]`;
                                flatInstImplicit.push(repr);
                            } else if (lb instanceof LeanParenthesis || (lb instanceof LeanColon && lb.rhs)) {
                                if (s.rhs instanceof LeanStatements || s.rhs instanceof LeanArgsNewLineSeparated) {
                                    const inner = lb;
                                    if (inner instanceof LeanColon && inner.lhs && inner.rhs) {
                                        const innerLhs = inner.lhs;
                                        if (innerLhs instanceof LeanParenthesis && inner.rhs) {
                                            if (flatGiven === null) flatGiven = [];
                                            const varPart = strStmt(
                                                innerLhs.arg
                                            ).trim();
                                            const typePart = normalizeTypeStr(strStmt(inner.rhs));
                                            flatGiven.push({
                                                lean: `(${varPart} : ${typePart})`,
                                                latex: inner.toLatex ? inner.toLatex(syntax) : null,
                                            });
                                        }
                                    }
                                } else {
                                    if (flatGiven === null) flatGiven = [];
                                    let leanStr;
                                    if (lb instanceof LeanParenthesis && s.rhs) {
                                        const varPart = strStmt(lb.arg).trim();
                                        const typePart = normalizeTypeStr(strStmt(s.rhs));
                                        leanStr = `(${varPart} : ${typePart})`;
                                    } else {
                                        leanStr = strStmt(s).trim();
                                        if (lb instanceof LeanParenthesis && !leanStr.startsWith('('))
                                            leanStr = '(' + leanStr;
                                    }
                                    if (leanStr.includes('-- imply'))
                                        leanStr = leanStr.replace(/\s*--\s*imply.*$/, '').trim();
                                    flatGiven.push({ lean: leanStr, latex: s.toLatex ? s.toLatex(syntax) : null });
                                }
                            }
                        }
                    }
                    if (flatGiven && flatGiven.length > 0) {
                        const lines = flatGiven.map((g) => g.lean);
                        lines[lines.length - 1] += ' :';
                        flatExplicit = lines.join('\n');
                        flatGiven = null;
                    }
                }
                let useSimpleDeclspec = false;
                if (declspec instanceof LeanColon) {
                    const rhsColon = declspec.rhs;
                    const rhsArgs = rhsColon.args?? null;
                    const isImplyList =
                        rhsArgs &&
                        Array.isArray(rhsArgs) &&
                        rhsArgs.length > 0 &&
                        (rhsArgs[0] instanceof LeanLineComment ||
                            rhsArgs[0] instanceof Lean_let ||
                            rhsColon instanceof LeanArgsSpaceSeparated ||
                            rhsColon instanceof LeanStatements ||
                            rhsColon instanceof LeanArgsNewLineSeparated);
                    if (!rhsColon || !rhsArgs || !isImplyList) {
                        if (
                            assignment.lhs &&
                            (typeof assignment.lhs.toLatex === 'function' || flatImplyStmts.length > 0)
                        ) {
                            useSimpleDeclspec = true;
                        } else {
                            error.push({
                                code: strStmt(declspec),
                                line: 0,
                                info: 'lemma colon rhs must have args (LeanArgsSpaceSeparated)',
                                type: 'linter',
                            });
                            continue;
                        }
                    }
                }
                if (declspec instanceof LeanColon && !useSimpleDeclspec) {
                    const rhsColon = declspec.rhs;
                    let attribute = extractAttribute(stmt.attribute);
                    let imply =  rhsColon.args.slice()
                    if (imply[0] instanceof LeanLineComment && imply[0].text === 'imply') imply.shift();
                    // semantic pass: random variables are explicit binders on a
                    // probability-space domain; mark their free occurrences in
                    // the signature propositions and the imply statements
                    const rvNames = collectRandomVarNames([declspec.lhs]);
                    // Always run: `.map` argument detection marks random
                    // variables even when no PSpace hypothesis is present.
                    declspec.lhs.markRandomVarNames(rvNames);
                    markRandomVarSequence(imply, rvNames);
                    const proof0 = innerAssign.rhs;
                    const by = proof0 instanceof LeanBy? 'by' : proof0 instanceof LeanCalc ? 'calc' : '';
                    const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                    let implyLatex;
                    if (imply.length > 1 && imply[0] instanceof Lean_let)
                        implyLatex = implyLetAlignLatex(imply, syntax);
                    else
                        implyLatex = imply.map(st => implyConclusionLatex(st, syntax)).join('\n');
                    const assignSuffix = ' :=' + (by ? ` ${by}` : '');

                    const implyOut = { lean: implyLean + assignSuffix, latex: implyLatex };
                    declspec = declspec.lhs;
                    let collectedExplicit = null;
                    let name;
                    if (declspec instanceof LeanToken || declspec instanceof LeanProperty) {
                        name = declspec;
                        declspec = [];
                    } else if (
                        declspec &&
                        declspec.args &&
                        declspec.args.length >= 2 &&
                        !(declspec.args[0] && declspec.args[0] instanceof LeanParenthesis)
                    ) {
                        const dargs = declspec.args;
                        name = dargs[0];
                        const binders = dargs[1] && dargs[1].args ? dargs[1].args : (dargs.length > 2 ? dargs.slice(1) : []);
                        declspec = binders;
                    } else if (declspec && (declspec.lhs != null || declspec.args)) {
                        const collectParens = n => {
                            if (!n) return [];
                            if (n instanceof LeanParenthesis) return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(declspec);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = p.arg;
                                if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) lines[lines.length - 1] += ' :';
                            collectedExplicit = lines;
                        }
                        name = stmt.assignment;
                        declspec = [];
                    } else {
                        name = stmt.assignment;
                        declspec = [];
                    }
                    const instImplicit = [];
                    const implicit = [];
                    let explicit = [];
                    let given = null;
                    let default_ = [];
                    const decidables = [];
                    const typeVars = new Set();
                    const declList = declspec;
                    for (let i = 0; i < declList.length; ++i) {
                        const st = declList[i];
                        if (st instanceof LeanBracket) {
                            instImplicit.push(strStmt(st));
                            const ia = st.arg;
                            if (ia instanceof LeanArgsSpaceSeparated && ia.args.length === 2) {
                                const [l, r] = ia.args;
                                if (l instanceof LeanToken && l.text === 'Decidable' && r instanceof LeanToken)
                                    decidables.push(strStmt(r));
                            }
                            // `[Fintype S]`, `[NormedAddCommGroup α]`: class arguments are types
                            if (ia instanceof LeanArgsSpaceSeparated && ia.args[0] instanceof LeanToken && ia.args[0].text !== 'Decidable') {
                                for (const a of ia.args.slice(1))
                                    if (a instanceof LeanToken) typeVars.add(a.text);
                            }
                        } else if (st instanceof LeanBrace) {
                            st.toLatex(syntax);
                            implicit.push(st);
                        } else if (st instanceof LeanArgsSpaceSeparated) {
                            if (st.args.some((a) => a instanceof LeanParenthesis)) {
                                declList.splice(i, 1, ...st.args);
                                --i;
                            } else if (st.args[0] instanceof LeanBracket) {
                                instImplicit.push(strStmt(st));
                                for (const b of st.args) {
                                    const ia = b instanceof LeanBracket ? b.arg : null;
                                    if (ia instanceof LeanArgsSpaceSeparated && ia.args[0] instanceof LeanToken && ia.args[0].text !== 'Decidable') {
                                        for (const a of ia.args.slice(1))
                                            if (a instanceof LeanToken) typeVars.add(a.text);
                                    }
                                }
                            }
                            else if (st.args[0] instanceof LeanBrace) implicit.push(st);
                            else
                                error.push({
                                    code: strStmt(st),
                                    line: 0,
                                    info: `lemma ${strStmt(name)} is not well-defined`,
                                    type: 'linter',
                                });
                        } else if (st instanceof LeanLineComment) {
                            if (st.text === 'given') {
                                given = i + 1;
                                break;
                            }
                            if (implicit.length) implicit.push(strStmt(st));
                            else instImplicit.push(strStmt(st));
                        } else if (st instanceof LeanParenthesis) {
                            const inner = st.arg;
                            if (inner instanceof LeanColon) {
                                declList.splice(
                                    i,
                                    0,
                                    new LeanLineComment('given', st.indent, st.parent),
                                );
                                if (modify) modify.value = true;
                                ++i;
                            }
                            given = i;
                            break;
                        }
                    }
                    let givenOut = null;
                    if (given !== null) {
                        let givenSlice = declList.slice(given);
                        const latex = [];
                        let givenStart = null;
                        let givenStop = null;
                        let vars = null;
                        for (var i = 0; i < givenSlice.length; i++) {
                            const st = givenSlice[i];
                            if (st instanceof LeanParenthesis) {
                                const colon = st.arg;
                                if (colon instanceof LeanColon) {
                                    const prop = colon.rhs;
                                    if (vars == null) {
                                        vars = parseVars(implicit);
                                        for (const p of decidables) vars[p] = 'Prop';
                                        for (const v of Object.values(vars))
                                            if (typeof v === 'string' && /^[^\s()]+$/u.test(v) && v !== 'Prop') typeVars.add(v);
                                    }
                                    // Only before the first hypothesis: a data arrow in the middle
                                    // would end the given run and push later hypotheses to `default`.
                                    const isData = givenStart === null && looksLikeDataArrow(prop, vars, typeVars);
                                    if ((prop.isProp(vars) && !isData) || looksLikeClassHypothesis(colon.lhs, prop)) {
                                        latex.push([prop.toLatex(syntax), latexTag(strStmt(colon.lhs))]);
                                        if (givenStart === null) givenStart = i;
                                    } else if (givenStart !== null) {
                                        givenStop = i;
                                        break;
                                    }
                                } else if (colon instanceof LeanAssign) {
                                    break;
                                }
                            } else if (st.is_comment()) {
                                // Comments before the first hypothesis stay with `explicit`;
                                // a slot here would shift every given's LaTeX by one.
                                if (givenStart !== null) latex.push(null);
                            } else if (st instanceof LeanBrace) {
                                const pivot = i;
                                const par = new LeanParenthesis(st.arg, st.indent, st.parent);
                                par.is_closed = true;
                                givenSlice[pivot] = par;
                                break;
                            } else if (st instanceof LeanCaret) {
                                // skip
                            } else if (st instanceof LeanArgsSpaceSeparated) {
                                givenSlice.splice(i, 1, ...st.args);
                                --i;
                            } else {
                                error.push({
                                    code: strStmt(st),
                                    line: 0,
                                    info: 'given statement must be of LeanParenthesis Type',
                                    type: 'linter',
                                });
                            }
                        }
                        givenSlice = givenSlice.map((s) => unindentTwo(strStmt(s)));
                        if (givenStart !== null) {
                            if (givenStop != null) {
                                explicit = givenSlice.slice(0, givenStart);
                                default_ = givenSlice.slice(givenStop);
                                if (default_.length)
                                    default_[default_.length - 1] += ' :';
                                givenSlice = givenSlice.slice(givenStart, givenStop);
                            } else {
                                explicit = givenSlice.slice(0, givenStart);
                                givenSlice = givenSlice.slice(givenStart);

                                if (givenSlice.length)
                                    givenSlice[givenSlice.length - 1] += ' :';
                            }
                        } else {
                            explicit = givenSlice;
                            if (explicit.length) explicit[explicit.length - 1] += ' :';
                            givenSlice = [];
                        }

                        if (givenSlice.length) {
                            if (givenSlice.length > latex.length) givenSlice = givenSlice.filter(Boolean);
                            const tagged = latex.map((pair) =>
                                pair
                                    ? `${pair[0]}\\tag*{\$${pair[1]}\$}`
                                    : null,
                            );
                            givenOut = zipped(givenSlice, tagged).map(([g, lx]) => {
                                const o = { lean: g };
                                if (lx) o.latex = lx;
                                else o.insert = true;
                                return o;
                            });
                        }
                    }

                    const proof = innerAssign.rhs;
                    let proofOut;
                    let proofNode = proof;
                    if (
                        assignIdx >= 0 &&
                        !(proof instanceof LeanBy || proof instanceof LeanCalc) &&
                        (proof instanceof LeanCaret || !(proof.args && proof.args.length))
                    ) {
                        let end = assignIdx + 1;
                        for (; end < args.length; ++end) {
                            const x = args[end];
                            if (x instanceof LeanLineComment && /^(created|updated)\s/i.test(String(x.text || '')))
                                break;
                        }
                        proofNode = { args: args.slice(assignIdx + 1, end) };
                    }
                    syntax.letBindings = buildLetBindings(imply.length ? imply : flatImplyStmts);
                    if (by) {
                        proofOut = { [by]: leanModuleMergeProof(proofNode.arg ?? proofNode, echo, syntax) };
                    } else {
                        proofOut = leanModuleMergeProof(proofNode, echo, syntax);
                    }

                    const implicitStr = unindentTwo(
                        implicit.map((x) => (typeof x === 'string' ? x : strStmt(x))).join('\n'),
                    );

                    lemma.push({
                        comment,
                        accessibility: String(accessibility),
                        attribute,
                        name: strStmt(name).trim(),
                        instImplicit: normalizeInstImplicit(
                            unindentTwo(
                                instImplicit.length ? instImplicit.join('\n') : flatInstImplicit.join('\n'),
                            ),
                        ),
                        implicit: implicitStr,
                        explicit: collectedExplicit ? collectedExplicit.join('\n') : (explicit.length ? explicit.join('\n') : flatExplicit),
                        given: givenOut ?? flatGiven,
                        default: default_.join('\n'),
                        imply: implyOut,
                        proof: proofOut,
                    });
                    comment = null;
                } else if (declspec && (typeof declspec.toLatex === 'function' || flatImplyStmts.length > 0)) {
                    const proof0 = innerAssign.rhs;
                    const by = proof0 instanceof LeanBy? 'by' : proof0 instanceof LeanCalc? 'calc': '';

                    let simpleExplicit = flatExplicit;
                    let simpleName = null;
                    let implyNode = declspec;
                    if (declspec instanceof LeanColon && declspec.lhs && !flatExplicit) {
                        const inner = declspec.lhs;

                        if (inner.lhs instanceof LeanColon) {
                            const binderNode = inner.lhs.lhs;
                            const collectParens = n => {
                                if (!n) return [];
                                if (n instanceof LeanParenthesis) return [n];
                                const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                                return a.flatMap(collectParens);
                            };
                            const parens = collectParens(binderNode);
                            if (parens.length > 0) {
                                const lines = parens.map((p) => {
                                    const arg = p.arg;
                                    if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                        return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                    return strStmt(p);
                                });
                                if (lines.length) {
                                    lines[lines.length - 1] += ' :';
                                    simpleExplicit = lines.join('\n');
                                }
                            }

                            const innerLhs = inner.lhs;
                            implyNode =
                                (innerLhs &&
                                    innerLhs.rhs &&
                                    (innerLhs.rhs instanceof LeanStatements || innerLhs.rhs instanceof LeanArgsNewLineSeparated))
                                    ? innerLhs.rhs
                                    : inner.rhs || declspec;
                        } else if (declspec.rhs) {
                            // Standard `name (binders) : proposition := by …`
                            // binders live in the colon LHS, proposition in RHS.
                            const nameNode =
                                (inner.lhs instanceof LeanToken || inner.lhs instanceof LeanProperty)
                                    ? inner.lhs
                                    : (inner instanceof LeanToken || inner instanceof LeanProperty)
                                        ? inner
                                        : null;
                            if (nameNode) simpleName = nameNode;
                            const collectParens = n => {
                                if (!n) return [];
                                if (n instanceof LeanParenthesis) return [n];
                                const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                                return a.flatMap(collectParens);
                            };
                            const parens = collectParens(nameNode === inner ? null : inner);
                            if (parens.length > 0) {
                                const lines = parens.map((p) => {
                                    const arg = p.arg;
                                    if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                        return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                    return strStmt(p);
                                });
                                if (lines.length) {
                                    lines[lines.length - 1] += ' :';
                                    simpleExplicit = lines.join('\n');
                                }
                            }
                            implyNode = declspec.rhs;
                        }
                    }
                    let implyOut;
                    if (flatImplyStmts && flatImplyStmts.length > 0) {
                        const imply = [...flatImplyStmts, assignment.lhs];
                        markRandomVarSequence(imply, flatRvNames);
                        const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                        let implyLatex;
                        if (imply.length > 1 && imply[0] instanceof Lean_let) {
                            implyLatex = implyLetAlignLatex(imply, syntax);
                        } else {
                            implyLatex = imply
                                .map((st) => implyConclusionLatex(st, syntax))
                                .join('\n');
                        }

                        implyOut = { lean: implyLean + ' :=' + (by ? ` ${by}` : ''), latex: implyLatex };
                    } else {
                        markRandomVarSequence([implyNode], flatRvNames);
                        const implyLean = unindentTwo(strStmt(implyNode)) + ' :=' + (by ? ` ${by}` : '');
                        const implyLatex = implyConclusionLatex(implyNode, syntax);
                        implyOut = { lean: implyLean, latex: implyLatex };
                    }
                    syntax.letBindings = buildLetBindings(flatImplyStmts ?? []);
                    const proof = innerAssign.rhs;
                    let proofOut;
                    const proofArg = proof && typeof proof === 'object' && 'arg' in proof ? proof.arg : proof;
                    const hasProofArgs = proofArg && typeof proofArg === 'object' && Array.isArray(proofArg.args);
                    if (by) {
                        proofOut = { [by]: hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [] };
                    } else {
                        proofOut = hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [{ lean: strStmt(proof || ''), latex: null }];
                    }
                    let attribute = extractAttribute(stmt.attribute);
                    const name = simpleName ?? stmt.assignment;
                    lemma.push({
                        comment,
                        accessibility: String(stmt.accessibility),
                        attribute,
                        name: strStmt(name).trim(),
                        instImplicit: normalizeInstImplicit(unindentTwo(flatInstImplicit.join('\n'))),
                        implicit: '',
                        explicit: simpleExplicit,
                        given: flatGiven,
                        default: '',
                        imply: implyOut,
                        proof: proofOut,
                    });
                    comment = null;
                } else {
                    error.push({
                        code: strStmt(declspec),
                        line: 0,
                        info: 'declspec of lemma must be of LeanColon Type',
                        type: 'linter',
                    });
                }
            } else {
                error.push({
                    code: strStmt(stmt),
                    line: 0,
                    info: 'lemma must be of LeanAssign Type',
                    type: 'linter',
                });
            }
        } else if (stmt instanceof Lean_def) {
            preamble.push(strStmt(stmt));
        } else if (stmt instanceof Lean_open) {
            let o = stmt.arg;
            if (o instanceof LeanArgsSpaceSeparated) {
                if (o.args.length === 2 && o.args[1] instanceof LeanParenthesis) {
                    const defs = o.args[1].arg;
                    open.push({
                        [strStmt(o.args[0])]:
                            defs instanceof LeanArgsSpaceSeparated
                                ? defs.args.map((a) => strStmt(a))
                                : [strStmt(defs.arg)],
                    });
                } else open.push(o.args.map((a) => strStmt(a)).filter((s) => s.trim()));
            } else open.push([strStmt(o.text)]);
        } else if (stmt instanceof Lean_set_option) {
            const a = stmt.arg;
            if (a instanceof LeanArgsSpaceSeparated) set_option.push(a.args.map((x) => strStmt(x)));
        } else if (stmt instanceof LeanLineComment) {
            const m = /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.exec(stmt.text);
            if (m) date[m[1]] = m[2];
            else comment = stmt.text;
        } else if (stmt instanceof LeanBlockComment) {
            comment = stmt.text;
        }
    }

    return {
        imports: $import,
        open,
        set_option,
        preamble,
        lemma,
        date,
        error,
    };
}

export class LeanModule extends LeanStatements {
    get root() {
        return this;
    }

    get stack_priority() {
        return -3;
    }

    array_push(vars, lhs, rhs) {
        arrayPushVars(vars, lhs, rhs);
    }

    create_property(module) {
        const parts = String(module).split('.');
        return parts.reduce((carry, token) => {
            const t = new LeanToken(token, 0, 0);
            return carry ? new LeanProperty(carry, t, 0, 0) : t;
        }, null);
    }

    decode(json, latex) {
        const keys = Object.keys(json);
        if (!keys.length) return;
        const line = keys[0];
        const latexFormat = json[line];
        if (Object.prototype.hasOwnProperty.call(latex, line)) {
            if (!Array.isArray(latex[line])) latex[line] = [latex[line]];
            latex[line].push(latexFormat);
        } else {
            latex[line] = latexFormat;
        }
    }

    echo() {
        this.import('sympy.printing.echo');
        const {args} = this;
        for (let i = 0; i < args.length; i++) args[i].echo();
    }

    echo2vue(_leanFile) {
        throw new Error(
            'LeanModule.echo2vue runs only on the Node server (see server/lean/echo2vue.mjs `runEcho2Vue`).',
        );
    }

    /**
     * After writing `*.echo.lean` with inflated maxHeartbeats (×5 for Lean server),
     * revert those nodes in the AST so `render2vue` reports the original values.
     */
    restoreMaxHeartbeats() {
        for (const node of this.args) {
            if (node instanceof Lean_set_option) {
                const arg = node.arg;
                if (arg instanceof LeanArgsSpaceSeparated && arg.args.length === 2) {
                    const [nameTok, valTok] = arg.args;
                    if (
                        nameTok instanceof LeanToken &&
                        valTok instanceof LeanToken &&
                        nameTok.text === 'maxHeartbeats'
                    ) {
                        const v = parseInt(String(valTok.text), 10);
                        if (!Number.isNaN(v)) {
                            valTok.text = String(Math.floor(v / 5));
                            break;
                        }
                    }
                }
            }
        }
    }

    import(module) {
        this.args.unshift(new Lean_import(this.create_property(module), 0, 0));
    }

    /**
     * Port of `LeanModule::insert`.
     * @param {LeanCaret} caret
     * @param {string | typeof Lean} func class name or constructor
     */
    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? LEAN_CLASSES[func] : func;
            this.push(new Ctor(caret, this.indent, caret.level));
            return caret;
        }
        return caret;
    }

    parse_vars(implicit) {
        return parseVars(implicit);
    }

    parse_vars_default(defaultList) {
        const vars = [];
        for (const parenthesis of defaultList) {
            if (parenthesis instanceof LeanParenthesis) {
                const colon = parenthesis.arg;
                if (colon instanceof LeanColon) arrayPushVars(vars, colon.lhs, colon.rhs);
            }
        }
        return vars;
    }

    render2vue(echo, modify = null, syntax = {}) {
        return leanModuleRender2vue(this, echo, modify, syntax);
    }

    static merge_proof(proof, echo, syntax = {}) {
        return leanModuleMergeProof(proof, echo, syntax);
    }

    leanModuleStrSegments() {
        const args = this.args;
        /** @type {string[]} */
        const parts = [];
        const skip = new Set();
        const indentText = (s, indent) => {
            if (indent <= 0) return s;
            const pad = ' '.repeat(indent);
            return s
                .split('\n')
                .map((line) => (line === '' ? line : pad + line))
                .join('\n');
        };
        for (let i = 0; i < args.length; i++) {
            if (skip.has(i)) continue;
            const a = args[i];
            if (a == null) continue;
            if (a instanceof LeanCaret) {
                parts.push('');
                continue;
            }
            if (a instanceof Lean_def) {
                const asn = a.assignment;
                if (asn instanceof LeanAssign && asn.rhs instanceof LeanCaret) {
                    const tail = consumeEchoAssignProofTail(args, i + 1, indentText);
                    if (tail) {
                        for (let k = i + 1; k <= tail.endJ; k++) skip.add(k);
                        const acc = a.accessibility === 'public' ? '' : `${a.accessibility} `;
                        const kw = `${acc}${a.func} `;
                        const head = a.attribute ? `${String(a.attribute)}\n${kw}` : kw;
                        const asnPad = ' '.repeat(Math.max(0, asn.indent ?? 0));
                        let block = `${head}${asnPad}${String(asn.lhs)} :=`;
                        for (const c of tail.cmts) block += `\n${String(c)}`;
                        block += `\n${tail.proofStr}`;
                        parts.push(block);
                        continue;
                    }
                }
            }
            if (a instanceof LeanAssign && a.rhs instanceof LeanCaret) {
                const tail = consumeEchoAssignProofTail(args, i + 1, indentText);
                if (tail) {
                    for (let k = i + 1; k <= tail.endJ; k++) skip.add(k);
                    const asnPad = ' '.repeat(Math.max(0, a.indent ?? 0));
                    let block = `${asnPad}${String(a.lhs)} :=`;
                    for (const c of tail.cmts) block += `\n${String(c)}`;
                    block += `\n${tail.proofStr}`;
                    parts.push(block);
                    continue;
                }
            }
            if (a instanceof LeanTactic) {
                const next = i + 1 < args.length ? args[i + 1] : null;
                let danglingStc = false;
                for (let k = 0; k < a.args.length; k++) {
                    const x = a.args[k];
                    if (x instanceof LeanSequentialTacticCombinator && x.arg instanceof LeanCaret) {
                        danglingStc = true;
                        break;
                    }
                }
                if (danglingStc && next instanceof LeanTacticBlock) {
                    skip.add(i + 1);
                    const indent = Math.max(a.indent ?? 0, next.indent ?? 0);
                    const as = String(a);
                    const ns = String(next);
                    const join = as.endsWith('\n') ? '' : '\n';
                    parts.push(indentText(`${as}${join}${ns}`, indent));
                    continue;
                }
            }
            if (a instanceof LeanColon && a.parent === this) {
                const indent = a.indent ?? 0;
                if (indent > 0) {
                    let k = i + 1;
                    while (k < args.length && args[k] instanceof LeanCaret) k++;
                    let next = args[k];
                    const echoTail =
                        next instanceof LeanAssign &&
                        next.rhs instanceof LeanCaret &&
                        consumeEchoAssignProofTail(args, k + 1, indentText);
                    let assignAfterColon = next;
                    if (!(next instanceof LeanAssign)) {
                        let j = k;
                        while (j < args.length) {
                            const x = args[j];
                            if (x instanceof LeanCaret) {
                                j++;
                                continue;
                            }
                            if (x instanceof Lean_land) {
                                j++;
                                continue;
                            }
                            if (x instanceof LeanAssign) {
                                assignAfterColon = x;
                                break;
                            }
                            break;
                        }
                    }
                    let prevIdx = i - 1;
                    while (prevIdx >= 0) {
                        const p = args[prevIdx];
                        if (p == null || p instanceof LeanCaret) {
                            prevIdx--;
                            continue;
                        }
                        if (
                            p instanceof LeanBrace ||
                            p instanceof LeanBracket ||
                            p instanceof LeanParenthesis ||
                            p instanceof LeanLineComment ||
                            p instanceof LeanBlockComment
                        ) {
                            prevIdx--;
                            continue;
                        }
                        break;
                    }
                    const lemmaColonMatchBy =
                        prevIdx >= 0 &&
                        args[prevIdx] instanceof Lean_lemma &&
                        assignAfterColon instanceof LeanAssign &&
                        assignAfterColon.rhs instanceof LeanBy &&
                        (assignAfterColon.lhs instanceof Lean_match ||
                            assignAfterColon.lhs instanceof LeanParenthesis);
                    if (echoTail || lemmaColonMatchBy) {
                        const lines = String(a).split('\n');
                        if (lines[0] !== '') lines[0] = ' '.repeat(indent) + lines[0];
                        parts.push(lines.join('\n'));
                        continue;
                    }
                }
            }
            let out = String(a);
            if (a instanceof LeanTactic && (a.indent ?? 0) === 0) {
                let p = i - 1;
                while (p >= 0 && (args[p] instanceof LeanCaret || args[p] == null || skip.has(p))) p--;
                const prev = p >= 0 ? args[p] : null;
                const indent = prev instanceof Lean_let ? prev.indent ?? 0 : 0;
                if (indent > 0) out = ' '.repeat(indent) + out;
            }
            parts.push(out);
        }
        return parts;
    }

    strFormat() {
        this._moduleStrSegs = this.leanModuleStrSegments();
        const n = this._moduleStrSegs.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join('\n');
    }

    strArgs() {
        const segs = this._moduleStrSegs ?? this.leanModuleStrSegments();
        delete this._moduleStrSegs;
        return segs;
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    // insert_colon, insert_if, insert_left, insert_newline, insert_space, insert_tactic: inherit `LeanStatements` / `Lean`.
}

/** Top-level commands (`import` / `open` / `set_option` / `namespace`): `stack_priority` 27 except `namespace` (inherits unary 47). */
class LeanCommand extends LeanUnary {
    get command() {
        return this.operator;
    }

    is_indented() {
        return false;
    }

    toJSON() {
        return { [this.func]: this.arg.toJSON() };
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}

/** `import %s`. */
class Lean_import extends LeanCommand {
    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'import';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = LEAN_CLASSES[func];
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

class Lean_open extends LeanCommand {
    get stack_priority() {
        return 27;
    }
    get operator() {
        return this.scoped ? 'open scoped' : 'open';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = LEAN_CLASSES[func];
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** `set_option %s`. */
class Lean_set_option extends LeanCommand {
    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'set_option';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = LEAN_CLASSES[func];
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    echo() {
        const {arg} = this;
        if (arg instanceof LeanArgsSpaceSeparated && arg.args.length === 2) {
            const {args} = arg;
            if (args[0] instanceof LeanToken && args[1] instanceof LeanToken && args[0].text === 'maxHeartbeats') {
                args[1].text = String(parseInt(String(args[1].text), 10) * 5);
            }
        }
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** `namespace %s`. */
class Lean_namespace extends LeanCommand {
    get operator() {
        return 'namespace';
    }
}

/** Bar, then `=>` and related arrow nodes. */
class LeanBar extends LeanUnary {
    get stack_priority() {
        return LeanAssign.input_priority ?? 20;
    }

    get operator() {
        return '|';
    }

    get command() {
        return '|';
    }

    echo() {
        this.arg.echo();
    }

    insert_bar(caret, prevToken, next) {
        const p = this.parent;
        if (p instanceof LeanTactic) {
            const c = new LeanCaret(this.indent, caret.level);
            p.push(new LeanBar(c, this.indent, c.level));
            return c;
        }
        return super.insert_bar(caret, prevToken, next);
    }

    insert_comma(caret) {
        if (caret === this.arg) {
            const $new = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
            return $new;
        }
        throw new Error(`LeanBar.insert_comma: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    is_indented() {
        return !(this.parent instanceof LeanTactic);
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    split(syntax) {
        const arrow = this.arg;
        if (arrow instanceof LeanRightarrow) {
            const self = this.clone();
            const statements = [self];
            const clonedArrow = /** @type {LeanRightarrow} */ (self.arg);
            const stmts = clonedArrow.rhs;
            if (stmts instanceof LeanStatements) {
                clonedArrow.rhs = new LeanCaret(clonedArrow.indent, stmts.level);
                stmts.swap_echo_star(syntax, statements);
            }
            return statements;
        }
        return [this];
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}

const arrowsLate = {};
const arrowsFamily = createArrowsFamily({
    LeanBinary,
    LeanUnary,
    LeanToken,
    LeanCaret,
    LeanColon,
    LeanProperty,
    LeanBar,
    LeanStatements,
    LeanLineComment,
    classRegistry: arithmeticClassRegistry,
    arrowsLate,
});
export const LeanRightarrow = arrowsFamily.LeanRightarrow;
export const Lean_rightarrow = arrowsFamily.Lean_rightarrow;
export const Lean_mapsto = arrowsFamily.Lean_mapsto;
const Lean_leftarrow = arrowsFamily.Lean_leftarrow;

const negationFamily = createNegationFamily({
    LeanUnary,
    LeanProp,
    LeanStatements,
});
const Lean_lnot = negationFamily.Lean_lnot;
const LeanNot = negationFamily.LeanNot;

const matchLate = {};
const matchFamily = createMatchFamily({
    LeanArgs,
    LeanColon,
    LeanCaret,
    LeanBar,
    LeanRightarrow,
    classRegistry: arithmeticClassRegistry,
    matchLate,
});
const Lean_match = matchFamily.Lean_match;

const iteLate = {};
const iteFamily = createIteFamily({
    LeanArgs,
    LeanCaret,
    LeanColon,
    LeanStatements,
    iteLate,
});
export const LeanIte = iteFamily.LeanIte;

class ParserPrefixExpr {
    /**
     * @param {LeanToken} func
     * @param {ParserPrefixExpr[]} args
     */
    constructor(func, args) {
        this.func = func;
        this.args = args;
        /** @type {ParserPrefixExpr | null} */
        this.parent = null;
        /** @type {Record<string, unknown>} */
        this.cache = {};
        for (const arg of args) {
            if (arg) arg.parent = this;
        }
    }

    /**
     * @param {(n: ParserPrefixExpr) => void} visit
     */
    traverse(visit) {
        visit(this);
        for (const arg of this.args) arg.traverse(visit);
    }

    size() {
        if (this.cache.size != null) return this.cache.size;
        let s = 1;
        for (const arg of this.args) s += arg.size();
        this.cache.size = s;
        return s;
    }
}

function leanEvalPrefix(expressions, operandCount) {
    const stack = [];
    for (let i = expressions.length - 1; i >= 0; i--) {
        const token = expressions[i];
        const n = operandCount(token);
        const operand = [];
        for (let k = 0; k < n; k++) {
            if (!stack.length) break;
            operand[k] = stack.pop();
        }
        stack.push(new ParserPrefixExpr(token, operand));
    }
    return stack.reverse();
}

/** Path lookup for type-variable maps (`get_type` / `isProp`). */
function leanVarsGetitem(root, keys) {
    let cur = root;
    for (const k of keys) {
        if (k === '' || k == null) return undefined;
        if (cur == null || typeof cur !== 'object') return undefined;
        cur = cur[k];
    }
    return cur;
}

const argsLate = {};
const argsFamily = createArgsFamily({
    LeanArgs,
    LeanBinary,
    LeanMultipleLine,
    LeanAssign,
    LeanBar,
    LeanBinaryBoolean,
    LeanCaret,
    LeanColon,
    LeanEq,
    LeanGetElem,
    LeanGetElemQue,
    LeanGetElemQuote,
    LeanIte,
    LeanLogic,
    LeanProperty,
    LeanRelational,
    LeanRightarrow,
    LeanStatements,
    LeanToken,
    Lean_land,
    Lean_mapsto,
    leanEvalPrefix,
    leanVarsGetitem,
    classRegistry: arithmeticClassRegistry,
    argsLate,
});
export const LeanArgsSpaceSeparated = argsFamily.LeanArgsSpaceSeparated;
export const LeanArgsNewLineSeparated = argsFamily.LeanArgsNewLineSeparated;
export const LeanArgsIndented = argsFamily.LeanArgsIndented;
export const LeanArgsCommaSeparated = argsFamily.LeanArgsCommaSeparated;
export const LeanArgsSemicolonSeparated = argsFamily.LeanArgsSemicolonSeparated;
export const LeanArgsCommaNewLineSeparated = argsFamily.LeanArgsCommaNewLineSeparated;

const tacticLate = {};
const tacticFamily = createTacticFamily({
    LeanArgs,
    LeanArgsCommaNewLineSeparated,
    LeanArgsCommaSeparated,
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSemicolonSeparated,
    LeanArgsSpaceSeparated,
    LeanAssign,
    LeanBar,
    LeanBinary,
    LeanCaret,
    LeanColon,
    LeanIte,
    LeanLineComment,
    LeanModule,
    LeanProperty,
    LeanUnary,
    Lean_match,
    LeanRightarrow,
    LeanStatements,
    LeanToken,
    escapeSpecialsForLatex,
    leanIsInfixContinue,
    leanSubtreeContains,
    classRegistry: arithmeticClassRegistry,
    tacticLate,
});
export const LeanSyntax = tacticFamily.LeanSyntax;
export const LeanTactic = tacticFamily.LeanTactic;

export const LeanBy = tacticFamily.LeanBy;
const LeanFrom = tacticFamily.LeanFrom;
const LeanCalc = tacticFamily.LeanCalc;
const LeanMOD = tacticFamily.LeanMOD;
const LeanUsing = tacticFamily.LeanUsing;
export const LeanAt = tacticFamily.LeanAt;
const LeanIn = tacticFamily.LeanIn;
const LeanGeneralizing = tacticFamily.LeanGeneralizing;
export const LeanSequentialTacticCombinator = tacticFamily.LeanSequentialTacticCombinator;
const LeanTacticBlock = tacticFamily.LeanTacticBlock;
const LeanWith = tacticFamily.LeanWith;
const LeanAttribute = tacticFamily.LeanAttribute;

const declLate = {};
const declFamily = createDeclFamily({
    Lean,
    LeanArgs,
    LeanArgsCommaSeparated,
    LeanArgsNewLineSeparated,
    LeanArgsSemicolonSeparated,
    LeanArgsSpaceSeparated,
    LeanAssign,
    LeanBinary,
    LeanBy,
    LeanCalc,
    LeanCaret,
    LeanColon,
    LeanSequentialTacticCombinator,
    LeanStatements,
    LeanSyntax,
    LeanTactic,
    LeanTacticBlock,
    LeanToken,
    declLate,
});
export const Lean_def = declFamily.Lean_def;
export const Lean_theorem = declFamily.Lean_theorem;
export const Lean_abbrev = declFamily.Lean_abbrev;
const Lean_where = declFamily.Lean_where;
export const Lean_class = declFamily.Lean_class;
export const Lean_instance = declFamily.Lean_instance;
export const Lean_macro = declFamily.Lean_macro;
export const Lean_syntax = declFamily.Lean_syntax;
export const Lean_lemma = declFamily.Lean_lemma;
const Lean_let = declFamily.Lean_let;
const Lean_have = declFamily.Lean_have;
const Lean_set = declFamily.Lean_set;
const Lean_replace = declFamily.Lean_replace;
const Lean_show = declFamily.Lean_show;

const funFamily = createFunFamily({
    LeanUnary,
    LeanArgsNewLineSeparated,
    LeanStatements,
});
const Lean_fun = funFamily.Lean_fun;

const bigopsLate = {};
const bigopsFamily = createBigOpsFamily({
    LeanArgs,
    LeanArgsCommaNewLineSeparated,
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanCaret,
    LeanColon,
    LeanEq,
    LeanIn,
    LeanIte,
    LeanProperty,
    LeanRelational,
    LeanStatements,
    LeanToken,
    LeanUpto,
    Lean_in,
    Lean_rightarrow,
    strStmt,
    bigopsLate,
});
const LeanBigOperator = bigopsFamily.LeanBigOperator;
const Lean_sum = bigopsFamily.Lean_sum;
const Lean_lim = bigopsFamily.Lean_lim;
const Lean_prod = bigopsFamily.Lean_prod;
const Lean_int = bigopsFamily.Lean_int;
const Lean_bigcap = bigopsFamily.Lean_bigcap;
const Lean_bigcup = bigopsFamily.Lean_bigcup;
const LeanInf = bigopsFamily.LeanInf;
const LeanSup = bigopsFamily.LeanSup;
const LeanStack = bigopsFamily.LeanStack;

const quantifierLate = {};
const quantifierFamily = createQuantifierFamily({
    LeanProp,
    LeanBigOperator,
    LeanArgsSpaceSeparated,
    LeanCaret,
    LeanIn,
    LeanColon,
    quantifierLate,
});
const LeanQuantifier = quantifierFamily.LeanQuantifier;
const Lean_forall = quantifierFamily.Lean_forall;
const Lean_exists = quantifierFamily.Lean_exists;

export class LeanParser extends AbstractParser {
    constructor() {
        super(null);
        this.tokens = [];
        this.start_idx = 0;
        this.root = null;
    }

    toString() {
        return String(this.root);
    }

    /**
     * Port of `LeanParser::build`.
     * @param {string} text
     */
    build(text) {
        this.init();
        if (!text.endsWith('\n')) text += '\n';
        this.tokens = Array.from(text.matchAll(/\w+|\W/gu), (m) => m[0]);
        const { tokens } = this;
        const length = tokens.length;
        this.start_idx = 0;
        for (; this.start_idx < length; ++this.start_idx) {
            this.parse(tokens[this.start_idx], this);
            if (!this.caret) break;
        }
        return this.root;
    }

    init() {
        const caret = new LeanCaret(0, 0);
        this.caret = caret;
        this.root = new LeanModule([caret], 0, 0);
    }

    parseKeywordAsPropertyField(caret, token) {
        if (caret instanceof LeanCaret && caret.parent instanceof LeanProperty) {
            let word = token;
            while (isIdentContinueToken(this.tokens[this.start_idx + 1])) {
                this.start_idx++;
                word += this.tokens[this.start_idx];
            }
            return caret.parent.insert_word(caret, word);
        }
    }
}

/**
 * Extra binary operators from `token2classname`. `export const Name = class extends …` keeps
 * declaration-order tooling aligned with the shared class list length; inferred `constructor.name` stays `Name`.
 */
export const Lean_ominus = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_oslash = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_circledcirc = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_circledast = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_circleeq = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_circleddash = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_boxplus = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_boxminus = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_boxtimes = class extends LeanBinary {
    static input_priority = 67;
};

export const Lean_dotsquare = class extends LeanBinary {
    static input_priority = 67;
};

export const LeanEDiv = class extends LeanBinary {
    static input_priority = 70;
};

logicLate.LeanStatements = LeanStatements;
const arithmeticLate = {};
const pairedFamily = createPairedFamily({
    LeanUnary,
    LeanArgsCommaNewLineSeparated,
    LeanArgsCommaSeparated,
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSemicolonSeparated,
    LeanArgsSpaceSeparated,
    LeanAssign,
    LeanBigOperator,
    LeanBinaryBoolean,
    LeanBy,
    LeanCaret,
    LeanColon,
    LeanGetElem,
    LeanGetElemQue,
    LeanGetElemQuote,
    LeanIte,
    LeanLineComment,
    LeanModule,
    LeanProperty,
    LeanQuantifier,
    LeanRelational,
    LeanRightarrow,
    LeanSetOperator,
    LeanStack,
    LeanStatements,
    LeanTactic,
    LeanToken,
    LeanWith,
    Lean_fun,
    Lean_let,
    Lean_lim,
    Lean_lt,
    Lean_mapsto,
    Lean_rightarrow,
    classRegistry: arithmeticClassRegistry,
    arithmeticLate,
});
export const LeanParenthesis = pairedFamily.LeanParenthesis;
membershipLate.LeanParenthesis = LeanParenthesis;
membershipLate.LeanIte = LeanIte;
const LeanPairedGroup = pairedFamily.LeanPairedGroup;
const LeanAngleBracket = pairedFamily.LeanAngleBracket;
const LeanBracket = pairedFamily.LeanBracket;
const LeanBrace = pairedFamily.LeanBrace;
const LeanAbs = pairedFamily.LeanAbs;
const LeanNorm = pairedFamily.LeanNorm;
const LeanInner = pairedFamily.LeanInner;
const LeanCeil = pairedFamily.LeanCeil;
const LeanFloor = pairedFamily.LeanFloor;
const LeanWhiteSquareBracket = pairedFamily.LeanWhiteSquareBracket;
const LeanDoubleAngleQuotation = pairedFamily.LeanDoubleAngleQuotation;
const LeanSingleAngleQuotation = pairedFamily.LeanSingleAngleQuotation;

const leanArithmeticFamily = createArithmeticFamily({
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
    classRegistry: arithmeticClassRegistry,
});
Object.assign(arithmeticLate, {
    LeanArithmetic: leanArithmeticFamily.LeanArithmetic,
    LeanBitOr: leanArithmeticFamily.LeanBitOr,
    LeanPow: leanArithmeticFamily.LeanPow,
    LeanUnaryArithmeticPost: leanArithmeticFamily.LeanUnaryArithmeticPost,
    LeanUnaryArithmeticPre: leanArithmeticFamily.LeanUnaryArithmeticPre,
});
export const {
    LeanArithmetic,
    LeanAdd,
    LeanSub,
    LeanMul,
    Lean_times,
    LeanMatMul,
    Lean_bullet,
    Lean_odot,
    Lean_otimes,
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
    LeanUnaryArithmeticPost,
} = leanArithmeticFamily;

const {
    Lean_otimesSub,
    LeanUnaryArithmetic,
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
} = leanArithmeticFamily;
quantifierLate.Lean_partial = Lean_partial;
Object.assign(bigopsLate, {
    LeanAdd,
    LeanPlus,
    LeanQuantifier,
    Lean_partial,
    LeanParenthesis,
    LeanDoubleAngleQuotation,
});
Object.assign(indexingLate, {
    LeanParenthesis,
    LeanBitOr,
    LeanCondBar,
    Lean_fun,
});
Object.assign(arrowsLate, {
    LeanWith,
    Lean_match,
    LeanTactic,
    LeanArgsCommaSeparated,
    LeanArgsSpaceSeparated,
    LeanAngleBracket,
    LeanPlus,
    LeanNeg,
    LeanPosPart,
    LeanNegPart,
});
Object.assign(matchLate, {
    LeanWith,
    LeanArgsCommaSeparated,
});
Object.assign(iteLate, {
    LeanTactic,
    Lean_let,
    LeanArgsNewLineSeparated,
});
Object.assign(argsLate, {
    LeanAngleBracket,
    LeanAppend,
    LeanBitOr,
    LeanBracket,
    LeanBy,
    LeanCalc,
    LeanDiv,
    LeanDoubleAngleQuotation,
    LeanParenthesis,
    LeanPreimage,
    LeanQuantifier,
    LeanStack,
    LeanSyntax,
    LeanTactic,
    LeanTacticBlock,
    Lean_fun,
    Lean_int,
    Lean_show,
});
Object.assign(tacticLate, {
    LeanAngleBracket,
    LeanBitOr,
    LeanBrace,
    LeanPairedGroup,
    LeanParenthesis,
    Lean_def,
    Lean_have,
    Lean_let,
});
Object.assign(declLate, {
    LeanAngleBracket,
});
Object.assign(baseLate, {
    LeanArgsCommaNewLineSeparated,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanAssign,
    LeanAt,
    LeanAttribute,
    LeanBEq,
    LeanBigOperator,
    LeanBitwiseOr,
    LeanBracket,
    LeanCalc,
    LeanCaret,
    LeanCeil,
    LeanColon,
    LeanCondBar,
    LeanConstruct,
    LeanDoubleAngleQuotation,
    LeanEq,
    LeanFloor,
    LeanGetElem,
    LeanGetElemQue,
    LeanGetElemQuote,
    LeanGetWhiteSquareBracket,
    LeanInner,
    LeanIte,
    LeanLogicOr,
    LeanMatMul,
    LeanMul,
    LeanNotEquiv,
    LeanPairedGroup,
    LeanParenthesis,
    LeanPreimage,
    LeanProperty,
    LeanQuantifier,
    LeanRightarrow,
    LeanSequentialTacticCombinator,
    LeanStatements,
    LeanTactic,
    LeanToken,
    LeanUnaryArithmeticPost,
    LeanUpto,
    LeanWhiteSquareBracket,
    LeanWith,
    Lean_cdotp,
    Lean_circ,
    Lean_def,
    Lean_equiv,
    Lean_ge,
    Lean_gg,
    Lean_import,
    Lean_int,
    Lean_le,
    Lean_lemma,
    Lean_let,
    Lean_ll,
    Lean_mapsto,
    Lean_namespace,
    Lean_ne,
    Lean_open,
    Lean_otimes,
    Lean_otimesSub,
    Lean_perp,
    Lean_rightarrow,
    Lean_set_option,
    Lean_simeq,
    Lean_sum,
    Lean_theorem,
    Lean_times,
    Lean_where,
});

/** Concrete AST / parser node classes only (keys = `constructor.name`). No abstract/intermediate bases (`Lean`, `LeanArgs`, `LeanBinary`, …). */
const LEAN_CLASSES = {
    LeanArgsCommaSeparated,
    LeanArgsNewLineSeparated,
    LeanArgsCommaNewLineSeparated,
    LeanArgsSemicolonSeparated,
    LeanColon,
    LeanRightarrow,
    LeanAssign,
    LeanArgsIndented,
    LeanBy,
    LeanCalc,
    LeanAttribute,
    Lean_leftarrow,
    LeanNeg,
    LeanParenthesis,
    LeanArgsSpaceSeparated,
    LeanStatements,
    LeanModule,
    Lean_def,
    Lean_abbrev,
    Lean_theorem,
    Lean_lemma,
    Lean_class,
    Lean_instance,
    Lean_macro,
    Lean_syntax,
    Lean_where,
    LeanCaret,
    Lean_let,
    Lean_have,
    Lean_replace,
    Lean_set,
    Lean_fun,
    Lean_match,
    LeanWith,
    LeanToken,
    LeanLineComment,
    LeanBlockComment,
    LeanDocString,
    LeanProperty,
    LeanUpto,
    LeanGetElem,
    LeanGetWhiteSquareBracket,
    LeanGetElemQue,
    LeanGetElemQuote,
    LeanStack,
    LeanBracket,
    LeanBrace,
    LeanAngleBracket,
    LeanAbs,
    LeanCondBar,
    LeanNorm,
    LeanInner,
    LeanCeil,
    LeanFloor,
    LeanWhiteSquareBracket,
    LeanFrom,
    LeanDoubleAngleQuotation,
    LeanSingleAngleQuotation,
    Lean_equiv,
    LeanNotEquiv,
    LeanAt,
    LeanTactic,
    LeanTacticBlock,
    LeanSequentialTacticCombinator,
    LeanIte,
    LeanAdd,
    LeanSub,
    LeanMul,
    LeanMatMul,
    Lean_sqcap,
    Lean_sqcup,
    LeanDiv,
    Lean_times,
    LeanPow,
    LeanConstruct,
    LeanAppend,
    Lean_bigcap,
    Lean_bigcup,
    LeanInf,
    LeanSup,
    Lean_bullet,
    Lean_exists,
    Lean_forall,
    Lean_odot,
    Lean_otimes,
    Lean_oplus,
    LeanFDiv,
    LeanModular,
    Lean_ll,
    Lean_lll,
    Lean_gg,
    Lean_ggg,
    LeanGeneralizing,
    Lean_cdotp,
    Lean_circ,
    Lean_blacktriangleright,
    LeanBitAnd,
    LeanBitwiseAnd,
    LeanBitwiseXor,
    LeanBitOr,
    LeanBitwiseOr,
    Lean_land,
    LeanLogicAnd,
    LeanLogicOr,
    LeanLogicXor,
    Lean_cup,
    Lean_cap,
    Lean_setminus,
    Lean_subseteq,
    Lean_subset,
    Lean_supseteq,
    Lean_supset,
    Lean_is,
    Lean_is_not,
    LeanMethodChaining,
    LeanMOD,
    Lean_approx,
    Lean_lt,
    Lean_gt,
    Lean_ge,
    Lean_le,
    Lean_lazy,
    LeanEq,
    Lean_perp,
    LeanBEq,
    Lean_ne,
    Lean_simeq,
    Lean_asymp,
    LeanDvd,
    Lean_in,
    Lean_notin,
    Lean_leftrightarrow,
    Lean_rightarrow,
    Lean_lor,
    LeanEDiv,
    Lean_ominus,
    Lean_oslash,
    Lean_prod,
    Lean_int,
    Lean_circledcirc,
    Lean_circledast,
    Lean_circleeq,
    Lean_circleddash,
    Lean_boxplus,
    Lean_boxminus,
    Lean_boxtimes,
    Lean_dotsquare,
    Lean_mapsto,
    Lean_bne,
    LeanBar,
    LeanCubicRoot,
    LeanCube,
    Lean_import,
    LeanIn,
    LeanInv,
    LeanPreimage,
    LeanFactorial,
    Lean_lnot,
    LeanConj,
    Lean_namespace,
    LeanNegPart,
    LeanNot,
    Lean_open,
    Lean_partial,
    LeanPipeForward,
    LeanPlus,
    LeanPosPart,
    LeanQuarticRoot,
    Lean_set_option,
    Lean_show,
    Lean_sum,
    Lean_lim,
    LeanSquare,
    Lean_sqrt,
    LeanTesseract,
    LeanTranspose,
    Lean_uparrow,
    LeanUparrow,
    LeanUsing,
};
arithmeticClassRegistry.map = LEAN_CLASSES;

export function compile(code) {
    return LeanParser.instance.build(code);
}

LeanParser.instance = new LeanParser();
/**
 * Parse a Lean source file and extract the theorem structure.
 *
 * Designed for FLT solution files (`S_<key>.lean`) which carry a theorem named
 * `solution` (the convention); some files also define helper theorems first.
 *
 * Returns a JSON object:
 *   { imports, namespace, theoremName, binders, conclusion, proof, key }
 *
 * @param {string} source - Lean source text
 * @param {string} [key] - the FLT key (from `S_<key>.lean`); used verbatim when
 *   supplied, otherwise derived from a `P2MW.S_<key>` / `P2M.S_<key>` namespace.
 * @returns {{imports:string[],namespace:string,theoremName:string,binders:string,conclusion:string,proof:string,key:string}|null}
 */
export function parseTheoremFile(source, key) {
    const ast = compile(source);
    if (!(ast instanceof LeanModule)) return null;

    const imports = [];
    let namespace = '';
    for (const node of ast.args) {
        if (!node) continue;
        if (node instanceof Lean_import) {
            imports.push(String(node).replace(/^import\s+/, '').trim());
        } else if (node instanceof Lean_namespace) {
            namespace = String(node).replace(/^namespace\s+/, '').trim();
        }
    }

    if (key == null) {
        if (namespace.startsWith('P2MW.S_')) {
            key = namespace.slice('P2MW.S_'.length);
        } else if (namespace.startsWith('P2M.S_')) {
            key = namespace.slice('P2M.S_'.length);
        } else {
            key = null;
        }
    }

    // Prefer `theorem/lemma solution`, then `theorem/lemma main`, otherwise the
    // first theorem/lemma in the file.
    let declMatch = /\b(?:theorem|lemma)\s+solution\b/.exec(source);
    if (!declMatch) declMatch = /\b(?:theorem|lemma)\s+main\b/.exec(source);
    if (!declMatch) declMatch = /\b(?:theorem|lemma)\s+(\S+)/.exec(source);
    if (!declMatch) return null;
    const theoremName = declMatch[0].trim().split(/\s+/)[1];
    const declStart = declMatch.index;

    // The declaration's terminating ':=' is the first ':=' after the keyword.
    const restart = source.slice(declStart);
    const assignMatch = /:=/.exec(restart);
    if (!assignMatch) return null;
    const assignIdx = declStart + assignMatch.index;

    // Declaration text: from the theorem keyword up to (but not including) ':='.
    let fullDecl = source.slice(declStart, assignIdx);
    fullDecl = fullDecl.replace(/^(?:theorem|lemma)\s+\S+\s*/, '').trim();

    // Split binders from conclusion at the first ':' at bracket depth 0.
    let depth = 0;
    let colonIdx = -1;
    for (let i = 0; i < fullDecl.length; i++) {
        const ch = fullDecl[i];
        if (ch === '{' || ch === '[' || ch === '(') depth++;
        else if (ch === '}' || ch === ']' || ch === ')') depth--;
        else if (ch === ':' && depth === 0) {
            colonIdx = i;
            break;
        }
    }
    if (colonIdx < 0) return null;
    const binders = fullDecl.slice(0, colonIdx).trim();
    const conclusion = fullDecl.slice(colonIdx + 1).trim();

    // Proof: raw source after ':='.  Drop a leading 'by' keyword so the rest is
    // the tactic block; otherwise keep the proof term verbatim.
    let proofStyle = 'term';
    let proof = source.slice(assignIdx + 2);
    const byTail = proof.match(/^[\s\n]*\bby\b/);
    if (byTail) {
        proofStyle = 'by';
        proof = proof.slice(byTail[0].length);
    }
    proof = proof.replace(/^\s*\n/, '');
    proof = proof.replace(/\n\s*(end\b[^\n]*)?\s*$/, '\n');

    return { imports, namespace, theoremName, binders, conclusion, proof, proofStyle, key };
}
