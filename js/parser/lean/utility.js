/**
 * Shared helpers for the Lean parser families in this directory.
 *
 * The class registry lives on `Lean` (`Lean.classes`, filled by `static { this.register(); }`).
 * `base.js` imports this module and this module imports `Lean` from `base.js`, so the two are a
 * cycle: whichever is evaluated first sees the other's bindings uninitialized. Nothing here may
 * touch `Lean` at module top level; the helpers below read `Lean.classes` only when called.
 */
import { Lean } from './base.js';

/** Relational / comparison ops; reused by token2classname and leanInfixContinue. */
export const leanRelationalTokens = Object.freeze({
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

export function leanIsInfixContinue(next) {
    return Object.hasOwn(leanInfixContinue, next);
}


/** Lean identifier continuation token (supports Unicode letters like Ξ). */
export function isIdentContinueToken(s) {
    if ('ᵀ²³⁴'.includes(s)) return false;
    return /^[\p{L}\p{N}_'!?₀-₉]+$/u.test(s);
}

export function escapeSpecialsForLatex(token) {
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
export function leanSubtreeContains(node, target) {
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
export function leanInsertComma(leaf) {
    const {LeanArgsSpaceSeparated, LeanTactic} = Lean.classes;
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
export function findInnermostOpenLeanAbsAncestor(from, caret) {
    const {LeanAbs} = Lean.classes;
    for (let p = from; p; p = p.parent) {
        if (!(p instanceof LeanAbs)) continue;
        if (p.is_closed === true) continue;
        if (caret != null && leanSubtreeContains(p.arg, caret)) return p;
    }
    return null;
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
            const {LeanCaret, LeanArgsCommaSeparated} = Lean.classes;
            let $new = new LeanCaret(this.indent, caret.level);
            const commaSep = new LeanArgsCommaSeparated([caret, $new], this.indent, $new.level);
            this.args[1] = commaSep;
            commaSep.parent = this;
            return $new;
        }

        push_token(word) {
            const {LeanToken, LeanArgsSpaceSeparated} = Lean.classes;
            const level = this.level;
            const newTok = new LeanToken(word, this.indent, level);
            this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
            return newTok;
        }

        /** `Measurable[m] fun ω => …` — like `LeanToken.append`: the `fun`/`match` is the next argument. */
        append($new, $func) {
            if (typeof $new === 'string' && ($func === 'expr' || $func === 'operator')) {
                const {LeanCaret, LeanArgsSpaceSeparated} = Lean.classes;
                const Ctor = Lean.classes[$new];
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
            const {LeanProperty} = Lean.classes;
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
            const {LeanProperty, LeanToken} = Lean.classes;
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

/** @param {import('../../../js/parser/lean.js').Lean} node */
export function strStmt(node) {
    return String(node).replace(/\n$/, '');
}

export class ParserPrefixExpr {
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

export function leanEvalPrefix(expressions, operandCount) {
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
export function leanVarsGetitem(root, keys) {
    let cur = root;
    for (const k of keys) {
        if (k === '' || k == null) return undefined;
        if (cur == null || typeof cur !== 'object') return undefined;
        cur = cur[k];
    }
    return cur;
}
