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
import { createAtomicFamily } from './lean/atomic.js';
import { createAbstractFamily } from './lean/abstract.js';
import { createRangeFamily } from './lean/range.js';
import { createPropertyFamily } from './lean/property.js';
import { createColonFamily } from './lean/colon.js';
import { createAssignFamily } from './lean/assign.js';
import { createBooleanFamily } from './lean/boolean.js';
import { createLazyFamily } from './lean/lazy.js';
import { createPipelineFamily } from './lean/pipeline.js';
import { createIsInstanceFamily } from './lean/isinstance.js';
import { createStatementsFamily } from './lean/statements.js';
import { createModuleFamily } from './lean/module.js';
import { createCommandFamily } from './lean/command.js';

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

const abstractLate = {};
const abstractFamily = createAbstractFamily({
    Lean,
    token2classname,
    leanSubtreeContains,
    abstractLate,
});
export const LeanArgs = abstractFamily.LeanArgs;
export const LeanUnary = abstractFamily.LeanUnary;
export const LeanBinary = abstractFamily.LeanBinary;

const atomicLate = {};
const atomicFamily = createAtomicFamily({
    Lean,
    LeanBinary,
    escapeSpecialsForLatex,
    classRegistry: arithmeticClassRegistry,
    atomicLate,
});
export const LeanCaret = atomicFamily.LeanCaret;
export const LeanToken = atomicFamily.LeanToken;
export const LeanLineComment = atomicFamily.LeanLineComment;
const LeanBlockComment = atomicFamily.LeanBlockComment;
const LeanDocString = atomicFamily.LeanDocString;

const rangeFamily = createRangeFamily({
    LeanBinary,
    LeanCaret,
});
export const LeanUpto = rangeFamily.LeanUpto;
const propertyLate = {};
const propertyFamily = createPropertyFamily({
    LeanBinary,
    LeanCaret,
    LeanToken,
    classRegistry: arithmeticClassRegistry,
    propertyLate,
});
export const LeanProperty = propertyFamily.LeanProperty;

const colonLate = {};
const colonFamily = createColonFamily({
    LeanBinary,
    LeanCaret,
    LeanToken,
    LeanProperty,
    leanIsInfixContinue,
    classRegistry: arithmeticClassRegistry,
    colonLate,
});
export const LeanColon = colonFamily.LeanColon;

const assignLate = {};
const assignFamily = createAssignFamily({
    LeanBinary,
    LeanCaret,
    LeanLineComment,
    classRegistry: arithmeticClassRegistry,
    assignLate,
});
export const LeanAssign = assignFamily.LeanAssign;

const booleanLate = {};
const booleanFamily = createBooleanFamily({
    LeanBinary,
    LeanProp,
    LeanCaret,
    LeanColon,
    classRegistry: arithmeticClassRegistry,
    booleanLate,
});
export const LeanBinaryBoolean = booleanFamily.LeanBinaryBoolean;

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

const lazyFamily = createLazyFamily({
    LeanBinary,
});
export const Lean_lazy = lazyFamily.Lean_lazy;

const pipelineFamily = createPipelineFamily({
    LeanBinary,
});
export const LeanMethodChaining = pipelineFamily.LeanMethodChaining;

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

const isinstanceLate = {};
const isinstanceFamily = createIsInstanceFamily({
    LeanBinary,
    isinstanceLate,
});
export const Lean_is = isinstanceFamily.Lean_is;
export const Lean_is_not = isinstanceFamily.Lean_is_not;

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


const statementsLate = {};
const statementsFamily = createStatementsFamily({
    LeanMultipleLine,
    LeanArgs,
    LeanColon,
    LeanCaret,
    LeanLineComment,
    LeanBlockComment,
    LeanAssign,
    LeanRelational,
    LeanBinary,
    LeanToken,
    leanIsInfixContinue,
    statementsLate,
});
export const LeanStatements = statementsFamily.LeanStatements;

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function strStmt(node) {
    return String(node).replace(/\n$/, '');
}

const moduleLate = {};
const moduleFamily = createModuleFamily({
    LeanStatements,
    LeanAssign,
    LeanBlockComment,
    LeanCaret,
    LeanColon,
    LeanLineComment,
    LeanProperty,
    LeanToken,
    Lean_land,
    strStmt,
    classRegistry: arithmeticClassRegistry,
    moduleLate,
});
export const LeanModule = moduleFamily.LeanModule;

const commandLate = {};
const commandFamily = createCommandFamily({
    LeanUnary,
    LeanCaret,
    LeanProperty,
    LeanToken,
    classRegistry: arithmeticClassRegistry,
    commandLate,
});
const LeanCommand = commandFamily.LeanCommand;
const Lean_import = commandFamily.Lean_import;
const Lean_open = commandFamily.Lean_open;
const Lean_set_option = commandFamily.Lean_set_option;
const Lean_namespace = commandFamily.Lean_namespace;

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
 * Extra binary operators from `token2classname`. Defined in `./lean/atomic.js`.
 * Re-exported here so `constructor.name` and declaration order stay put.
 */
export const Lean_ominus = atomicFamily.Lean_ominus;
export const Lean_oslash = atomicFamily.Lean_oslash;
export const Lean_circledcirc = atomicFamily.Lean_circledcirc;
export const Lean_circledast = atomicFamily.Lean_circledast;
export const Lean_circleeq = atomicFamily.Lean_circleeq;
export const Lean_circleddash = atomicFamily.Lean_circleddash;
export const Lean_boxplus = atomicFamily.Lean_boxplus;
export const Lean_boxminus = atomicFamily.Lean_boxminus;
export const Lean_boxtimes = atomicFamily.Lean_boxtimes;
export const Lean_dotsquare = atomicFamily.Lean_dotsquare;
export const LeanEDiv = atomicFamily.LeanEDiv;

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
Object.assign(atomicLate, {
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanAssign,
    LeanBy,
    LeanColon,
    LeanStatements,
    LeanTactic,
    Lean_lemma,
});
Object.assign(propertyLate, {
    LeanArgsCommaNewLineSeparated,
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanColon,
    LeanIte,
    LeanParenthesis,
    LeanStatements,
    LeanTactic,
});
Object.assign(colonLate, {
    LeanArgsCommaSeparated,
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanBrace,
    LeanBracket,
    LeanGetElem,
    LeanParenthesis,
    LeanStatements,
    Lean_let,
});
Object.assign(assignLate, {
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanBrace,
    LeanBy,
    LeanCalc,
    LeanStatements,
    Lean_blacktriangleright,
});
Object.assign(booleanLate, {
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanStatements,
});
Object.assign(isinstanceLate, {
    LeanStatements,
});
Object.assign(statementsLate, {
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanBitOr,
    LeanBrace,
    LeanBy,
    LeanCalc,
    LeanFrom,
    LeanIte,
    LeanStack,
    LeanTactic,
    LeanTacticBlock,
    Lean_lemma,
    Lean_mapsto,
    Lean_match,
    Lean_rightarrow,
});
Object.assign(moduleLate, {
    LeanAngleBracket,
    LeanArgsCommaSeparated,
    LeanArgsNewLineSeparated,
    LeanArgsSpaceSeparated,
    LeanBrace,
    LeanBracket,
    LeanBy,
    LeanCalc,
    LeanParenthesis,
    LeanSequentialTacticCombinator,
    LeanTactic,
    LeanTacticBlock,
    Lean_def,
    Lean_fun,
    Lean_import,
    Lean_lemma,
    Lean_let,
    Lean_match,
    Lean_open,
    Lean_rightarrow,
    Lean_set_option,
});
Object.assign(commandLate, {
    LeanArgsSpaceSeparated,
});
Object.assign(abstractLate, {
    LeanArgsIndented,
    LeanArgsNewLineSeparated,
    LeanCalc,
    LeanCaret,
    LeanColon,
    LeanIte,
    LeanMethodChaining,
    LeanParenthesis,
    LeanProperty,
    LeanStatements,
    LeanTactic,
    LeanToken,
    Lean_rightarrow,
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
