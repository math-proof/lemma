import '../std.js';
import { AbstractParser } from './node.js';
import { isIdentContinueToken } from './lean/utility.js';

// Each family module registers its classes in `Lean.classes` (`static { this.register(); }`)
// when it is evaluated, so every module is imported here even when nothing is re-exported.
import { Lean } from './lean/base.js';
import './lean/abstract.js';
import './lean/atomic.js';
import './lean/range.js';
import './lean/property.js';
import './lean/colon.js';
import './lean/assign.js';
import './lean/boolean.js';
import './lean/relational.js';
import './lean/membership.js';
import './lean/lazy.js';
import './lean/pipeline.js';
import './lean/indexing.js';
import './lean/isinstance.js';
import './lean/logic.js';
import './lean/set.js';
import './lean/statements.js';
import './lean/module.js';
import './lean/command.js';
import './lean/bar.js';
import './lean/arrows.js';
import './lean/negation.js';
import './lean/match.js';
import './lean/ite.js';
import './lean/args.js';
import './lean/tactic.js';
import './lean/decl.js';
import './lean/fun.js';
import './lean/bigops.js';
import './lean/quantifier.js';
import './lean/paired.js';
import './lean/arithmetic.js';

const L = Lean.classes;

export {
    token2classname,
    leanInfixContinue,
    LeanMultipleLine,
    LeanProp,
    LeanGetElemBase,
    LeanGetElemBaseBinary,
} from './lean/utility.js';
export { Lean } from './lean/base.js';
export { LeanArgs, LeanUnary, LeanBinary } from './lean/abstract.js';
export { LeanCaret, LeanToken, LeanLineComment } from './lean/atomic.js';
/**
 * Extra binary operators from `token2classname`. Defined in `./lean/atomic.js`.
 * Re-exported here so `constructor.name` and declaration order stay put.
 */
export {
    Lean_ominus,
    Lean_oslash,
    Lean_circledcirc,
    Lean_circledast,
    Lean_circleeq,
    Lean_circleddash,
    Lean_boxplus,
    Lean_boxminus,
    Lean_boxtimes,
    Lean_dotsquare,
    LeanEDiv,
} from './lean/atomic.js';
export { LeanUpto } from './lean/range.js';
export { LeanProperty } from './lean/property.js';
export { LeanColon } from './lean/colon.js';
export { LeanAssign } from './lean/assign.js';
export { LeanBinaryBoolean } from './lean/boolean.js';
export {
    LeanRelational,
    Lean_gt,
    Lean_ge,
    Lean_lt,
    Lean_le,
    LeanEq,
    Lean_perp,
    LeanBEq,
    Lean_bne,
    Lean_ne,
    Lean_equiv,
    LeanNotEquiv,
    Lean_simeq,
    Lean_approx,
    Lean_asymp,
    LeanDvd,
    Lean_ll,
    Lean_gg,
} from './lean/relational.js';
export { Lean_in, Lean_notin, Lean_leftrightarrow } from './lean/membership.js';
export { Lean_lazy } from './lean/lazy.js';
export { LeanMethodChaining } from './lean/pipeline.js';
export {
    LeanGetElem,
    LeanGetWhiteSquareBracket,
    LeanGetElemQue,
    LeanGetElemQuote,
} from './lean/indexing.js';
export { Lean_is, Lean_is_not } from './lean/isinstance.js';
export {
    LeanLogic,
    LeanLogicAnd,
    LeanLogicOr,
    LeanLogicXor,
    Lean_lor,
    Lean_land,
} from './lean/logic.js';
export {
    LeanSetOperator,
    Lean_setminus,
    Lean_cup,
    Lean_cap,
    Lean_subseteq,
    Lean_subset,
    Lean_supseteq,
    Lean_supset,
} from './lean/set.js';
export { LeanStatements } from './lean/statements.js';
export { LeanModule } from './lean/module.js';
export { LeanRightarrow, Lean_rightarrow, Lean_mapsto } from './lean/arrows.js';
export { LeanIte } from './lean/ite.js';
export {
    LeanArgsSpaceSeparated,
    LeanArgsNewLineSeparated,
    LeanArgsIndented,
    LeanArgsCommaSeparated,
    LeanArgsSemicolonSeparated,
    LeanArgsCommaNewLineSeparated,
} from './lean/args.js';
export {
    LeanSyntax,
    LeanTactic,
    LeanBy,
    LeanAt,
    LeanSequentialTacticCombinator,
} from './lean/tactic.js';
export {
    Lean_def,
    Lean_theorem,
    Lean_abbrev,
    Lean_class,
    Lean_instance,
    Lean_macro,
    Lean_syntax,
    Lean_lemma,
} from './lean/decl.js';
export { LeanParenthesis } from './lean/paired.js';
export {
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
} from './lean/arithmetic.js';

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
        const caret = new L.LeanCaret(0, 0);
        this.caret = caret;
        this.root = new L.LeanModule([caret], 0, 0);
    }

    parseKeywordAsPropertyField(caret, token) {
        if (caret instanceof L.LeanCaret && caret.parent instanceof L.LeanProperty) {
            let word = token;
            while (isIdentContinueToken(this.tokens[this.start_idx + 1])) {
                this.start_idx++;
                word += this.tokens[this.start_idx];
            }
            return caret.parent.insert_word(caret, word);
        }
    }
}

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
    if (!(ast instanceof L.LeanModule)) return null;

    const imports = [];
    let namespace = '';
    for (const node of ast.args) {
        if (!node) continue;
        if (node instanceof L.Lean_import) {
            imports.push(String(node).replace(/^import\s+/, '').trim());
        } else if (node instanceof L.Lean_namespace) {
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
