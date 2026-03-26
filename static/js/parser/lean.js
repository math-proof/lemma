import '../utility.js';
import { IndentedNode, AbstractParser } from './node.js';
import { tactics } from '../../codemirror/mode/lean/tactics.js';

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
    '∈': 'Lean_in',
    '∉': 'Lean_notin',
    '|': 'LeanBitOr',
    '&': 'LeanBitAnd',
    '||': 'LeanLogicOr',
    '|||': 'LeanBitwiseOr',
    '&&': 'LeanLogicAnd',
    '&&&': 'LeanBitwiseAnd',
    '^': 'LeanPow',
    '^^': 'LeanLogicXor',
    '^^^': 'LeanBitwiseXor',
    '<': 'Lean_lt',
    '<<': 'Lean_ll',
    '<<<': 'Lean_lll',
    '<=': 'Lean_le',
    '>': 'Lean_gt',
    '>>': 'Lean_gg',
    '>>>': 'Lean_ggg',
    '>=': 'Lean_ge',
    '∨': 'Lean_lor',
    '∧': 'Lean_land',
    '∪': 'Lean_cup',
    '∩': 'Lean_cap',
    '\\': 'Lean_setminus',
    '|>.': 'LeanMethodChaining',
    '⊆': 'Lean_subseteq',
    '⊂': 'Lean_subset',
    '⊇': 'Lean_supseteq',
    '⊃': 'Lean_supset',
    '⊔': 'Lean_sqcup',
    '⊓': 'Lean_sqcap',
    '++': 'LeanAppend',
    '::': 'LeanConstruct',
    '::ᵥ': 'LeanVConstruct',
    '→': 'Lean_rightarrow',
    '↦': 'Lean_mapsto',
    '↔': 'Lean_leftrightarrow',
    '≠': 'Lean_ne',
    '≡': 'Lean_equiv',
    '≢': 'LeanNotEquiv',
    '≍': 'Lean_asymp',
    '≃': 'Lean_simeq',
    '≈': 'Lean_approx',
    '∣': 'LeanDvd',
});

/** Lean identifier continuation token (supports Unicode letters like Ξ). */
function isIdentContinueToken(s) {
    return /^[\p{L}\p{N}_'!?₀-₉]+$/u.test(s);
}

/**
 * Port of PHP `abstract class Lean`; method order follows `lean.php` (`__construct` → `__get` → `__set` → … → `append`).
 * See `scripts/reorder_lean_class.py` preset `lean`.
 */
export class Lean extends IndentedNode {
    constructor(indent, level, parent = null) {
        super(indent, parent);
        this.level = level;
    }

    clone() {
        const copy = Object.create(Object.getPrototypeOf(this));
        Object.assign(copy, this);
        copy.parent = null;
        return copy;
    }

    get root() {
        return this.parent ? this.parent.root : null;
    }

    get line() {
        return this.kwargs.line;
    }

    set line(v) {
        this.kwargs.line = v;
    }

    get stack_priority() {
        const c = /** @type {{ input_priority?: number }} */ (this.constructor);
        return typeof c.input_priority === 'number' ? c.input_priority : 100;
    }

    get level() {
        return this.kwargs.level ?? 0;
    }

    set level(v) {
        this.kwargs.level = v;
    }

    toString() {
        const inner = leanPhpToStringBody(this);
        return (this.is_indented() ? ' '.repeat(this.indent) : '') + inner;
    }

    append(_new, _type) {
        if (this.parent) return this.parent.append(this, _new, _type);
    }

    case_default() {
        return this;
    }

    echo() {}

    getEcho() {}

    insert(caret, func, type) {
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_assign(caret) {
        return caret.push_binary('LeanAssign');
    }

    insert_bar(caret, prevToken, next) {
        switch (next) {
            case ' ':
                if (prevToken === ' ') return caret.push_arithmetic('|');
                return this.push_right('LeanAbs');
            case ')':
                return this.push_right('LeanAbs');
            default:
                if (!next) return this.push_right('LeanAbs');
                return this.insert_unary(caret, 'LeanAbs');
        }
    }

    insert_calc(caret) {
        if (this.parent) return this.parent.insert_calc(this);
    }

    insert_colon(caret) {
        return caret.push_binary('LeanColon');
    }

    insert_comma(caret) {
        if (this.parent) return this.parent.insert_comma(this);
    }

    insert_construct(caret) {
        return caret.push_binary('LeanConstruct');
    }

    insert_else(caret) {
        if (this.parent) return this.parent.insert_else(this);
    }

    insert_end(caret) {
        if (this.parent) return this.parent.insert_end(this);
    }

    insert_if(caret) {
        if (this.parent) return this.parent.insert_if(caret);
    }

    insert_left(caret, func, prevToken = '') {
        return caret.push_left(func, prevToken);
    }

    insert_line_comment(caret, comment) {
        return caret.push_line_comment(comment);
    }

    insert_newline(_caret, newlineCount, indent, next) {
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
        throw new Error('insert_newline: no parent');
    }

    insert_only(caret) {
        if (this.parent) return this.parent.insert_only(this);
    }

    insert_semicolon(caret) {
        if (this.parent) return this.parent.insert_semicolon(this);
    }

    insert_sequential_tactic_combinator(caret, nextToken) {
        if (this.parent) return this.parent.insert_sequential_tactic_combinator(this, nextToken);
    }

    insert_space(caret) {
        return caret;
    }

    insert_tactic(caret, token) {
        if (this.parent) return this.parent.insert_tactic(this, token);
    }

    insert_then(caret) {
        if (this.parent) return this.parent.insert_then(this);
    }

    insert_unary(self, funcName) {
        const parent = self.parent;
        const Ctor = getLeanClass(funcName);
        let caret;
        let replacement;
        if (self instanceof LeanCaret) {
            caret = self;
            replacement = new Ctor(caret, self.indent, self.level);
        } else {
            caret = new LeanCaret(self.indent, self.level);
            replacement = new Ctor(caret, self.indent, self.level);
            replacement = new LeanArgsSpaceSeparated([self, replacement], self.indent, self.level);
        }
        parent.replace(self, replacement);
        return caret;
    }

    insert_vconstruct(caret) {
        return caret.push_binary('LeanVConstruct');
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    is_comment() {
        return false;
    }

    is_indented() {
        const p = this.parent;
        return (
            p instanceof LeanArgsCommaNewLineSeparated ||
            p instanceof LeanArgsNewLineSeparated ||
            p instanceof LeanStatements ||
            (p instanceof LeanIte && (this === p.then || this === p.else))
        );
    }

    is_outsider() {
        return false;
    }

    isProp(_vars) {
        return false;
    }

    is_space_separated() {
        return false;
    }

    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join(' ');
    }

    latexArgs(syntax) {
        return this.args.map((a) => a.toLatex(syntax));
    }

    latexFormat() {
        return this.strFormat();
    }

    parse(token, parser) {
        const self = parser;
        const tokens = self.tokens;
        const count = tokens.length;

        switch (token) {
            case 'import':
            case 'open':
            case 'namespace':
            case 'def':
            case 'theorem':
            case 'lemma':
            case 'set_option':
                return this.append(`Lean_${token}`, 'delspec');
            case 'fun':
            case 'match':
                return this.append(`Lean_${token}`, 'expr');
            case 'have':
            case 'let':
            case 'show':
                return this.append(`Lean_${token}`, 'tactic');
            case 'public':
            case 'private':
            case 'protected':
                while (tokens[++self.start_idx] === ' ');
                if (tokens[self.start_idx] === 'nonrec') {
                    self.start_idx++;
                    while (tokens[++self.start_idx] === ' ');
                }
                return this.push_accessibility(`Lean_${tokens[self.start_idx]}`, token);
            case 'scoped':
            case 'noncomputable':
            case 'nonrec':
                while (tokens[++self.start_idx] === ' ');
                return this.push_accessibility(`Lean_${tokens[self.start_idx]}`, token);
            case ' ':
                return this.parent.insert_space(this);
            case '\t':
                throw new Error('Tab is not allowed in Lean');
            case '\r':
                console.warn('Carriage return is not allowed in Lean');
                break;
            case '\n': {
                let j = 0;
                let newlineCount = 1;
                let indent = 0;
                while (true) {
                    indent = 0;
                    while (tokens[self.start_idx + ++j] === ' ') ++indent;
                    if (tokens[self.start_idx + j] !== '\n') break;
                    ++newlineCount;
                }
                let k = j;
                while (
                    self.start_idx + k + 1 < count &&
                    tokens[self.start_idx + k] === '-' &&
                    tokens[self.start_idx + k + 1] === '-'
                ) {
                    while (tokens[self.start_idx + ++k] !== '\n');
                    while (tokens[self.start_idx + k] === '\n') {
                        indent = 0;
                        while (tokens[self.start_idx + ++k] === ' ') ++indent;
                    }
                }
                if (indent === 0 && tokens[self.start_idx + k] === 'end') newlineCount -= 1;
                const nextCaret = this.parent.insert_newline(this, newlineCount, indent, tokens[self.start_idx + k]);
                self.start_idx += j - 1;
                return nextCaret ?? this;
            }
            case '.':
                if (
                    this instanceof LeanCaret &&
                    (this.parent instanceof LeanStatements || this.parent instanceof LeanSequentialTacticCombinator)
                )
                    return this.parent.insert_unary(this, 'LeanTacticBlock');
                return this.push_binary('LeanProperty');
            case 'is': {
                if (this instanceof LeanCaret && this.parent instanceof LeanProperty)
                    return this.parent.insert_word(this, token);
                // In import/open/set_option/def etc., "is" is a plain identifier (e.g. Setoid.is.All_SetoidGetS)
                let p = this;
                while (p && p.parent) {
                    const name = p.parent.constructor?.name || '';
                    if (/^Lean_(import|open|set_option|namespace|def|theorem|lemma)$/.test(name))
                        return this.parent.insert_word(this, token);
                    p = p.parent;
                }
                let func = `Lean_${token}`;
                const sp = tokens[self.start_idx + 1];
                const not =
                    self.start_idx + 2 < count &&
                    typeof sp === 'string' &&
                    sp.isspace() &&
                    tokens[self.start_idx + 2].toLowerCase() === 'not';
                if (not) {
                    self.start_idx += 2;
                    func += '_not';
                    self.start_idx = self.start_idx;
                }
                return this.push_binary(func);
            }
            case '(':
                return this.parent.insert_left(this, 'LeanParenthesis');
            case ')':
                return this.parent.push_right('LeanParenthesis');
            case '[':
                return this.parent.insert_left(this, 'LeanBracket', self.start_idx ? tokens[self.start_idx - 1] : '');
            case ']':
                return this.parent.push_right('LeanBracket');
            case '{':
                return this.parent.insert_left(this, 'LeanBrace');
            case '}':
                return this.parent.push_right('LeanBrace');
            case '⟨':
                return this.parent.insert_left(this, 'LeanAngleBracket');
            case '⟩':
                return this.parent.push_right('LeanAngleBracket');
            case '⌈':
                return this.parent.insert_left(this, 'LeanCeil');
            case '⌉':
                return this.parent.push_right('LeanCeil');
            case '⌊':
                return this.parent.insert_left(this, 'LeanFloor');
            case '⌋':
                return this.parent.push_right('LeanFloor');
            case '«':
                return this.parent.insert_left(this, 'LeanDoubleAngleQuotation');
            case '»':
                return this.parent.push_right('LeanDoubleAngleQuotation');
            case '?':
                if (this instanceof LeanGetElem) {
                    const parent = this.parent;
                    const [lhs, rhs] = this.args;
                    const newNode = new LeanGetElemQue(lhs, rhs, this.indent, this.level);
                    parent.replace(this, newNode);
                    return newNode;
                }
                if (tokens[self.start_idx + 1] === '_') {
                    self.start_idx++;
                    token += '_';
                }
                return this.parent.insert_word(this, token);
            case '<':
                if (tokens[self.start_idx + 1] === '=') {
                    self.start_idx++;
                    return this.push_binary('Lean_le');
                }
                if (self.start_idx + 2 < count && tokens[self.start_idx + 1] === ';' && tokens[self.start_idx + 2] === '>') {
                    self.start_idx += 2;
                    self.start_idx = self.start_idx;
                    return this.parent.insert_sequential_tactic_combinator(this, tokens[self.start_idx + 1]);
                }
                if (tokens[self.start_idx + 1] === '<') {
                    self.start_idx++;
                    token += '<';
                    if (tokens[self.start_idx + 1] === '<') {
                        self.start_idx++;
                        token += '<';
                    }
                }
                return this.push_arithmetic(token);
            case '>':
                if (tokens[self.start_idx + 1] === '=') {
                    self.start_idx++;
                    token += '=';
                } else if (tokens[self.start_idx + 1] === '>') {
                    self.start_idx++;
                    token += '>';
                    if (tokens[self.start_idx + 1] === '>') {
                        self.start_idx++;
                        token += '>';
                    }
                }
                return this.push_arithmetic(token);
            case '≤':
                return this.push_binary('Lean_le');
            case '≥':
                return this.push_binary('Lean_ge');
            case '=':
                if (tokens[self.start_idx + 1] === '>') {
                    self.start_idx++;
                    if (this.parent instanceof LeanAt && this.parent.parent instanceof LeanTactic) {
                        const newCaret = new LeanCaret(this.indent, this.level);
                        this.parent.parent.push(newCaret);
                        return newCaret.push_binary('LeanRightarrow');
                    }
                    return this.push_binary('LeanRightarrow');
                }
                if (tokens[self.start_idx + 1] === '=') {
                    self.start_idx++;
                    return this.push_binary('LeanBEq');
                }
                return this.push_binary('LeanEq');
            case '!':
                if (tokens[self.start_idx + 1] === '=') {
                    self.start_idx++;
                    return this.push_binary('Lean_ne');
                }
                return this.parent.insert_unary(this, 'LeanNot');
            case ',':
                return this.parent.insert_comma(this);
            case ':':
                if (tokens[self.start_idx + 1] === '=') {
                    self.start_idx++;
                    return this.parent.insert_assign(this);
                }
                if (tokens[self.start_idx + 1] === ':') {
                    self.start_idx++;
                    if (tokens[self.start_idx + 1] === 'ᵥ') {
                        self.start_idx++;
                        return this.parent.insert_vconstruct(this);
                    }
                    return this.parent.insert_construct(this);
                }
                return this.parent.insert_colon(this);
            case ';':
                return this.parent.insert_semicolon(this);
            case '-':
                if (tokens[self.start_idx + 1] === '-') {
                    self.start_idx++;
                    let comment = '';
                    while (self.start_idx + 1 < count && tokens[++self.start_idx] !== '\n')
                        comment += tokens[self.start_idx];
                    self.start_idx--;
                    return this.parent.insert_line_comment(this, comment.trim());
                }
                if (this instanceof LeanCaret) return this.parent.insert_unary(this, 'LeanNeg');
                return this.push_arithmetic(token);
            case '*':
                if (this instanceof LeanCaret) return this.parent.insert_word(this, token);
                if (this instanceof LeanToken && this.is_TypeStar() && (!self.start_idx || tokens[self.start_idx - 1] !== ' ')) {
                    this.text += '*';
                    return this;
                }
                return this.push_arithmetic(token);
            case '|': {
                const next = tokens[self.start_idx + 1];
                if (next === '|') {
                    self.start_idx++;
                    if (tokens[self.start_idx + 1] === '|') {
                        self.start_idx++;
                        return this.push_binary('LeanBitwiseOr');
                    }
                    return this.push_binary('LeanLogicOr');
                }
                if (next === '>') {
                    self.start_idx++;
                    if (tokens[self.start_idx + 1] === '.') {
                        self.start_idx++;
                        return this.push_arithmetic('|>.');
                    }
                    return this.push_post_unary('LeanPipeForward');
                }
                return this.parent.insert_bar(this, self.start_idx ? tokens[self.start_idx - 1] : '', next);
            }
            case '&':
                if (tokens[self.start_idx + 1] === '&') {
                    self.start_idx++;
                    token += '&';
                    if (tokens[self.start_idx + 1] === '&') {
                        self.start_idx++;
                        token += '&';
                    }
                }
                return this.push_arithmetic(token);
            case "'":
                if (this instanceof LeanGetElem && tokens[self.start_idx - 1] === ']') {
                    const [lhs, rhs] = this.args;
                    const caret = new LeanCaret(this.indent, this.level);
                    this.parent.replace(this, new LeanGetElemQuote([lhs, rhs, caret], this.indent, this.level));
                    return caret;
                }
                while (isIdentContinueToken(tokens[self.start_idx + 1])) {
                    self.start_idx++;
                    token += tokens[self.start_idx];
                }
                return this.push_quote(token);
            case '+':
                if (this instanceof LeanCaret) return this.parent.insert_unary(this, 'LeanPlus');
                if (tokens[self.start_idx + 1] === '+') {
                    self.start_idx++;
                    token += '+';
                }
                return this.push_arithmetic(token);
            case '^':
                if (tokens[self.start_idx + 1] === '^') {
                    self.start_idx++;
                    token += '^';
                    if (tokens[self.start_idx + 1] === '^') {
                        self.start_idx++;
                        token += '^';
                    }
                }
                return this.push_arithmetic(token);
            case '/':
                if (tokens[self.start_idx + 1] === '-') {
                    self.start_idx++;
                    let docstring = false;
                    if (tokens[self.start_idx + 1] === '-') {
                        docstring = true;
                        self.start_idx++;
                    }
                    let comment = '';
                    while (true) {
                        self.start_idx++;
                        if (tokens[self.start_idx] === '-' && tokens[self.start_idx + 1] === '/') {
                            self.start_idx++;
                            break;
                        }
                        comment += tokens[self.start_idx];
                    }
                    comment = comment.replace(/(?<=\n) +$/g, '');
                    comment = comment.replace(/^\n+|\n+$/g, '');
                    if (tokens[self.start_idx + 1] === '\n') self.start_idx++;
                    return this.push_block_comment(comment, docstring);
                }
                if (tokens[self.start_idx + 1] === '/') {
                    self.start_idx++;
                    return this.push_arithmetic('//');
                }
                // fallthrough: bare '/' uses same rule as '%'
            case '%':
            case '×':
            case '⬝':
            case '∘':
            case '•':
            case '⊙':
            case '⊗':
            case '⊕':
            case '⊖':
            case '⊘':
            case '⊚':
            case '⊛':
            case '⊜':
            case '⊝':
            case '⊞':
            case '⊟':
            case '⊠':
            case '⊡':
            case '∈':
            case '∉':
            case '▸':
            case '∪':
            case '∩':
            case '⊔':
            case '⊓':
            case '\\':
            case '⊆':
            case '⊇':
            case '⊂':
            case '⊃':
            case '→':
            case '↦':
            case '↔':
            case '∧':
            case '∨':
            case '≠':
            case '≡':
            case '≢':
            case '≃':
            case '≍':
            case '≈':
            case '∣':
                return this.push_arithmetic(token);
            case '←':
                return this.parent.insert_unary(this, 'Lean_leftarrow');
            case '∀':
                return this.append('Lean_forall', 'operator');
            case '∃':
                return this.append('Lean_exists', 'operator');
            case '∑':
                return this.append('Lean_sum', 'operator');
            case '∏':
                return this.append('Lean_prod', 'operator');
            case '⋃':
                return this.append('Lean_bigcup', 'operator');
            case '⋂':
                return this.append('Lean_bigcap', 'operator');
            case '¬':
                return this.parent.insert_unary(this, 'Lean_lnot');
            case '√':
                return this.parent.insert_unary(this, 'Lean_sqrt');
            case '∛':
                return this.parent.insert_unary(this, 'LeanCubicRoot');
            case '∜':
                return this.parent.insert_unary(this, 'LeanQuarticRoot');
            case '↑':
                return this.parent.insert_unary(this, 'Lean_uparrow');
            case '²':
                return this.push_post_unary('LeanSquare');
            case '³':
                return this.push_post_unary('LeanCube');
            case '⁴':
                return this.push_post_unary('LeanTesseract');
            case 'ᵀ':
                return this.push_post_unary('LeanTranspose');
            case '⁺':
                return this.push_post_unary('LeanPosPart');
            case '⁻':
                if (tokens[self.start_idx + 1] === '¹') {
                    self.start_idx++;
                    return this.push_post_unary('LeanInv');
                }
                return this.push_post_unary('LeanNegPart');
            case 'by':
            case 'using':
            case 'at':
            case 'with':
            case 'in':
            case 'generalizing':
            case 'MOD':
            case 'from':
                if (this instanceof LeanCaret && this.parent instanceof LeanProperty) {
                    while (isIdentContinueToken(tokens[self.start_idx + 1])) {
                        self.start_idx++;
                        token += tokens[self.start_idx];
                    }
                    return this.parent.insert_word(this, token);
                }
                return this.parent.insert(this, `Lean${token[0].toUpperCase() + token.slice(1)}`, 'modifier');
            case 'calc':
                if (this instanceof LeanCaret && this.parent instanceof LeanProperty) {
                    while (isIdentContinueToken(tokens[self.start_idx + 1])) {
                        self.start_idx++;
                        token += tokens[self.start_idx];
                    }
                    return this.parent.insert_word(this, token);
                }
                return this.parent.insert_calc(this);
            case '·':
                if (this.parent instanceof LeanStatements || this.parent instanceof LeanSequentialTacticCombinator)
                    return this.parent.insert_unary(this, 'LeanTacticBlock');
                return this.parent.insert_word(this, token);
            case '@':
                if (this instanceof LeanCaret) return this.parent.insert_unary(this, 'LeanAttribute');
                return this.push_binary('LeanMatMul');
            case 'end':
                return this.parent.insert_end(this);
            case 'only':
                return this.parent.insert_only(this);
            case 'if':
                return this.parent.insert_if(this);
            case 'then':
                return this.parent.insert_then(this);
            case 'else':
                return this.parent.insert_else(this);
            case '‖':
                if (this instanceof LeanCaret || (self.start_idx && tokens[self.start_idx - 1] === ' '))
                    return this.parent.insert_left(this, 'LeanNorm');
                return this.parent.push_right('LeanNorm');
            default: {
                const tokenOrig = token;
                const index = tactics.binary_search(tokenOrig, (a, b) =>
                    a < b ? -1 : a > b ? 1 : 0
                );
                while (isIdentContinueToken(tokens[self.start_idx + 1])) {
                    self.start_idx++;
                    token += tokens[self.start_idx];
                }
                if (index < tactics.length && tactics[index] === tokenOrig)
                    return this.parent.insert_tactic(this, token);
                return this.parent.insert_word(this, token);
            }
        }
        return this;
    }

    push_accessibility(_new, _accessibility) {
        if (this.parent) return this.parent.push_accessibility(_new, _accessibility);
    }

    push_arithmetic(token) {
        const cls = token2classname[token];
        if (!cls) throw new Error(`push_arithmetic: unknown token ${JSON.stringify(token)}`);
        return this.push_binary(cls);
    }

    push_attr(_caret) {
        throw new Error('push_attr is unexpected for ' + this.constructor.name);
    }

    push_binary(funcName) {
        const parent = this.parent;
        if (!parent) return undefined;
        const Ctor = getLeanClass(funcName);
        if (Ctor.input_priority > parent.stack_priority) {
            const level = this.level;
            const caret = new LeanCaret(this.indent, level);
            parent.replace(this, new Ctor(this, caret, this.indent, level));
            return caret;
        }
        return parent.push_binary(funcName);
    }

    push_block_comment(comment, docstring) {
        throw new Error(`push_block_comment is unexpected for ${this.constructor.name}`);
    }

    push_left(func, prevToken) {
        switch (func) {
            case 'LeanParenthesis':
            case 'LeanBracket':
            case 'LeanBrace':
            case 'LeanAngleBracket':
            case 'LeanFloor':
            case 'LeanCeil':
            case 'LeanNorm':
            case 'LeanDoubleAngleQuotation': {
                const indent = this.indent;
                const level = this.level;
                const caret = new LeanCaret(indent, level);
                if (func === 'LeanBracket') {
                    if (prevToken === ' ') {
                        let self = this;
                        let par = self.parent;
                        while (par) {
                            if (par instanceof Lean_equiv || par instanceof LeanNotEquiv) {
                                const newNode = new (getLeanClass(func))(caret, indent, level);
                                par.replace(self, new LeanArgsSpaceSeparated([self, newNode], indent, level));
                                return caret;
                            }
                            self = par;
                            par = par.parent;
                        }
                    } else if (
                        this instanceof LeanToken ||
                        this instanceof LeanProperty ||
                        this instanceof LeanGetElem ||
                        this instanceof LeanGetElemQue ||
                        this instanceof LeanGetElemQuote ||
                        this instanceof LeanUnaryArithmeticPost ||
                        (this instanceof LeanPairedGroup && this.is_Expr())
                    ) {
                        this.parent.replace(this, new LeanGetElem(this, caret, indent, level));
                        return caret;
                    }
                }
                const paired = new (getLeanClass(func))(caret, indent, level);
                if (this.parent instanceof LeanArgsSpaceSeparated) this.parent.push(paired);
                else this.parent.replace(this, new LeanArgsSpaceSeparated([this, paired], indent, level));
                return caret;
            }
            default:
                throw new Error(`push_left: unexpected ${func}`);
        }
    }

    push_line_comment(comment) {
        if (this.parent) return this.parent.push_line_comment(comment);
        throw new Error(`push_line_comment: no parent for ${this.constructor.name}`);
    }

    push_minus() {
        throw new Error('push_minus is unexpected for ' + this.constructor.name);
    }

    push_multiple(funcName, caret) {
        const parent = this.parent;
        if (!parent) throw new Error('push_multiple: no parent');
        const Ctor = getLeanClass(funcName);
        if (parent instanceof Ctor) {
            parent.push(caret);
        } else {
            parent.replace(this, new Ctor([this, caret], this.indent, this.level));
        }
        return caret;
    }

    push_or() {
        const parent = this.parent;
        if (!parent) return undefined;
        const Ctor = LEAN_CLASSES.Lean_lor;
        return Ctor.input_priority > parent.stack_priority
            ? this.push_multiple('Lean_lor', new LeanCaret(this.indent, this.level))
            : parent.push_or();
    }

    push_post_unary(funcName) {
        const parent = this.parent;
        if (!parent) return undefined;
        const Ctor = getLeanClass(funcName);
        if (Ctor.input_priority > parent.stack_priority) {
            const created = new Ctor(this, this.indent, this.level);
            parent.replace(this, created);
            return created;
        }
        return parent.push_post_unary(funcName);
    }

    push_quote(_quote) {
        throw new Error('push_quote is unexpected for ' + this.constructor.name);
    }

    push_right(funcName) {
        if (this.parent) return this.parent.push_right(funcName);
    }

    push_token(word) {
        return this.append(new LeanToken(word, this.indent, this.level), 'token');
    }

    regexp() {
        return [];
    }

    relocate_last_comment() {}

    set_line(line) {
        this.line = line;
        return line;
    }

    split(_syntax) {
        return [this];
    }

    strArgs() {
        return this.args ?? [];
    }

    tokens_space_separated() {
        return [];
    }

    toLatex(syntax) {
        const fmt = this.latexFormat();
        const args = this.latexArgs(syntax);
        if (args.length) return String(fmt).format(...args);
        return fmt;
    }

    *traverse() {
        yield this;
    }
}

export class LeanArgs extends Lean {
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

    /** PHP `LeanArgs::__get('func')`: `preg_replace('/^Lean_?/', '', get_class($this))`. */
    get func() {
        return this.constructor.name.replace(/^Lean_?/, '');
    }

    /** PHP `LeanArgs::__get('command')`: `"\\$this->func"` (LaTeX command name). */
    get command() {
        return '\\' + this.func;
    }

    push(arg) {
        this.args.push(arg);
        arg.parent = this;
    }

    replace(oldNode, newNode) {
        const i = this.args.indexOf(oldNode);
        if (i < 0) throw new Error(`replace: not found in ${this.constructor.name}`);
        if (Array.isArray(newNode)) {
            this.args.splice(i, 1, ...newNode);
            for (const el of newNode) el.parent = this;
        } else {
            this.args[i] = newNode;
            newNode.parent = this;
        }
    }

    push_binary(funcName) {
        const parent = this.parent;
        if (!parent) return undefined;
        const Ctor = getLeanClass(funcName);
        if (Ctor.input_priority > parent.stack_priority) {
            const level = this.level;
            const caret = new LeanCaret(this.indent, level);
            parent.replace(this, new Ctor(this, caret, this.indent, level));
            return caret;
        }
        return parent.push_binary(funcName);
    }

    insert_tactic(caret, func) {
        if (caret instanceof LeanCaret) {
            this.replace(caret, new LeanTactic(func, caret, this.indent, caret.level));
            return caret;
        }
        return this.insert_word(caret, func);
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    /** Replace trailing caret with `LeanCalc`. */
    insert_calc(caret) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            this.replace(caret, new LeanCalc(caret, caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_calc: unexpected for ${this.constructor.name}`);
    }

    /**
     * @param {number} indent
     * @param {number} newlineCount
     * @param {boolean} [functionCall]
     * @returns {LeanCaret | undefined}
     */
    push_args_indented(indent, newlineCount, functionCall = true) {
        const end = this.args[this.args.length - 1];
        if (
            !functionCall ||
            end instanceof LeanToken ||
            end instanceof LeanProperty ||
            end.constructor.name === 'LeanParenthesis'
        ) {
            const caret = new LeanCaret(indent, end.level);
            const nl = new LeanArgsNewLineSeparated([caret], indent, caret.level);
            const c = nl.push_newlines(newlineCount - 1);
            this.replace(end, new LeanArgsIndented(end, nl, this.indent, c.level));
            return c;
        }
    }

    /**
     * Deep-clone `args` and reparent children (same pattern as `Lean.prototype.clone` shell).
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
     * @returns {Lean[]}
     */
    strip_parenthesis() {
        return this.args.map((arg) => {
            if (!(arg instanceof LeanParenthesis)) return arg;
            const inner = arg.arg;
            const n = inner?.constructor?.name;
            if (n === 'LeanMethodChaining' || n === 'Lean_rightarrow' || n === 'LeanColon') return arg;
            return inner;
        });
    }

    /** Propagate line numbers through `args`. */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            if (arg != null) line = arg.set_line(line);
        }
        return line;
    }

    jsonSerialize() {
        return this.args.map((a) =>
            a == null ? a : typeof a.jsonSerialize === 'function' ? a.jsonSerialize() : a,
        );
    }

    /** Preorder over `this` then each `arg`. */
    *traverse() {
        yield this;
        for (const arg of this.args) {
            if (arg != null) yield* arg.traverse();
        }
    }

    // insert_comma, insert_semicolon, insert_assign, push_right, push_or, push_post_unary, etc.
    // inherit from Lean — delegate to parent; do not override with throws.
}

/** Comma-separated argument list; method order matches PHP class `LeanArgsCommaSeparated`. */
export class LeanArgsCommaSeparated extends LeanArgs {
    /**
     * Under LeanBar: LeanColon input priority; else one less so `:` binds in the right place.
     * GetElem index uses parent `LeanGetElem*` stack_priority, not this.
     */
    get stack_priority() {
        if (this.parent instanceof LeanBar) return LeanColon.input_priority;
        return LeanColon.input_priority - 1;
    }

    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret) {
            if (caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
                this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                return caret;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        this.push(caret2);
        return caret2;
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        throw new Error(`LeanArgsCommaSeparated.insert_tactic: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
    }

    latexFormat() {
        const n = this.args.length;
        return Array(n)
            .fill('{%s}')
            .join(', ');
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join(', ');
    }

    tokens_comma_separated() {
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanToken) tokens.push(arg);
            else if (arg instanceof LeanAngleBracket) tokens.push(...arg.tokens_comma_separated());
        }
        return tokens;
    }
}

/** Newline-separated args; method order matches PHP class `LeanArgsNewLineSeparated`. */
export class LeanArgsNewLineSeparated extends LeanArgs {
    get stack_priority() {
        const parent = this.parent;
        if (parent instanceof LeanCalc) return LeanAssign.input_priority - 1;
        if (parent instanceof LeanArgsIndented) {
            const gp = parent.parent;
            if (gp instanceof LeanQuantifier) return 51;
            if (gp instanceof LeanCalc) return LeanAssign.input_priority - 1;
        }
        return 47;
    }

    /** Non-last caret: return undefined (see `LeanStatements.insert_if`). */
    insert_if(caret) {
        if (!(caret instanceof LeanCaret)) return undefined;
        const last = this.args[this.args.length - 1];
        if (last !== caret) return undefined;
        this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
        return caret;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) {
            if (caret instanceof LeanParenthesis && next === ':') return caret;
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        if (this.indent < indent) {
            const pushed = this.push_args_indented(indent, newlineCount);
            if (pushed) return pushed;
            const c = new LeanCaret(indent, caret.level);
            this.push(c);
            return c;
        }
        if (this.parent instanceof LeanAssign && !(caret instanceof LeanLineComment)) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        const last = this.args[this.args.length - 1];
        if (last === caret) {
            for (let i = 0; i < newlineCount; ++i) {
                caret = new LeanCaret(indent, caret.level);
                this.push(caret);
            }
            return caret;
        }
        throw new Error(`LeanArgsNewLineSeparated.insert_newline: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
    }

    latexFormat() {
        return Array(this.args.length)
            .fill('{%s}')
            .join('\n');
    }

    push_newlines(newlineCount) {
        for (let i = 0; i < newlineCount; ++i) {
            this.push(new LeanCaret(this.indent, this.level));
        }
        return this.args[this.args.length - 1];
    }

    relocate_last_comment() {
        for (let index = this.args.length - 1; index >= 0; --index) {
            const end = this.args[index];
            if (end instanceof LeanCaret || end.is_comment()) {
                let self = this;
                let parent = null;
                while (self) {
                    parent = self.parent;
                    if (parent instanceof LeanStatements) break;
                    self = parent;
                }
                if (parent) {
                    const last = this.args.pop();
                    const ix = parent.args.indexOf(self);
                    parent.args.splice(ix + 1, 0, last);
                    last.parent = parent;
                    return parent.relocate_last_comment();
                }
            } else {
                return end.relocate_last_comment();
            }
        }
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join('\n');
    }

    /** `LeanMultipleLine`-style line tracking (same pattern as related arg-list classes). */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }
}

/**
 * Comma + newline separated args (`LeanMultipleLine`); used from `LeanPairedGroup.insert_newline`.
 * Method order: class body then `set_line`, matching PHP class `LeanArgsCommaNewLineSeparated`.
 */
export class LeanArgsCommaNewLineSeparated extends LeanArgs {
    get stack_priority() {
        return 17;
    }

    /**
     * @param {Lean} caret
     * @param {string | typeof Lean} func
     * @param {string} [_type]
     */
    insert(caret, func, _type) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        throw new Error(`LeanArgsCommaNewLineSeparated.insert: unexpected for ${this.constructor.name}`);
    }

    insert_comma(caret) {
        const c2 = new LeanCaret(this.indent, caret.level);
        this.push(c2);
        return c2;
    }

    /** When indent increases, also tries `push_args_indented` (multiline `⟨…⟩` / `[…]`). */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        if (this.indent < indent) {
            const pushed = this.push_args_indented(indent, newlineCount);
            if (pushed) return pushed;
            const c = new LeanCaret(indent, caret.level);
            this.push(c);
            return c;
        }
        const last = this.args[this.args.length - 1];
        if (last === caret) {
            for (let i = 0; i < newlineCount - 1; ++i) {
                caret = new LeanCaret(indent, caret.level);
                this.push(caret);
            }
            return caret;
        }
        throw new Error(`LeanArgsCommaNewLineSeparated.insert_newline: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
    }

    latexFormat() {
        return Array(this.args.length)
            .fill('{%s}')
            .join(',\n');
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join(',\n');
    }

    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }
}

/** Semicolon-separated args; method order matches PHP class `LeanArgsSemicolonSeparated`. */
export class LeanArgsSemicolonSeparated extends LeanArgs {
    get stack_priority() {
        return LeanColon.input_priority - 1;
    }

    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret) {
            if (caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
                this.replace(caret, new Ctor(caret, caret.indent, caret.level));
                return caret;
            }
            if (this.parent) return this.parent.insert(this, func, type);
        }
    }

    insert_semicolon(caret) {
        const c = new LeanCaret(this.indent, caret.level);
        this.push(c);
        return c;
    }

    insert_tactic(caret, type) {
        if (caret instanceof LeanCaret) {
            const p = this.parent;
            if ((p instanceof LeanTactic && p.is_inline_tactic_block()) || p instanceof LeanBy) {
                this.replace(caret, new LeanTactic(type, caret, this.indent, caret.level));
                return caret;
            }
            return this.insert_word(caret, type);
        }
        throw new Error(`LeanArgsSemicolonSeparated.insert_tactic: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
    }

    latexFormat() {
        return Array(this.args.length)
            .fill('{%s}')
            .join('; ');
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join('; ');
    }
}

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

    /** PHP `LeanBinary::__set('lhs'|'rhs')`. */
    set rhs(v) {
        this.args[1] = v;
        if (v) v.parent = this;
    }

    /**
     * PHP `LeanBinary` has no `__get('operator')`. Concrete subclasses use `case 'operator':` there;
     * in JS each of those classes defines `get operator()`. This base getter only mirrors tokens
     * that live in `token2classname` (e.g. `+`, `∈`, `⊆`) when a subclass does not override.
     */
    get operator() {
        const name = this.constructor.name;
        const pair = Object.entries(token2classname).find(([, cls]) => cls === name);
        return pair ? pair[0] : null;
    }

    /** Space vs newline between lhs/rhs depending on rhs shape. */
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

    strFormat() {
        const op = this.operator;
        if (op == null) return super.strFormat();
        const sep = this.sep();
        return `%s ${op}${sep}%s`;
    }

    /** LaTeX operator token; literals for arithmetic/relations vs macro names. */
    get command() {
        switch (this.constructor.name) {
            case 'LeanAdd':
                return '+';
            case 'LeanSub':
                return '-';
            case 'LeanDiv':
                return '\\frac';
            case 'LeanMatMul':
                return '{\\color{red}\\times}';
            case 'Lean_times':
                return '×';
            case 'Lean_approx':
                return '\\approx';
            case 'LeanColon':
                return ':';
            case 'LeanEq':
                return '=';
            case 'LeanAssign':
                return ':=';
            case 'Lean_equiv':
                return '\\equiv';
            case 'Lean_in':
                return '\\in';
            case 'Lean_cup':
                return '\\cup';
            case 'Lean_cap':
                return '\\cap';
            case 'Lean_sqcap':
                return '\\sqcap';
            case 'Lean_sqcup':
                return '\\sqcup';
            case 'Lean_le':
                return '\\le';
            case 'Lean_ge':
                return '\\ge';
            case 'Lean_lt':
                return '<';
            case 'Lean_gt':
                return '>';
            case 'Lean_ne':
                return '\\ne';
            case 'LeanBEq':
                return '\\!\\!=';
            case 'Lean_simeq':
                return '\\simeq';
            case 'Lean_asymp':
                return '\\asymp';
            case 'LeanDvd':
                return '{\\color{red}{\\ \\mid\\ }}';
            case 'Lean_notin':
                return '\\notin';
            case 'Lean_leftrightarrow':
                return '\\leftrightarrow';
            case 'Lean_rightarrow':
                return '\\rightarrow';
            case 'Lean_lor':
                return '\\lor';
            case 'Lean_land':
                return '\\land';
            case 'LeanPow':
                return '^';
            case 'LeanFDiv':
                return '/\\!\\!/';
            case 'LeanModular':
                return '\\%\\%';
            case 'Lean_cdotp':
                return '{\\color{red}\\cdotp}';
            case 'LeanAppend':
                return '+\\!\\!+';
            case 'LeanConstruct':
                return '::';
            case 'LeanVConstruct':
                return '::_v';
            case 'LeanBitAnd':
                return '\\&';
            case 'LeanBitwiseAnd':
                return '\\&\\!\\!\\&\\!\\!\\&';
            case 'LeanBitwiseXor':
                return '\\^\\^\\^';
            case 'LeanBitOr':
                return '|';
            case 'LeanBitwiseOr':
                return '|\\!\\!|\\!\\!|';
            case 'LeanLogicAnd':
                return '\\&\\&';
            case 'LeanLogicOr':
                return '\\|\\|';
            case 'LeanLogicXor':
                return '\\^\\^';
            case 'Lean_subseteq':
                return '\\subseteq';
            case 'Lean_subset':
                return '\\subset';
            case 'Lean_supseteq':
                return '\\supseteq';
            case 'Lean_supset':
                return '\\supset';
            case 'Lean_setminus':
                return '\\setminus';
            case 'Lean_is':
                return '{\\color{blue}\\text{is}}';
            case 'Lean_is_not':
                return '{\\color{blue}\\text{is not}}';
            default:
                return super.command;
        }
    }

    latexFormat() {
        return `{%s} ${this.command} {%s}`;
    }

    echo() {
        this.rhs?.echo?.();
    }

    insert_if(caret) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    /** PHP `LeanBinary::insert_newline`. */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.parent instanceof LeanTactic && indent > this.indent) {
            return this.parent.push_args_indented(indent, newlineCount, false);
        }
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
    }

    /** PHP `LeanBinary::insert_tactic`. */
    insert_tactic(caret, func) {
        return this.insert_word(caret, func);
    }
}

/** Property access `Foo.bar`. */
export class LeanProperty extends LeanBinary {
    static input_priority = 81;

    /** Extra space before trig/log rhs token names. */
    is_space_separated() {
        const rhs = this.rhs;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    return true;
                default:
                    break;
            }
        }
        return false;
    }

    get command() {
        return '.';
    }
    get operator() {
        return '.';
    }
    strFormat() {
        return `%s${this.operator}%s`;
    }
    latexFormat() {
        return `{%s}${this.command}{%s}`;
    }
}

/** Type ascription / declaration colon. */
export class LeanColon extends LeanBinary {
    static input_priority = 19;

    /** PHP `LeanColon::is_indented` returns false (so `__toString` adds no extra column here). */
    is_indented() {
        return false;
    }

    /** PHP `LeanColon::__get('operator')`. */
    get operator() {
        return ':';
    }

    /** `lemma main:\n` is tight; `{a b : α} :\n` keeps a space before the final colon. */
    colonLhsLooksLikeBinderHead() {
        const L = this.lhs;
        if (!L) return true;
        if (L instanceof LeanParenthesis) return true;
        const n = L.constructor?.name;
        if (n === 'LeanBracket' || n === 'LeanBrace') return true;
        if (L instanceof LeanArgsSpaceSeparated) {
            const active = L.args.filter((a) => a != null && !(a instanceof LeanCaret));
            if (active.length !== 1) return true;
            return !(active[0] instanceof LeanToken);
        }
        if (L instanceof LeanToken) return false;
        return true;
    }

    /** Spacing for caret vs statements vs binder-like lhs (round-trip). */
    strFormat() {
        const rhs = this.rhs;
        const inGetElem = this.parent?.constructor?.name === 'LeanGetElem';
        if (inGetElem) {
            const sep = rhs instanceof LeanCaret ? '' : ' ';
            return `%s:${sep}%s`;
        }
        if (rhs instanceof LeanStatements) {
            return this.colonLhsLooksLikeBinderHead() ? '%s :\n%s' : '%s:\n%s';
        }
        const sep = rhs instanceof LeanCaret ? '' : ' ';
        const first = '%s ';
        return `${first}:${sep}%s`;
    }

    /** PHP `LeanColon::strArgs`. */
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

    insert_newline(caret, newlineCount, indent, next) {
        if (this.rhs === caret) {
            if (caret instanceof LeanCaret && indent >= this.indent) {
                let ind = indent;
                if (ind === this.indent) ind = this.indent + 2;
                caret.indent = ind;
                const stmts = new LeanStatements([caret], ind, caret.level);
                this.replace(caret, stmts);
                return caret;
            }
            if (caret instanceof LeanStatements && indent === this.indent && this.parent?.constructor.name === 'LeanParenthesis') return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
}

/** Definition / assignment `:=`. Method order matches PHP `LeanAssign`. */
export class LeanAssign extends LeanBinary {
    static input_priority = 18;

    /** PHP `LeanAssign::__get('operator'|'command')`. */
    get operator() {
        return ':=';
    }

    get command() {
        return ':=';
    }

    /** PHP `LeanAssign::echo`. */
    echo() {
        this.rhs?.echo?.();
    }

    /**
     * PHP `LeanAssign::insert` (rhs caret only). When `caret !== rhs`, bubble like `LeanArgs*::insert`
     * unresolved arms — the tokenizer sometimes targets a nested caret while `rhs` is already wrapped.
     */
    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }

    /** PHP `LeanAssign::insert_newline`. */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent < indent) {
            if (caret === this.rhs) {
                let out = caret;
                if (caret instanceof LeanCaret) {
                    caret.indent = indent;
                    this.rhs = new LeanArgsNewLineSeparated([caret], indent, caret.level);
                    out = this.rhs.push_newlines(newlineCount - 1);
                } else if (caret instanceof LeanArgsNewLineSeparated) {
                    if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
                } else {
                    if (this.parent instanceof LeanCalc)
                        return this.parent.insert_newline(this, newlineCount, indent, next);
                    out = this.push_args_indented(indent, newlineCount, false);
                }
                return out;
            }
            throw new Error(`insert_newline is unexpected for ${this.constructor.name}`);
        }
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
    }

    /** PHP `LeanAssign::insert_tactic`. */
    insert_tactic(caret, type) {
        return this.insert_word(caret, type);
    }

    /** PHP `LeanAssign::is_indented`. */
    is_indented() {
        const p = this.parent;
        return !p || p instanceof LeanArgsNewLineSeparated || (p instanceof LeanArgsIndented && p.rhs === this);
    }

    /** PHP `LeanAssign::relocate_last_comment`. */
    relocate_last_comment() {
        this.rhs.relocate_last_comment();
    }

    /** PHP `LeanAssign::sep`. */
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
        return ' ';
    }

    /**
     * PHP `LeanAssign::split`.
     * @param {Record<string, unknown>} [syntax]
     * @returns {Lean[]}
     */
    split(syntax) {
        const by = this.rhs;
        if (by instanceof LeanBy && by.arg instanceof LeanStatements) {
            const self = this.clone();
            const stmts = by.arg;
            self.rhs.arg = new LeanCaret(by.indent, by.level);
            const statements = [self];
            stmts.swap_echo_star(syntax, statements);
            return statements;
        }
        return [this];
    }

    /** PHP `LeanAssign::strFormat`. */
    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

/**
 * PHP `abstract class LeanBinaryBoolean` and `trait LeanProp` (`isProp` always true).
 * Other PHP members on that class stay on `LeanBinary` in JS unless a subclass overrides.
 */
export class LeanBinaryBoolean extends LeanBinary {
    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }
}

/** PHP `LeanRelational` (abstract): relational / equality for `instanceof` parity. */
export class LeanRelational extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** Relational / equality binary nodes (`>`, `≥`, `=`, `≃`, `∣`, …). */
export class Lean_gt extends LeanRelational {
    static input_priority = 50;
}
export class Lean_ge extends LeanRelational {
    static input_priority = 50;
    /** PHP `Lean_ge::__get('operator')`. */
    get operator() {
        return '≥';
    }
}
export class Lean_lt extends LeanRelational {
    static input_priority = 50;
}
export class Lean_le extends LeanRelational {
    static input_priority = 50;
    /** PHP `Lean_le::__get('operator')`. */
    get operator() {
        return '≤';
    }
}
export class LeanEq extends LeanRelational {
    static input_priority = 50;

    /** PHP `LeanEq::__get('operator')`. */
    get operator() {
        return '=';
    }
}
export class LeanBEq extends LeanRelational {
    static input_priority = 50;

    /** PHP `LeanBEq::__get('operator')`. */
    get operator() {
        return '==';
    }
}
export class Lean_bne extends LeanRelational {
    static input_priority = 50;

    /** PHP `Lean_bne::__get('operator')`. */
    get operator() {
        return '!=';
    }
}
export class Lean_ne extends LeanRelational {
    static input_priority = 50;
    /** PHP `Lean_ne::__get('operator')`. */
    get operator() {
        return '≠';
    }
}
export class Lean_equiv extends LeanRelational {
    static input_priority = 40;
}
export class LeanNotEquiv extends LeanRelational {
    static input_priority = 40;
}
export class Lean_simeq extends LeanRelational {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≃'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_approx extends LeanRelational {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≈'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_asymp extends LeanRelational {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≍'] = true;
        return super.latexArgs(syntax);
    }
}
export class LeanDvd extends LeanRelational {
    static input_priority = 50;
}

/** Set / arrow: `∈` (membership). */
export class Lean_in extends LeanBinaryBoolean {
    static input_priority = 50;
    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon)) lhs = lhs.arg;
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
export class Lean_notin extends LeanBinaryBoolean {
    static input_priority = 50;
    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof LeanParenthesis) lhs = lhs.arg;
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
/** `↔`. */
export class Lean_leftrightarrow extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** PHP `LeanArithmetic` (abstract): ring / bitwise / shift / lattice ops for `instanceof` parity. */
export class LeanArithmetic extends LeanBinary {}

/** Arithmetic / ring / bitwise / shift / lattice ops (`+`, `×`, `^`, `⊓`, …). */
export class LeanAdd extends LeanArithmetic {
    static input_priority = 65;
}
export class LeanSub extends LeanArithmetic {
    static input_priority = 65;
}
export class LeanMul extends LeanArithmetic {
    static input_priority = 70;

    /** LaTeX: `\\cdot`, thin space, or empty for juxtaposition. */
    get command() {
        const lhs = this.lhs;
        const rhs = this.rhs;
        if (
            (rhs instanceof LeanParenthesis && rhs.arg instanceof LeanDiv) ||
            (rhs instanceof LeanToken && /^\d+$/.test(rhs.text)) ||
            (rhs instanceof LeanMul && rhs.command) ||
            (lhs instanceof LeanMul && lhs.command) ||
            lhs.is_space_separated?.() ||
            lhs instanceof LeanFDiv ||
            rhs instanceof LeanPow
        ) {
            return '\\cdot';
        }
        if (
            (lhs instanceof LeanToken &&
                (rhs.is_space_separated?.() || (rhs instanceof LeanToken && rhs.starts_with_2_letters?.()))) ||
            (lhs instanceof LeanToken && lhs.ends_with_2_letters?.() && rhs instanceof LeanToken) ||
            lhs instanceof LeanProperty ||
            rhs instanceof LeanProperty
        ) {
            return '\\ ';
        }
        return '';
    }
}

/** Matrix multiply `@` (LaTeX via `LeanBinary.command`). */
export class LeanMatMul extends LeanArithmetic {
    static input_priority = 70;
}

/** Lattice meet `⊓`. */
export class Lean_sqcap extends LeanArithmetic {
    static input_priority = 69;
}

/** Lattice join `⊔`. */
export class Lean_sqcup extends LeanArithmetic {
    static input_priority = 68;
}

/** Division `/` (LaTeX `\\frac`). */
export class LeanDiv extends LeanArithmetic {
    static input_priority = 70;
}

/** `×`. */
export class Lean_times extends LeanArithmetic {
    static input_priority = 72;
}

/** `^`. */
export class LeanPow extends LeanArithmetic {
    static input_priority = 80;
}

/** `::`. */
export class LeanConstruct extends LeanArithmetic {
    static input_priority = 67;
}

/** `::ᵥ`. */
export class LeanVConstruct extends LeanArithmetic {
    static input_priority = 67;
}

/** `++`. */
export class LeanAppend extends LeanArithmetic {
    static input_priority = 65;
}

/** `•`. */
export class Lean_bullet extends LeanArithmetic {
    static input_priority = 73;
}

/** `⊙`. */
export class Lean_odot extends LeanArithmetic {
    static input_priority = 73;
}

/** `⊗`. */
export class Lean_otimes extends LeanArithmetic {
    static input_priority = 32;
}

/** `⊕`. */
export class Lean_oplus extends LeanArithmetic {
    static input_priority = 30;
}

/** `⊖`. */
export class Lean_ominus extends LeanBinary {
    static input_priority = 67;
}

/** `⊘`. */
export class Lean_oslash extends LeanBinary {
    static input_priority = 67;
}

/** `⊚`. */
export class Lean_circledcirc extends LeanBinary {
    static input_priority = 67;
}

/** `⊛`. */
export class Lean_circledast extends LeanBinary {
    static input_priority = 67;
}

/** `⊜`. */
export class Lean_circleeq extends LeanBinary {
    static input_priority = 67;
}

/** `⊝`. */
export class Lean_circleddash extends LeanBinary {
    static input_priority = 67;
}

/** `⊞`. */
export class Lean_boxplus extends LeanBinary {
    static input_priority = 67;
}

/** `⊟`. */
export class Lean_boxminus extends LeanBinary {
    static input_priority = 67;
}

/** `⊠`. */
export class Lean_boxtimes extends LeanBinary {
    static input_priority = 67;
}

/** `⊡`. */
export class Lean_dotsquare extends LeanBinary {
    static input_priority = 67;
}

/** Euclidean division `÷`. */
export class LeanEDiv extends LeanBinary {
    static input_priority = 70;
}

/** `//`. */
export class LeanFDiv extends LeanArithmetic {
    static input_priority = 70;
}

/** `%`. */
export class LeanModular extends LeanArithmetic {
    static input_priority = 70;
}

/** `<<`. */
export class Lean_ll extends LeanArithmetic {
    static input_priority = 47;
}

/** `<<<`. */
export class Lean_lll extends LeanArithmetic {
    static input_priority = 47;
}

/** `>>`. */
export class Lean_gg extends LeanArithmetic {
    static input_priority = 47;
}

/** `>>>`. */
export class Lean_ggg extends LeanArithmetic {
    static input_priority = 75;
}

/** `⬝`. */
export class Lean_cdotp extends LeanArithmetic {
    static input_priority = 71;
}

/** `∘`. */
export class Lean_circ extends LeanArithmetic {
    static input_priority = 90;
}

/** `▸`. */
export class Lean_blacktriangleright extends LeanArithmetic {
    static input_priority = 47;
}

/** Bitwise `&`. */
export class LeanBitAnd extends LeanArithmetic {
    static input_priority = 68;
}

/** `&&&`. */
export class LeanBitwiseAnd extends LeanArithmetic {
    static input_priority = 60;
}

/** `^^^`. */
export class LeanBitwiseXor extends LeanArithmetic {
    static input_priority = 60;
}

/** Bar-separated alternatives `|`. */
export class LeanBitOr extends LeanArithmetic {
    static input_priority = 47;

    tokens_bar_separated() {
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanBitOr) tokens.push(...arg.tokens_bar_separated());
            else if (arg instanceof LeanAngleBracket) tokens.push(arg.tokens_comma_separated());
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
        let tok = tokens[0];
        if (Array.isArray(tok) && tok.length === 1) tok = tok[0];
        if (Array.isArray(tok)) {
            const mapped = tok.map((x) => {
                const c = x.clone();
                c.indent = indent;
                return c;
            });
            return new LeanArgsCommaSeparated(mapped, indent, 0);
        }
        const c = tok.clone();
        c.indent = indent;
        return c;
    }
}

/** `|||`. */
export class LeanBitwiseOr extends LeanArithmetic {
    static input_priority = 55;
}

/** `∧`. */
export class Lean_land extends LeanBinaryBoolean {
    static input_priority = 35;
}

/** `&&`. */
export class LeanLogicAnd extends LeanBinaryBoolean {
    static input_priority = 37;
}

/** `||`. */
export class LeanLogicOr extends LeanBinaryBoolean {
    static input_priority = 37;
}

/** `^^`. */
export class LeanLogicXor extends LeanBinaryBoolean {
    static input_priority = 33;
}

/** `∪`. */
export class Lean_cup extends LeanBinary {
    static input_priority = 50;
}

/** `∩`. */
export class Lean_cap extends LeanBinary {
    static input_priority = 50;
}

/** Set difference `\\`. */
export class Lean_setminus extends LeanBinary {
    static input_priority = 70;
}

/** `⊆`. */
export class Lean_subseteq extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** `⊂`. */
export class Lean_subset extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** `⊇`. */
export class Lean_supseteq extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** `⊃`. */
export class Lean_supset extends LeanBinaryBoolean {
    static input_priority = 50;
}

/** `is`. */
export class Lean_is extends LeanBinary {
    static input_priority = 62;

    /** PHP `Lean_is::__get('operator')`. */
    get operator() {
        return 'is';
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

    /** PHP `Lean_is_not::__get('operator')`. */
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

/** Pipeline `|>.`. */
export class LeanMethodChaining extends LeanBinary {
    static input_priority = 67;
}

/** `∨` (lower priority than typical relations). */
export class Lean_lor extends LeanBinaryBoolean {
    static input_priority = 30;
}

/** `→` (right-associative). Method order matches PHP class `Lean_rightarrow`. */
export class Lean_rightarrow extends LeanBinary {
    static input_priority = 25;

    get stack_priority() {
        return 24;
    }

    get operator() {
        return '→';
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.rhs) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            const stmts = new LeanStatements([caret], ind, caret.level);
            this.replace(caret, stmts);
            for (let i = 1; i < newlineCount; i++) {
                const c = new LeanCaret(ind, caret.level);
                stmts.push(c);
            }
            return stmts.args[stmts.args.length - 1];
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    /**
     * @param {Record<string, unknown>} [vars]
     */
    isProp(vars) {
        const lhs = this.lhs;
        const rhs = this.rhs;
        const lhsOk =
            (lhs instanceof LeanToken && (vars?.[lhs.text] ?? 'Prop') === 'Prop') ||
            (!(lhs instanceof LeanToken) && lhs.isProp(vars));
        const rhsOk =
            (rhs instanceof LeanToken && (vars?.[rhs.text] ?? 'Prop') === 'Prop') ||
            (!(rhs instanceof LeanToken) && rhs.isProp(vars));
        return Boolean(lhsOk && rhsOk);
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

/** `↦`; `stack_priority` 23. Method order matches PHP class `Lean_mapsto`. */
export class Lean_mapsto extends LeanBinary {
    static input_priority = 47;

    get stack_priority() {
        return 23;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.rhs) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            const stmts = new LeanStatements([caret], ind, caret.level);
            this.replace(caret, stmts);
            for (let i = 1; i < newlineCount; i++) {
                const c = new LeanCaret(ind, caret.level);
                stmts.push(c);
            }
            return stmts.args[stmts.args.length - 1];
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    is_indented() {
        return false;
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

/** Tactic arrow `=>`; same `input_priority` as `LeanColon`. Method order matches PHP class `LeanRightarrow`. */
export class LeanRightarrow extends LeanBinary {
    static input_priority = 19;

    /** PHP `LeanRightarrow::__get('operator')`. */
    get operator() {
        return '=>';
    }

    echo() {
        /** @type {Lean[]} */
        const token = [];
        const bar = this.parent;
        if (bar instanceof LeanBar) {
            const withNode = bar.parent;
            if (withNode instanceof LeanWith) {
                const outer = withNode.parent;
                if (
                    outer instanceof Lean_match ||
                    (outer instanceof LeanTactic && outer.tacticName === 'induction')
                ) {
                    token.push(new LeanToken('⊢', this.rhs.indent, this.rhs.level));
                    const subject = outer.args[0];
                    if (subject instanceof LeanArgsCommaSeparated) {
                        for (const sujet of subject.args) {
                            if (sujet instanceof LeanColon) token.push(sujet.lhs);
                        }
                    } else if (subject instanceof LeanColon) {
                        token.push(subject.lhs);
                    }
                }
            }
        }
        const expr = this.lhs;
        if (expr instanceof LeanArgsSpaceSeparated) {
            let func = null;
            if (expr.args[0] instanceof LeanToken) func = expr.args[0].text;
            else if (
                expr.args[0] instanceof LeanProperty &&
                expr.args[0].lhs instanceof LeanCaret &&
                expr.args[0].rhs instanceof LeanToken
            ) {
                func = expr.args[0].rhs.text;
            }
            let start = 1;
            switch (func) {
                case 'succ':
                case 'ofNat':
                case 'negSucc':
                    start = 2;
                    break;
                case 'cons':
                    start = 3;
                    break;
                default:
                    start = 1;
            }
            token.push(...expr.args.slice(start));
        } else if (expr instanceof LeanAngleBracket) {
            if (expr.arg instanceof LeanArgsCommaSeparated) {
                token.push(...expr.arg.args.slice(1));
            }
        } else if (expr instanceof LeanArgsCommaSeparated) {
            for (const arg of expr.args) {
                if (arg instanceof LeanAngleBracket && arg.arg instanceof LeanArgsCommaSeparated) {
                    token.push(arg.arg.args[1]);
                }
            }
        }
        const stmt = this.rhs;
        stmt.echo?.();
        if (token.length && stmt instanceof LeanStatements) {
            const indent = stmt.args[0].indent;
            const level = stmt.args[0].level;
            let payload;
            if (token.length > 1) {
                payload = new LeanArgsCommaSeparated(
                    token.map((arg) => {
                        const c = arg.clone();
                        c.indent = indent;
                        c.level = level;
                        return c;
                    }),
                    indent,
                    level
                );
            } else {
                const [only] = token;
                payload = only;
            }
            stmt.unshift(new LeanTactic('echo', payload, indent, level));
        }
    }

    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret === this.rhs) {
            if (caret instanceof LeanCaret || caret instanceof LeanLineComment) {
                let ind = indent;
                if (ind === this.indent) ind = this.indent + 2;
                caret.indent = ind;
                const stmts = new LeanStatements([caret], ind, caret.level);
                this.replace(caret, stmts);
                let nl = newlineCount;
                if (!(caret instanceof LeanCaret)) nl++;
                let last = caret;
                for (let i = 1; i < nl; i++) {
                    last = new LeanCaret(ind, caret.level);
                    stmts.push(last);
                }
                return last;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    is_indented() {
        return false;
    }

    relocate_last_comment() {
        this.rhs.relocate_last_comment();
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : this.rhs instanceof LeanCaret ? '' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        let lhs = '%s';
        if (!(this.lhs instanceof LeanCaret)) lhs += ' ';
        return `${lhs}${this.operator}${sep}%s`;
    }
}

/** Indented `lhs` + newline `rhs`; ports PHP `LeanArgsIndented`. Method order: README Step 3 §2 (alphabetic). */
export class LeanArgsIndented extends LeanBinary {
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        if (this.indent < indent) {
            const pushed = this.push_args_indented(indent, newlineCount);
            if (pushed) return pushed;
            this.rhs = new LeanArgsNewLineSeparated([caret], indent, caret.level);
            return this.rhs.push_newlines(newlineCount);
        }
        if (this.parent instanceof LeanAssign) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        const last = this.args[this.args.length - 1];
        if (last === caret) {
            for (let i = 0; i < newlineCount; ++i) {
                caret = new LeanCaret(indent, caret.level);
                this.push(caret);
            }
            return caret;
        }
        throw new Error(`LeanArgsIndented.insert_newline is unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    latexFormat() {
        const sep = this.sep();
        return `%s${sep}%s`;
    }

    relocate_last_comment() {
        for (let index = this.args.length - 1; index >= 0; --index) {
            const end = this.args[index];
            if (end instanceof LeanCaret || end.is_comment()) {
                let self = this;
                let parent = null;
                while (self) {
                    parent = self.parent;
                    if (parent instanceof LeanStatements) break;
                    self = parent;
                }
                if (parent) {
                    const last = this.args.pop();
                    const ix = parent.args.indexOf(self);
                    parent.args.splice(ix + 1, 0, last);
                    last.parent = parent;
                    return parent.relocate_last_comment();
                }
            } else {
                return end.relocate_last_comment();
            }
        }
    }

    sep() {
        return '\n';
    }

    get stack_priority() {
        if (this.parent instanceof LeanCalc) return 17;
        if (this.parent instanceof LeanQuantifier) return LeanRelational.input_priority + 1;
        return 47;
    }

    strFormat() {
        const sep = this.sep();
        return `%s${sep}%s`;
    }
}

export class LeanUnary extends LeanArgs {
    static input_priority = 47;
    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
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
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    jsonSerialize() {
        return this.arg?.jsonSerialize?.() ?? this.arg;
    }

    replace(oldNode, newNode) {
        if (this.arg !== oldNode) {
            throw new Error(`replace: assert failed in ${this.constructor.name}`);
        }
        this.arg = newNode;
    }
}

/** PHP `LeanUnaryArithmetic` / pre — prefix unary ops for `instanceof` parity. */
class LeanUnaryArithmetic extends LeanUnary {}
class LeanUnaryArithmeticPre extends LeanUnaryArithmetic {}

/** PHP `LeanUnaryArithmeticPost` — postfix unary ops for `instanceof` parity (`push_left`, `LeanPairedGroup::is_indented`). */
export class LeanUnaryArithmeticPost extends LeanUnaryArithmetic {
    static input_priority = 72;
}

/** Tactic block intro `by`. Method order matches PHP class `LeanBy`. */
export class LeanBy extends LeanUnary {
    static input_priority = 47;

    echo() {
        this.arg?.echo?.();
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            this.arg = new LeanStatements([caret], ind, caret.level);
            for (let i = 1; i < newlineCount; ++i) {
                caret = new LeanCaret(ind, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_semicolon(caret) {
        if (caret === this.arg) {
            const c = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanArgsSemicolonSeparated([this.arg, c], this.indent, c.level);
            return c;
        }
        if (this.parent) return this.parent.insert_semicolon(this);
    }

    is_indented() {
        return this.parent instanceof LeanArgsCommaNewLineSeparated;
    }

    latexFormat() {
        const arg = this.arg;
        const command = '{\\color{#00f}by}';
        if (arg instanceof LeanStatements) return `\\begin{align*}\n${command} && \\\\\n%s\n\\end{align*}`;
        return `${command}\\ %s`;
    }

    relocate_last_comment() {
        this.arg?.relocate_last_comment?.();
    }

    sep() {
        return this.arg instanceof LeanStatements ? '\n' : ' ';
    }

    set_line(line) {
        this.line = line;
        let L = line;
        if (this.arg instanceof LeanStatements) L++;
        return this.arg.set_line(L);
    }

    strFormat() {
        const s = this.sep();
        return `by${s}%s`;
    }
}

/** Attribute prefix `@…` on declarations. Method order matches PHP class `LeanAttribute`. */
class LeanAttribute extends LeanUnary {
    get operator() {
        return '@';
    }

    get command() {
        return '@';
    }

    append(new_, _type) {
        return this.push_accessibility(new_, 'public');
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.parent instanceof LeanTactic)
            return super.insert_newline(caret, newlineCount, indent, next);
        return caret;
    }

    is_indented() {
        return false;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    push_accessibility(New, accessibility) {
        switch (New) {
            case 'Lean_theorem':
            case 'Lean_lemma':
            case 'Lean_def': {
                const Ctor = getLeanClass(New);
                const caret = new LeanCaret(this.indent, this.level);
                const replacement = new Ctor(accessibility, caret, this.indent, this.level);
                this.parent.replace(this, replacement);
                replacement.attribute = this;
                return caret;
            }
            default:
                throw new Error(`push_accessibility is unexpected for ${this.constructor.name}`);
        }
    }

    sep() {
        return '';
    }

    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }
}

/** Unary `←`. */
class Lean_leftarrow extends LeanUnary {
    get operator() {
        return '←';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** Unary minus. */
class LeanNeg extends LeanUnaryArithmeticPre {
    static input_priority = 75;
    get operator() {
        return '-';
    }
    sep() {
        return this.arg?.constructor?.name === 'LeanNeg' ? ' ' : '';
    }
    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }
}

/** Unary plus. */
class LeanPlus extends LeanUnaryArithmeticPre {
    get operator() {
        return '+';
    }
    strFormat() {
        return `${this.operator}%s`;
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
    strFormat() {
        return `${this.operator}%s`;
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
    strFormat() {
        return `${this.operator}%s`;
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
    strFormat() {
        return `${this.operator}%s`;
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
    strFormat() {
        return `${this.operator}%s`;
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
    strFormat() {
        return `${this.operator}%s`;
    }
}

/** Logical not `¬`. */
class Lean_lnot extends LeanUnary {
    static input_priority = 40;

    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    get operator() {
        return '¬';
    }

    strFormat() {
        return `${this.operator}%s`;
    }
}

/** Prefix `!` (boolean/programmatic; distinct from `Lean_lnot` `¬`). Method order matches PHP class `LeanNot`. */
class LeanNot extends LeanUnary {
    static input_priority = 40;

    get operator() {
        return '!';
    }

    get command() {
        return '\\text{!}';
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    strFormat() {
        return `${this.operator}%s`;
    }

    isProp(_vars) {
        return true;
    }
}

/** Postfix inverse `⁻¹`. */
class LeanInv extends LeanUnaryArithmeticPost {
    static input_priority = 71;
    get operator() {
        return '⁻¹';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix positive part `⁺`. */
class LeanPosPart extends LeanUnaryArithmeticPost {
    static input_priority = 71;
    get operator() {
        return '⁺';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix negative part `⁻`. */
class LeanNegPart extends LeanUnaryArithmeticPost {
    static input_priority = 71;
    get operator() {
        return '⁻';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix square `²`. */
class LeanSquare extends LeanUnaryArithmeticPost {
    static input_priority = 66;
    get operator() {
        return '²';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix cube `³`. */
class LeanCube extends LeanUnaryArithmeticPost {
    get operator() {
        return '³';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix fourth power `⁴`. */
class LeanTesseract extends LeanUnaryArithmeticPost {
    get operator() {
        return '⁴';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** Postfix transpose `ᵀ`. */
class LeanTranspose extends LeanUnaryArithmeticPost {
    get operator() {
        return 'ᵀ';
    }
    strFormat() {
        return `%s${this.operator}`;
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

/** `|` arm separator in `match` / `with` / `induction`. Method order matches PHP class `LeanBar`. */
class LeanBar extends LeanUnary {
    get stack_priority() {
        return LeanAssign?.input_priority ?? 20;
    }

    get operator() {
        return '|';
    }

    get command() {
        return '|';
    }

    echo() {
        this.arg?.echo?.();
    }

    insert_comma(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanArgsCommaSeparated([caret, new_], this.indent, caret.level));
            return new_;
        }
        throw new Error(`LeanBar.insert_comma: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    is_indented() {
        return true;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    /**
     * Clone bar and detach `=>` rhs statements onto `swap_echo_star` list (proof echo).
     * @param {Record<string, unknown>} [syntax]
     */
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

class LeanPairedGroup extends LeanUnary {
    static input_priority = 60;

    get operator() {
        switch (this.constructor.name) {
            case 'LeanBracket':
                return '[]';
            case 'LeanAngleBracket':
                return ['⟨', '⟩'];
            case 'LeanBrace':
                return '{}';
            case 'LeanParenthesis':
                return '()';
            default:
                return '()';
        }
    }

    argFormat() {
        return '%s';
    }

    /**
     * @param {Lean} caret
     * @param {string | typeof Lean} func
     * @param {string} _type
     */
    insert(caret, func, _type) {
        if (this.arg === caret) {
            if (caret instanceof LeanCaret) {
                const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
                this.arg = new Ctor(caret, this.indent, caret.level);
                return caret;
            }
            if (caret instanceof LeanToken) {
                const caret2 = new LeanCaret(this.indent, caret.level);
                const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
                this.arg = new LeanArgsSpaceSeparated([this.arg, new Ctor(caret2, this.indent, caret.level)], this.indent, caret.level);
                return caret2;
            }
        }
        if (this.parent) return this.parent.insert(this, func, _type);
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const a = this.arg;
        if (a instanceof LeanArgsCommaSeparated) {
            a.push(caret2);
        } else {
            this.arg = new LeanArgsCommaSeparated([a, caret2], this.indent, caret2.level);
        }
        return caret2;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this) {
            caret = this.arg;
        }
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        if (this.indent <= indent) {
            if (caret instanceof LeanCaret) {
                let ind = indent;
                if (ind === this.indent) ind = this.indent + 2;
                caret.indent = ind;
                if (this.constructor.name === 'LeanBrace') {
                    this.arg = new LeanStatements([caret], ind, caret.level);
                    return caret;
                }
                this.arg = new LeanArgsCommaNewLineSeparated([caret], ind, caret.level);
                return caret;
            }
            if (indent === this.indent) return caret;
            /**
             * `Lean::insert_newline` bubbles with `this` (not the inner parse node), so `caret` is often the
             * full `arg` (e.g. `LeanArgsSpaceSeparated`) while `indent` is the continuation column inside a
             * nested `()` / last operand. Descend to the trailing structural child and recurse — mirrors
             * how the proof term continues on the next line (last sibling).
             * Do not recurse into `LeanCaret`: `LeanCaret.insert_newline` delegates to parent and would pass
             * the whole `LeanArgsSpaceSeparated` again → infinite loop with this branch.
             */
            if (indent > this.indent && caret === this.arg) {
                let target = this.arg;
                while (target instanceof LeanArgsSpaceSeparated) {
                    const next = target.args[target.args.length - 1];
                    if (!next) break;
                    target = next;
                }
                if (target instanceof LeanCaret || target instanceof LeanArgsSpaceSeparated) {
                    return super.insert_newline(caret, newlineCount, indent, next);
                }
                if (target instanceof LeanPairedGroup) {
                    return target.insert_newline(target, newlineCount, indent, next);
                }
                return super.insert_newline(caret, newlineCount, indent, next);
            }
            throw new Error(`LeanPairedGroup.insert_newline: unexpected for ${this.constructor.name}`);
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        if (this.parent) return this.parent.insert_tactic(caret, token);
        throw new Error(`LeanPairedGroup.insert_tactic: unexpected for ${this.constructor.name}`);
    }

    is_Expr() {
        return true;
    }

    is_indented() {
        const parent = this.parent;
        return !(
            parent instanceof LeanTactic ||
            parent instanceof LeanArgsCommaSeparated ||
            parent instanceof LeanAssign ||
            parent instanceof LeanArgsSpaceSeparated ||
            parent instanceof LeanBinaryBoolean ||
            parent instanceof LeanRightarrow ||
            parent instanceof LeanUnaryArithmeticPre ||
            parent instanceof LeanArithmetic ||
            parent instanceof LeanProperty ||
            parent instanceof LeanColon ||
            parent instanceof LeanUnaryArithmeticPost ||
            parent instanceof LeanPairedGroup
        );
    }

    /** @param {string} funcName e.g. 'LeanParenthesis' */
    push_right(funcName) {
        if (this.constructor.name === funcName) {
            this.is_closed = true;
            return this;
        }
        if (this.parent) return this.parent.push_right(funcName);
    }

    set_line(line) {
        this.line = line;
        const arg = this.arg;
        const hasNewline =
            arg instanceof LeanArgsCommaNewLineSeparated || arg instanceof LeanStatements;
        if (hasNewline) line++;
        line = arg.set_line(line);
        if (hasNewline) line++;
        return line;
    }

    strFormat() {
        let format = this.argFormat();
        const operator = this.operator;
        const open = typeof operator === 'string' ? operator[0] : operator[0];
        const close = typeof operator === 'string' ? operator[1] : operator[1];
        const c = this.is_closed;
        if (c === false) {
            format += close;
        } else if (c === null) {
            format = open + format;
        } else {
            format = open + format + close;
        }
        return format;
    }

    /**
     * When `'` continues a name after `[…]` etc., caret may be a paired group; delegate to parent `insert_word`.
     */
    push_quote(token) {
        if (this.parent) return this.parent.insert_word(this, token);
        throw new Error('push_quote: no parent');
    }

    /** Sibling token after a closed group (e.g. function application continuing after `)`). */
    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    get is_closed() {
        return this.kwargs.is_closed;
    }

    set is_closed(v) {
        this.kwargs.is_closed = v;
    }
}

/**
 * Port of `LeanParenthesis`.
 * Parentheses bump inner `level` and handle newlines/`by` differently from generic `LeanPairedGroup`.
 * Rainbow printing: nesting level (arg.level) selects one of 8 colors via toColor().
 */
export class LeanParenthesis extends LeanPairedGroup {
    /** PHP `LeanParenthesis::__get('stack_priority')` returns 10. Ensures `:` creates LeanColon inside parens, e.g. (1 : Tensor ℝ* [n,n]). */
    get stack_priority() {
        return 10;
    }

    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super(arg, indent, level, parent);
        this.arg.level++;
    }

    /**
     * PHP `LeanParenthesis::toColor`.
     * Maps nesting level (arg.level & 7) to RGB hex for rainbow parentheses.
     */
    toColor() {
        const n = (this.arg.level ?? 0) & 7;
        const b = '9f'[n & 1];
        const g = '9f'[(n >> 1) & 1];
        const r = '9f'[(n >> 2) & 1];
        return `\\colorbox{#${r}${g}${b}}{$\\mathord{\\left(%s\\right)}$}`;
    }

    /**
     * PHP `LeanParenthesis::latexFormat`.
     * Special cases for LeanColon/lhs LeanBrace and Bool; otherwise rainbow colorbox.
     */
    latexFormat() {
        const arg = this.arg;
        if (arg instanceof LeanColon) {
            if (arg.lhs && arg.lhs.constructor?.name === 'LeanBrace') return arg.lhs.latexFormat?.() ?? '%s';
            if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return '\\left|{%s}\\right|';
        }
        return this.toColor();
    }

    /**
     * PHP `LeanParenthesis::latexArgs`.
     */
    latexArgs(syntax) {
        const arg = this.arg;
        if (arg instanceof LeanColon) {
            if (arg.lhs && arg.lhs.constructor?.name === 'LeanBrace')
                return arg.lhs.latexArgs?.(syntax) ?? [arg.lhs.toLatex(syntax)];
            if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return [arg.lhs.toLatex(syntax)];
        }
        return super.latexArgs(syntax);
    }

    /**
     * Port of `LeanParenthesis::insert_newline`.
     */
    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this) {
            caret = this.arg;
        }
        if (this.indent <= indent && caret === this.arg) {
            if (caret instanceof LeanBy && this.indent === indent) {
                const c2 = new LeanCaret(indent, caret.level);
                const newNL = new LeanArgsNewLineSeparated([this.arg, c2], indent, c2.level);
                const c = newNL.push_newlines(newlineCount - 1);
                this.arg = newNL;
                return c;
            }
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            const c = this.push_args_indented(ind, newlineCount, false);
            return c;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
}

/**
 * PHP `std\Expr` used by `eval_prefix`.
 * @typedef {import('./node.js').Node} LeanNode
 */
class LeanPrefixExpr {
    /**
     * @param {LeanToken} func
     * @param {LeanPrefixExpr[]} args
     */
    constructor(func, args) {
        this.func = func;
        this.args = args;
        /** @type {LeanPrefixExpr | null} */
        this.parent = null;
        /** @type {Record<string, unknown>} */
        this.cache = {};
        for (const arg of args) {
            if (arg) arg.parent = this;
        }
    }

    /**
     * @param {(n: LeanPrefixExpr) => void} visit
     */
    traverse(visit) {
        visit(this);
        for (const arg of this.args) arg.traverse(visit);
    }

    size() {
        if (this.cache.size != null) return /** @type {number} */ (this.cache.size);
        let s = 1;
        for (const arg of this.args) s += arg.size();
        this.cache.size = s;
        return s;
    }
}

/** PHP `std\eval_prefix`. */
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
        stack.push(new LeanPrefixExpr(token, operand));
    }
    return stack.reverse();
}

export class LeanArgsSpaceSeparated extends LeanArgs {
    static input_priority = 80;

    constructor(args, indent, level, parent = null) {
        super(args, indent, level, parent);
        /** @type {Record<string, unknown> | null} PHP `LeanArgsSpaceSeparated::$cache` */
        this.cache = null;
    }

    /** PHP `LeanArgsSpaceSeparated::construct_prefix_tree`. */
    construct_prefix_tree() {
        const tokens = this.tokens_space_separated();
        return leanEvalPrefix(tokens, (arg) => arg.operand_count());
    }

    /**
     * When inside LeanBracket (e.g. [i < n]), use LeanBracket's stack_priority (17) so that
     * Lean_lt is created by replacing the token (LeanToken "i"), not the whole group.
     * When inside GetElem index lists or `LeanGetElem*`, use 18 so +, :, ⊓ parse inside the index.
     */
    get stack_priority() {
        if (this.parent?.constructor?.name === 'LeanBracket') return 17;
        const pc = this.parent?.constructor?.name;
        if (pc === 'LeanArgsCommaSeparated' && this.parent?.parent?.constructor?.name === 'LeanGetElem')
            return 18;
        if (pc === 'LeanGetElem' || pc === 'LeanGetElemQue' || pc === 'LeanGetElemQuote') return 18;
        return 80;
    }

    /** PHP `LeanArgsSpaceSeparated::is_space_separated`. */
    is_space_separated() {
        return true;
    }

    latexFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n)
            .fill('{%s}')
            .join('\\ ');
    }

    /** PHP `LeanArgsSpaceSeparated::operand_count`. */
    operand_count() {
        return this.args[0].operand_count();
    }

    /** PHP `LeanArgsSpaceSeparated::strFormat` (one `%s` per arg, including carets). */
    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join(' ');
    }

    /** PHP `LeanArgsSpaceSeparated::tactic_block_info`. */
    tactic_block_info() {
        if (!this.cache) this.cache = {};
        if (this.cache.tactic_block_info != null)
            return /** @type {Record<number, LeanToken[]>} */ (this.cache.tactic_block_info);
        const nodes = this.construct_prefix_tree();
        let physic_index = 0;
        let logic_index = 0;
        for (const node of nodes) {
            node.traverse((n) => {
                /** @type {LeanPrefixExpr[] | null} */
                let args;
                if (n.parent) args = n.parent.args;
                else args = nodes;
                const i = args.indexOf(n);
                if (i > 0) {
                    for (let j = i - 1; j >= 0; j--) {
                        const size = args[j].size();
                        const pi = /** @type {{ physic_index?: number }} */ (args[j].cache).physic_index ?? 0;
                        if (pi + size === physic_index) {
                            const fc = /** @type {LeanToken} */ (args[j].func);
                            if (!fc.cache) fc.cache = {};
                            const idx = /** @type {{ index?: number }} */ (fc.cache).index ?? 0;
                            logic_index = Math.max(logic_index, idx + size);
                        }
                    }
                } else if (n.parent && /** @type {LeanToken} */ (n.parent.func).is_parallel_operator()) {
                    logic_index++;
                }
                const f = /** @type {LeanToken} */ (n.func);
                if (!f.cache) f.cache = {};
                f.cache.index = logic_index;
                f.cache.size = n.size();
                n.cache.physic_index = physic_index;
                physic_index++;
            });
        }
        const tokens = this.tokens_space_separated();
        /** @type {Record<number, LeanToken[]>} */
        const map = {};
        for (let ti = tokens.length - 1; ti >= 0; ti--) {
            const token = tokens[ti];
            if (!token.cache) token.cache = {};
            if (token.is_parallel_operator()) {
                const sz = /** @type {{ size?: number }} */ (token.cache).size ?? 1;
                token.cache.size = sz - 1;
            }
            const idx = /** @type {{ index?: number }} */ (token.cache).index ?? 0;
            if (!map[idx]) map[idx] = [];
            map[idx].push(token);
        }
        this.cache.tactic_block_info = map;
        return map;
    }

    /**
     * PHP `LeanArgsSpaceSeparated::tokens_space_separated`.
     * @returns {LeanToken[]}
     */
    tokens_space_separated() {
        if (!this.cache) this.cache = {};
        if (this.cache.tokens_space_separated != null)
            return /** @type {LeanToken[]} */ (this.cache.tokens_space_separated);
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanToken) tokens.push(arg);
            else if (arg instanceof LeanAngleBracket) tokens.push(...arg.tokens_comma_separated());
            else {
                this.cache.tokens_space_separated = [];
                return [];
            }
        }
        this.cache.tokens_space_separated = tokens;
        return tokens;
    }

    /** JS helper: subscript glue and sparse holes vs PHP `implode` default `toLatex` path. */
    toLatex(syntax) {
        const active = this.args.filter((a) => !(a instanceof LeanCaret));
        if (active.length === 0) return '';
        const parts = [];
        for (let i = 0; i < active.length; i++) {
            const cur = active[i];
            const curLatex = cur.toLatex(syntax);
            if (!curLatex) continue;
            if (parts.length > 0) {
                const prev = active[i - 1];
                const prevText = prev instanceof LeanToken ? prev.text : '';
                const sep =
                    prev && prevText.length > 1 && prevText.endsWith('_') && cur instanceof LeanToken
                        ? ''
                        : '\\ ';
                parts.push(sep);
            }
            parts.push(curLatex);
        }
        return parts.join('');
    }
}

export class LeanStatements extends LeanArgs {
    get stack_priority() {
        return 19;
    }

    /** PHP `LeanStatements::strFormat` — always `\n` between args; `LeanBrace` parent adds wrapped newlines + indent. */
    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        let format = Array(n).fill('%s').join('\n');
        if (this.parent instanceof LeanBrace) {
            format = `\n${format}\n${' '.repeat(this.parent.indent)}`;
        }
        return format;
    }

    /**
     * PHP LeanStatements::latexFormat.
     * Each statement on its own line in align; `\\` between rows so let blocks render with newlines.
     */
    latexFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        const stmt = Array(n)
            .fill('&{%s}&& ')
            .join('\\\\\n');
        if (this.parent && this.parent.constructor?.name === 'LeanBy') return stmt;
        return `\\begin{align*}\n${stmt}\n\\end{align*}`;
    }

    /**
     * Port of `LeanStatements::relocate_last_comment`.
     */
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
                    const ix = parent.args.indexOf(self);
                    parent.args.splice(ix + 1, 0, last);
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

    /** Port of LeanStatements::push_line_comment. Stops bubbling to root. */
    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }

    /**
     * PHP `LeanStatements::swap_echo_star`.
     * @param {Record<string, unknown>} syntax
     * @param {Lean[]} statements
     */
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

    /** PHP trait `LeanMultipleLine::set_line` via `LeanStatements`. */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }

    /**
     * PHP `LeanStatements::echo`.
     * @returns {void}
     */
    echo() {
        const args = this.args;
        let count = args.length;
        let voidLines = 0;
        while (count > 0) {
            const last = args[count - 1];
            if (
                last instanceof LeanCaret ||
                last instanceof LeanLineComment ||
                last instanceof LeanBlockComment
            ) {
                count--;
                voidLines++;
            } else break;
        }
        const limit = args.length - voidLines - 1;
        let index = 0;
        while (index < limit) {
            const result = args[index].echo?.();
            if (Array.isArray(result)) {
                const length = /** @type {number} */ (result.shift());
                if (
                    index + 1 < args.length - voidLines &&
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
                const oldRef = args[index];
                const inc = result.indexOf(oldRef);
                const increment = inc >= 0 ? inc : 0;
                args.splice(index, length, ...result);
                index += increment;
            } else {
                index++;
            }
        }
        index = limit;
        const tactic = args[index];
        if (tactic instanceof LeanTactic || tactic?.constructor?.name === 'Lean_match') {
            const w = tactic.with;
            if (w) {
                if (w.sep() === '\n') {
                    for (const c of w.args) c.echo?.();
                } else if (tactic.sequential_tactic_combinator) {
                    const block = tactic.sequential_tactic_combinator.arg;
                    if (block instanceof LeanTacticBlock) block.echo?.();
                    else tactic.sequential_tactic_combinator.echo?.();
                }
            } else if (tactic.sequential_tactic_combinator) {
                tactic.sequential_tactic_combinator.echo?.();
            } else {
                const rb = tactic.repeat_block?.();
                if (rb) rb.echo?.();
            }
        } else if (
            tactic instanceof LeanTacticBlock ||
            tactic instanceof LeanIte ||
            tactic?.constructor?.name === 'LeanCalc'
        ) {
            tactic.echo?.();
        }
    }

    /**
     * PHP `LeanStatements::insert_if`.
     * When `caret` is not `end(args)`, PHP throws; JS previously inherited `Lean::insert_if` and no-op’d
     * (e.g. `if` inside a lemma while the module still has trailing nodes). Return undefined there so corpus parses.
     */
    insert_if(caret) {
        if (!(caret instanceof LeanCaret)) return undefined;
        const last = this.args[this.args.length - 1];
        if (last !== caret) return undefined;
        this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
        return caret;
    }

    /** PHP `LeanStatements::isProp`. */
    isProp(vars) {
        const args = this.args;
        if (args.length === 1) return args[0].isProp?.(vars);
    }

    /** PHP `LeanStatements::jsonSerialize`. */
    jsonSerialize() {
        let args = super.jsonSerialize();
        if (this.args.length && this.args[this.args.length - 1] instanceof LeanCaret) {
            args = args.slice(0, -1);
        }
        if (args.length === 1) return args[0];
        return args;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) return super.insert_newline(caret, newlineCount, indent, next);
        if (this.indent < indent) {
            const c = this.push_args_indented(indent, newlineCount);
            if (c) return c;
            // See `LeanModule.insert_newline` — fall through when last arg cannot be wrapped.
        }
        for (let k = 0; k < newlineCount; ++k) {
            caret = new LeanCaret(indent, caret.level);
            this.push(caret);
        }
        return caret;
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

/**
 * Scan module args after `LeanAssign`/`Lean_def` with empty rhs caret: optional carets, line comments,
 * then `LeanTactic` or space-separated proof. Used for echo `:= by` serialization.
 * @param {Lean[]} moduleArgs
 * @param {number} startJ
 * @param {(s: string, ind: number) => string} indentText
 * @returns {{ cmts: Lean[], proofStr: string, endJ: number } | null}
 */
function consumeEchoAssignProofTail(moduleArgs, startJ, indentText) {
    let j = startJ;
    while (j < moduleArgs.length && moduleArgs[j] instanceof LeanCaret) j++;
    const cmts = [];
    while (j < moduleArgs.length && moduleArgs[j].is_comment?.()) {
        cmts.push(moduleArgs[j]);
        j++;
    }
    const proof = j < moduleArgs.length ? moduleArgs[j] : null;
    const proofOk =
        proof && (proof instanceof LeanTactic || proof instanceof LeanArgsSpaceSeparated);
    if (!proofOk) return null;
    let endJ = j;
    let proofStr = String(proof);
    let proofInd = proof.indent ?? 0;
    for (const c of cmts) proofInd = Math.max(proofInd, c.indent ?? 0);
    if (proof instanceof LeanTactic) {
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
        proofStr = indentText(String(proof), proofInd);
    }
    return { cmts, proofStr, endJ };
}

export class LeanModule extends LeanStatements {
    get root() {
        return this;
    }

    get stack_priority() {
        return -3;
    }

    /**
     * Top-level declarations must be separated by newlines for re-parse: `import A import B` leaves
     * the second `import` inside the first `Lean_import` and breaks `compile(String(root))`.
     * Inner `LeanStatements` (proofs, etc.) keep space-separated `strFormat` from `LeanStatements` / `Lean`.
     */
    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join('\n');
    }

    /**
     * Echo-style lemmas: `LeanAssign` with empty `LeanCaret` rhs and proof on the next module lines — emit `:= by`
     * so the second parse matches.
     */
    toString() {
        const args = this.args;
        const skip = new Set();
        const parts = [];
        const indentText = (s, ind) => {
            if (ind <= 0) return s;
            const pad = ' '.repeat(ind);
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
                        let block = `${head}${String(asn.lhs)} := by`;
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
                    let block = `${String(a.lhs)} := by`;
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
                    const ind = Math.max(a.indent ?? 0, next.indent ?? 0);
                    const as = String(a);
                    const ns = String(next);
                    const join = as.endsWith('\n') ? '' : '\n';
                    parts.push(indentText(`${as}${join}${ns}`, ind));
                    continue;
                }
            }
            parts.push(String(a));
        }
        return parts.join('\n');
    }

    insert_space(caret) {
        return caret;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) return super.insert_newline(caret, newlineCount, indent, next);
        if (this.indent < indent) {
            const c = this.push_args_indented(indent, newlineCount);
            if (c) return c;
            // PHP throws here when `push_args_indented` cannot wrap the last arg; for real lemmas the
            // last node is often `Lean_lemma` (not Token/Parenthesis). Fall through like the
            // same-indent branch so parsing can continue (proof lines, etc.).
        }
        for (let k = 0; k < newlineCount; ++k) {
            caret = new LeanCaret(indent, caret.level);
            this.push(caret);
        }
        return caret;
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    insert_tactic(caret, token) {
        return super.insert_tactic(caret, token);
    }

    /**
     * Port of `LeanModule::insert`.
     * @param {LeanCaret} caret
     * @param {string | typeof Lean} func class name or constructor
     */
    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.push(new Ctor(caret, this.indent, caret.level));
            return caret;
        }
        return caret;
    }

    insert_left(caret, func, prevToken) {
        return caret.push_left(func, prevToken);
    }

    insert_colon(caret) {
        return caret.push_binary('LeanColon');
    }

    // insert_comma, push_right, insert_if, insert_calc, push_line_comment, etc. inherit from `Lean`.
}

/**
 * Port of `Lean_def`. Used by `LeanCaret::append` (3-arg) and
 * `LeanCaret::push_accessibility` (4-arg).
 */
export class Lean_def extends LeanArgs {
    get stack_priority() {
        return 7;
    }

    get operator() {
        return 'def';
    }

    /**
     * @param {string|Lean} accessibility
     * @param {Lean|number} name
     * @param {number} [indent]
     * @param {number} [level]
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(accessibility, name, indent, level, parent = null) {
        if (level === null || level === undefined) {
            indent = /** @type {number} */ (name);
            name = /** @type {Lean} */ (accessibility);
            accessibility = 'public';
            level = name instanceof Lean ? name.level : 0;
        }
        super([name], indent, level, parent);
        this.args.unshift(null);
        this.kwargs.accessibility = accessibility;
    }

    get accessibility() {
        return this.kwargs.accessibility;
    }

    set accessibility(v) {
        this.kwargs.accessibility = v;
    }

    get attribute() {
        return this.args[0];
    }

    set attribute(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get assignment() {
        return this.args[1];
    }

    set assignment(v) {
        this.args[1] = v;
        if (v) v.parent = this;
    }

    /** PHP `Lean_def::strArgs`. */
    strArgs() {
        const [attr, assignment] = this.args;
        if (attr == null) return [assignment];
        return this.args;
    }

    /** PHP `Lean_def::strFormat`: uses `func` (def / theorem / lemma). */
    strFormat() {
        const acc = this.accessibility === 'public' ? '' : `${this.accessibility} `;
        let def = `${acc}${this.func} %s`;
        if (this.attribute) def = `%s\n${def}`;
        return def;
    }

    /** PHP `Lean_def::latexFormat`. */
    latexFormat() {
        return this.strFormat();
    }

    /** PHP `Lean_def::jsonSerialize`: key is `operator` (`'def'`), not `func`. */
    jsonSerialize() {
        const json = {
            [this.operator]: super.jsonSerialize(),
            accessibility: this.accessibility,
        };
        if (this.attribute) json.attribute = this.attribute.jsonSerialize?.() ?? this.attribute;
        return json;
    }

    /** PHP `Lean_def::insert_tactic`. */
    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    /** PHP `Lean_def::is_indented`. */
    is_indented() {
        return false;
    }

    /** PHP `Lean_def::set_line`. */
    set_line(line) {
        this.line = line;
        let L = line;
        const attr = this.attribute;
        if (attr) L = attr.set_line(L) + 1;
        return this.assignment.set_line(L);
    }

    /** PHP `Lean_def::relocate_last_comment`. */
    relocate_last_comment() {
        const assignment = this.assignment;
        if (assignment instanceof LeanAssign) assignment.relocate_last_comment();
    }

    /**
     * Port of `Lean_def::insert_newline`.
     * Stops indented proof lines from bubbling to `LeanModule` (which would throw).
     */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent < indent) {
            if (caret === this.assignment) {
                const pushed = this.push_args_indented(indent, newlineCount);
                if (pushed) return pushed;
                if (caret instanceof LeanColon) {
                    const rhs = caret.rhs;
                    if (rhs instanceof LeanCaret) {
                        rhs.indent = indent;
                        const stmts = new LeanStatements([rhs], indent, rhs.level);
                        caret.replace(rhs, stmts);
                        return rhs;
                    }
                } else if (caret instanceof LeanAssign) {
                    const inner = this.assignment.rhs;
                    if (inner instanceof LeanCaret) {
                        inner.indent = indent;
                        const stmts = new LeanStatements([inner], indent, inner.level);
                        this.assignment.replace(inner, stmts);
                        return inner;
                    }
                    return super.insert_newline(caret, newlineCount, this.indent, next);
                }
            }
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
}

export class Lean_theorem extends Lean_def {}

export class Lean_lemma extends Lean_def {
    /** PHP `Lean_lemma::echo`. */
    echo() {
        this.assignment?.echo?.();
        const asn = this.assignment;
        if (asn instanceof LeanAssign && asn.rhs instanceof LeanBy) {
            const statement = asn.rhs.arg;
            if (statement instanceof LeanStatements) {
                const stmts = statement.args;
                for (let i = stmts.length - 1; i >= 0; i--) {
                    const stmt = stmts[i];
                    if (stmt.is_comment?.()) continue;
                    if (stmt instanceof LeanTactic || stmt instanceof Lean_let) {
                        const token = stmt.get_echo_token?.();
                        if (token) {
                            const ind = statement.indent;
                            const lev = statement.level;
                            statement.push(
                                new LeanTactic(
                                    'try',
                                    new LeanTactic('echo', token, ind, lev),
                                    ind,
                                    lev,
                                ),
                            );
                        }
                        break;
                    }
                }
            }
        }
    }
}

export class LeanCaret extends Lean {
    static input_priority = 100;

    append(New, _func) {
        if (typeof New === 'string') {
            const Ctor = getLeanClass(New);
            this.parent.replace(this, new Ctor(this, this.indent, this.level));
            return this;
        }
        this.parent.replace(this, New);
        return New;
    }

    is_indented() {
        return this.parent instanceof LeanArgsNewLineSeparated;
    }

    is_outsider() {
        return true;
    }

    jsonSerialize() {
        return '';
    }

    /** PHP `LeanCaret` participates in `Lean::toString` as empty text. */
    strFormat() {
        return '';
    }

    strArgs() {
        return [];
    }

    latexFormat() {
        return '';
    }

    /**
     * Empty slot; `Lean.toString` would still apply `__toString`-style indent when `is_indented`, which
     * injects spaces into `strFormat` holes and breaks round-trip. PHP effectively omits caret text.
     */
    toString() {
        return '';
    }

    push_accessibility(New, accessibility) {
        this.parent.replace(this, new (getLeanClass(New))(accessibility, this, this.indent, this.level));
        return this;
    }

    push_block_comment(comment, docstring) {
        const parent = this.parent;
        const Cls = docstring ? LeanDocString : LeanBlockComment;
        parent.replace(this, new Cls(comment, this.indent, this.level));
        parent.push(this);
        return this;
    }

    /** Port of LeanCaret::push_left — simpler than Lean::push_left. */
    push_left(func, _prevToken) {
        const Ctor = getLeanClass(func);
        this.parent.replace(this, new Ctor(this, this.indent, this.level));
        return this;
    }

    push_line_comment(comment) {
        const parent = this.parent;
        const line = new LeanLineComment(comment, this.indent, this.level);
        parent.replace(this, line);
        return line;
    }

    /** PHP does not define this on LeanCaret; delegate so `case "'"` can finish (see LeanToken::push_quote). */
    push_quote(token) {
        if (this.parent) return this.parent.insert_word(this, token);
        throw new Error('push_quote: no parent');
    }

    /** Same spacing behavior as `LeanToken::push_token` when building word sequences from a caret. */
    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    strFormat() {
        return '';
    }
}

/** Top-level commands (`import` / `open` / `set_option` / `namespace`): `stack_priority` 27 except `namespace` (inherits unary 47). */
class LeanCommand extends LeanUnary {
    get command() {
        return this.operator;
    }

    is_indented() {
        return false;
    }

    jsonSerialize() {
        const inner = this.arg?.jsonSerialize?.() ?? this.arg;
        return { [this.func]: inner };
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}

/** `fun` (λ-style binder head). */
class Lean_fun extends LeanUnary {
    static input_priority = 18;
    get operator() {
        return 'fun';
    }
    get command() {
        return '\\lambda';
    }
    is_indented() {
        const p = this.parent;
        return p instanceof LeanArgsNewLineSeparated || p instanceof LeanStatements;
    }
    jsonSerialize() {
        const inner = this.arg?.jsonSerialize?.() ?? this.arg;
        return { [this.operator]: inner };
    }
    latexFormat() {
        return `${this.command}\\ %s`;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP `Lean_match`. */
class Lean_match extends LeanArgs {
    /**
     * @param {Lean} subject
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(subject, indent, level, parent = null) {
        super([subject], indent, level, parent);
    }

    get stack_priority() {
        return LeanColon.input_priority - 1;
    }

    get subject() {
        return this.args[0];
    }
    set subject(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get with() {
        return this.args[1] ?? null;
    }
    set with(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    get operator() {
        return 'match';
    }

    is_indented() {
        return true;
    }

    strFormat() {
        if (this.with) return `${this.operator} %s %s`;
        return `${this.operator} %s`;
    }

    latexFormat() {
        if (this.with) {
            const n = this.with.args.length;
            const cases = Array(n).fill('%s').join('\\\\');
            return `\\begin{cases} ${cases} \\end{cases}`;
        }
        return 'match\\ %s';
    }

    /**
     * PHP `Lean_match::latexArgs`.
     * @param {Record<string, unknown>} [syntax]
     */
    latexArgs(syntax) {
        const subject = this.subject.toLatex(syntax);
        const w = this.with;
        if (w) {
            return w.args.map((row) => {
                const a = row.arg;
                const type = a.lhs.toLatex(syntax);
                const value = a.rhs.toLatex(syntax);
                return `{${value}} & {\\color{blue}\\text{if}}\\ \\: ${subject}\\ =\\ ${type}`;
            });
        }
        return [subject];
    }

    insert(caret, func, _type) {
        if (!this.with && func === 'LeanWith') {
            const c = new LeanCaret(this.indent, caret.level);
            const Ctor = getLeanClass(func);
            const w = new Ctor(c, this.indent, c.level);
            this.with = w;
            return c;
        }
        throw new Error(`Lean_match.insert: unexpected for ${String(func)}`);
    }

    insert_comma(caret) {
        if (caret === this.subject) {
            const c = new LeanCaret(this.indent, caret.level);
            this.subject = new LeanArgsCommaSeparated([this.subject, c], this.indent, caret.level);
            return c;
        }
        if (this.parent) return this.parent.insert_comma(this);
    }

    relocate_last_comment() {
        const w = this.with;
        if (w instanceof LeanWith) w.relocate_last_comment();
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    /**
     * PHP `Lean_match::split`; clone via `this.clone()` / `LeanArgs::__clone`.
     * @param {Record<string, unknown>} [syntax]
     */
    split(syntax) {
        const w = this.with;
        if (!w) return [this];
        const self = this.clone();
        if (self.with) self.with.args = [];
        const statements = [self];
        for (const stmt of w.args) {
            statements.push(...stmt.split(syntax));
        }
        return statements;
    }

    isProp(vars) {
        const w = this.with;
        if (!w) return undefined;
        const cases = w.args;
        const first = cases[0];
        if (first instanceof LeanBar) {
            const arrow = first.arg;
            if (arrow instanceof LeanRightarrow) {
                return arrow.rhs.isProp(vars);
            }
        }
        return undefined;
    }
}

/** PHP `LeanWith`. */
class LeanWith extends LeanArgs {
    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    is_indented() {
        return false;
    }

    get stack_priority() {
        return this.parent instanceof Lean_match ? 23 : 17;
    }

    get operator() {
        return 'with';
    }
    get command() {
        return 'with';
    }

    sep() {
        if (this.args.length > 1) return '\n';
        if (!this.args.length) return '';
        const [caret] = this.args;
        return caret instanceof LeanCaret || caret.tokens_space_separated() || caret instanceof LeanBitOr ? ' ' : '\n';
    }

    strFormat() {
        const s = this.sep();
        return `${this.operator}${s}${Array(this.args.length).fill('%s').join('\n')}`;
    }

    relocate_last_comment() {
        const a = this.args[this.args.length - 1];
        a?.relocate_last_comment?.();
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        const cases = this.args;
        if (cases.length > 0) {
            let c = cases[cases.length - 1];
            if (c instanceof LeanCaret) return c;
            if (next === '|') {
                if (c instanceof LeanBar || c.is_comment()) {
                    const nc = new LeanCaret(this.indent, c.level);
                    this.push(nc);
                    return nc;
                }
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_bar(caret, prevToken, next) {
        const cases = this.args;
        const last = cases[cases.length - 1];
        if (last === caret) {
            if (caret instanceof LeanCaret) {
                this.replace(caret, new LeanBar(caret, this.indent, caret.level));
                return caret;
            }
            const new_ = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanBitOr(caret, new_, this.indent, caret.level));
            return new_;
        }
        throw new Error(`LeanWith.insert_bar: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    insert_comma(caret) {
        if (caret === this.args[this.args.length - 1]) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanArgsCommaSeparated([caret, new_], this.indent, caret.level));
            return new_;
        }
        throw new Error(`LeanWith.insert_comma: unexpected for ${this.constructor.name}`);
    }

    set_line(line) {
        this.line = line;
        if (this.sep() === '\n') line++;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }

    tokens_bar_separated() {
        if (this.args.length === 1 && this.args[0] instanceof LeanBitOr) {
            return this.args[0].tokens_bar_separated();
        }
        return [];
    }

    unique_token(indent) {
        if (this.args.length === 1) {
            const stmt = this.args[0];
            if (stmt instanceof LeanBitOr || stmt instanceof LeanArgsSpaceSeparated) {
                return stmt.unique_token(indent);
            }
        }
        return undefined;
    }

    tokens_space_separated() {
        if (this.args.length === 1 && this.args[0] instanceof LeanArgsSpaceSeparated) {
            return this.args[0].tokens_space_separated();
        }
        return [];
    }
}

/** Port of `LeanBigOperator`. */
class LeanBigOperator extends LeanArgs {
    /**
     * @param {Lean} bound
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(bound, indent, level, parent = null) {
        super([bound], indent, level, parent);
    }

    get bound() {
        return this.args[0];
    }
    set bound(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get scope() {
        return this.args[1] ?? null;
    }
    set scope(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    get stack_priority() {
        return LeanColon.input_priority - 1;
    }

    is_indented() {
        const p = this.parent;
        return p instanceof LeanStatements || p instanceof LeanIte;
    }

    strFormat() {
        const op = this.operator;
        if (this.args.length === 1) return `${op} %s,`;
        return `${op} %s, %s`;
    }

    latexFormat() {
        const cmd = this.command;
        return `${cmd}\\limits_{\\substack{%s}} {%s}`;
    }

    /** PHP `LeanBigOperator::jsonSerialize`: `{ [func]: parent::jsonSerialize() }`. */
    jsonSerialize() {
        return {
            [this.func]: super.jsonSerialize(),
        };
    }

    insert_comma(caret) {
        if (caret === this.bound) {
            const c = new LeanCaret(this.indent, caret.level);
            this.scope = c;
            return c;
        }
        throw new Error(`${this.constructor.name}.insert_comma: unexpected`);
    }

    insert_if(caret) {
        if (this.scope === caret && caret instanceof LeanCaret) {
            this.scope = new LeanIte([caret], caret.indent, caret.level);
            return caret;
        }
        throw new Error(`${this.constructor.name}.insert_if: unexpected`);
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.scope) {
            const pushed = this.push_args_indented(this.indent + 2, newlineCount);
            if (pushed) return pushed;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
}

/** Port of `LeanQuantifier`. */
class LeanQuantifier extends LeanBigOperator {
    static input_priority = 24;

    isProp(_vars) {
        return true;
    }

    latexFormat() {
        const cmd = this.command;
        if (this.args.length === 1) return `${cmd}\\ {%s},`;
        return `${cmd}\\ {%s}, {%s}`;
    }
}

class Lean_forall extends LeanQuantifier {
    get operator() {
        return '∀';
    }
}

class Lean_exists extends LeanQuantifier {
    get operator() {
        return '∃';
    }
}

class Lean_sum extends LeanBigOperator {
    static input_priority = 67;
    get operator() {
        return '∑';
    }
}

class Lean_prod extends LeanBigOperator {
    static input_priority = 67;
    get operator() {
        return '∏';
    }
}

class Lean_bigcap extends LeanBigOperator {
    static input_priority = 60;
    get operator() {
        return '⋂';
    }
}

class Lean_bigcup extends LeanBigOperator {
    static input_priority = 60;
    get operator() {
        return '⋃';
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

    append(func, _type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = getLeanClass(func);
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, new_, this.indent, caret.level);
            return new_;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** `open %s`. */
class Lean_open extends LeanCommand {
    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'open';
    }

    append(func, _type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = getLeanClass(func);
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, new_, this.indent, caret.level);
            return new_;
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

    append(func, _type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = getLeanClass(func);
        const level = this.arg.level;
        const c = new LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    /** Proof echo: scale `maxHeartbeats` token value (×5). */
    echo() {
        const arg = this.arg;
        if (arg instanceof LeanArgsSpaceSeparated && arg.args.length === 2) {
            const [a0, a1] = arg.args;
            if (a0 instanceof LeanToken && a1 instanceof LeanToken && a0.text === 'maxHeartbeats') {
                a1.text = String(parseInt(a1.text, 10) * 5);
            }
        }
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, new_, this.indent, caret.level);
            return new_;
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

/**
 * PHP `escape_specials`.
 * Escapes underscores in identifiers: single-char prefix → subscript (e.g. d_z → d_{z}),
 * multi-char → literal underscore (e.g. band_part → band\_part).
 * @param {string} token
 * @returns {string}
 */
function escapeSpecialsForLatex(token) {
    const s = String(token);
    const m = /^(\w+?)_(.+)$/.exec(s);
    if (m) {
        const [, head, tail] = m;
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        return head.length === 1 ? `${head}_{${escTail}}` : `${head}\\_${escTail}`;
    }
    // Handle identifiers ending with underscore, e.g. `h_`.
    if (/\w_$/.test(s)) return s.slice(0, -1) + '\\_';
    return s;
}

export class LeanToken extends Lean {
    static input_priority = 90;

    /**
     * @param {string} text
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(text, indent, level, parent = null) {
        super(indent, level, parent);
        this.text = text;
        /** @type {Record<string, unknown> | null} */
        this.cache = null;
    }

    clone() {
        const copy = super.clone();
        copy.cache = null;
        return copy;
    }

    append(New, func) {
        if (this.parent) return this.parent.insert(this, New, func);
    }

    ends_with_2_letters() {
        return /[a-zA-Z]{2,}$/.test(this.text);
    }

    equals(other) {
        return other instanceof LeanToken && this.text === other.text;
    }

    is_parallel_operator() {
        return /_\?+$/.test(this.text);
    }

    isProp(vars) {
        return (vars?.[this.text] ?? null) === 'Prop';
    }

    is_TypeStar() {
        return this.text === 'Sort' || this.text === 'Type' || this.text === 'ℝ';
    }

    is_variable() {
        return /^[a-zA-Z_][a-zA-Z_0-9]*$/.test(this.text);
    }

    jsonSerialize() {
        return this.text;
    }

    latexFormat() {
        return '%s';
    }

    latexArgs() {
        return [this.text];
    }

    /**
     * Identifier LaTeX: backslash-escape then `escapeSpecialsForLatex` (sub/superscripts).
     * @param {Record<string, unknown>} [_syntax]
     */
    toLatex(_syntax) {
        const backslashEscaped = this.text.replace(/\\/g, '\\textbackslash ');
        return escapeSpecialsForLatex(backslashEscaped);
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
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
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
        if (!this.cache) this.cache = {};
        const map = { 0: [this] };
        this.cache.size = 1;
        return map;
    }

    tokens_space_separated() {
        return [this];
    }

    /**
     * `--` after an identifier: keep the token and append the comment (e.g. `intro x -- note`).
     * Replacing the token used to drop the binder and break round-trip.
     */
    push_line_comment(comment) {
        const parent = this.parent;
        if (!parent) throw new Error(`push_line_comment: no parent for LeanToken`);
        const line = new LeanLineComment(comment, this.indent, this.level);
        if (parent instanceof LeanArgsSpaceSeparated) {
            const i = parent.args.indexOf(this);
            if (i >= 0) {
                parent.args.splice(i + 1, 0, line);
                line.parent = parent;
                return line;
            }
        }
        parent.replace(this, line);
        return line;
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
        const t = this.text;
        if (t === 'given') {
            let parent = this.parent;
            if (
                parent instanceof LeanArgsNewLineSeparated &&
                (parent = parent.parent) instanceof LeanArgsIndented &&
                (parent = parent.parent) instanceof LeanColon &&
                (parent = parent.parent) instanceof LeanAssign &&
                parent.parent instanceof Lean_lemma
            ) {
                return false;
            }
            if (this.parent instanceof LeanModule) {
                const mod = this.parent;
                const ix = mod.args.indexOf(this);
                if (ix > 0 && mod.args[ix - 1] instanceof Lean_lemma) return false;
            }
            return true;
        }
        if (t === 'proof') {
            let parent = this.parent;
            if (parent instanceof LeanStatements) {
                if (parent.parent instanceof LeanBy) parent = parent.parent;
                if (
                    (parent = parent.parent) instanceof LeanAssign &&
                    parent.parent instanceof Lean_lemma
                ) {
                    return false;
                }
            } else if (parent instanceof LeanArgsNewLineSeparated) {
                if (
                    (parent = parent.parent) instanceof LeanAssign &&
                    parent.parent instanceof Lean_lemma
                ) {
                    return false;
                }
            }
        }
        if (t === 'imply' || t === 'proof') {
            let parent = this.parent;
            if (
                parent instanceof LeanStatements &&
                (parent = parent.parent) instanceof LeanColon &&
                (parent = parent.parent) instanceof LeanAssign &&
                parent.parent instanceof Lean_lemma
            ) {
                return false;
            }
            // `lemma` + sibling layout: `Colon` may sit under `LeanAssign` (parent `LeanModule`, not `Lean_lemma`)
            // or directly under `LeanModule` after `Lean_lemma`.
            if (t === 'imply' && this.parent instanceof LeanStatements) {
                const colon = this.parent.parent;
                if (colon instanceof LeanColon) {
                    const holder = colon.parent;
                    if (holder instanceof LeanModule) {
                        const mod = holder;
                        const ix = mod.args.indexOf(colon);
                        if (ix >= 0) {
                            for (let j = 0; j < ix; j++) {
                                if (mod.args[j] instanceof Lean_lemma) return false;
                            }
                        }
                    } else if (holder instanceof LeanAssign && holder.parent instanceof LeanModule) {
                        const mod = holder.parent;
                        const ix = mod.args.indexOf(holder);
                        if (ix >= 0) {
                            for (let j = 0; j < ix; j++) {
                                if (mod.args[j] instanceof Lean_lemma) return false;
                            }
                        }
                    }
                }
            }
            // Echo-style proof header: `-- proof` as its own module line after `… :=`.
            if (t === 'proof' && this.parent instanceof LeanModule) {
                const mod = this.parent;
                const ix = mod.args.indexOf(this);
                if (ix > 0 && mod.args[ix - 1] instanceof LeanAssign) return false;
            }
        } else if (this.parent instanceof LeanTactic) {
            return false;
        }
        return true;
    }

    is_outsider() {
        return /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.test(this.text);
    }

    /**
     * `%` starts a LaTeX comment; structural markers (`imply`, `given`, `proof`) would truncate output.
     */
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

export class LeanGetElem extends LeanBinary {
    static input_priority = 88;

    /** PHP LeanGetElemBaseBinary::stack_priority 18. Keeps slice `:` and binary ops inside the index. */
    get stack_priority() {
        return 18;
    }

    /** PHP `LeanGetElemBase::push_right`. Absorb `]` so it closes the index bracket, not an outer LeanBracket. */
    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    /** PHP `LeanGetElemBase::insert_comma`. Create comma-separated index e.g. A[i, j]. */
    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    /** PHP `LeanGetElemBaseBinary::sep`. */
    sep() {
        return '';
    }

    /** PHP `LeanGetElem::strFormat`: `A[i,j]`. */
    strFormat() {
        return '%s[%s]';
    }

    /** PHP `LeanGetElem::latexFormat`: subscript. */
    latexFormat() {
        return '{%s}_{%s}';
    }
}

export class LeanGetElemQue extends LeanBinary {
    static input_priority = 88;

    /** PHP LeanGetElemBaseBinary::stack_priority 18. */
    get stack_priority() {
        return 18;
    }

    /** PHP `LeanGetElemBase::push_right` — absorb `]` for index. */
    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    /** PHP `LeanGetElemBase::insert_comma`. */
    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    /** PHP `LeanGetElemBaseBinary::sep`. */
    sep() {
        return '';
    }

    /** PHP `LeanGetElemQue::strFormat`. */
    strFormat() {
        return '%s[%s]?';
    }

    /** PHP `LeanGetElemQue::latexFormat`. */
    latexFormat() {
        return '{%s}_{%s?}';
    }
}

export class LeanGetElemQuote extends LeanArgs {
    static input_priority = 88;

    /** PHP LeanGetElemBaseBinary::stack_priority 18. */
    get stack_priority() {
        return 18;
    }

    /** PHP `LeanGetElemBase::push_right` — absorb `]` for index. */
    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    /** PHP `LeanGetElemQuote::strFormat`. */
    strFormat() {
        return "%s[%s]'%s";
    }
}

/**
 * PHP `LeanStack` extends `LeanBigOperator`. `[i < n] body` notation.
 */
class LeanStack extends LeanBigOperator {
    static input_priority = 52;

    get operator() {
        return 'Stack';
    }

    get command() {
        return 'Stack';
    }

    /** PHP `LeanStack::__get('stack_priority')`. */
    get stack_priority() {
        return 28;
    }

    /** PHP `LeanStack::latexArgs`. */
    latexArgs(syntax) {
        const s = syntax ?? {};
        s[this.constructor.name] = true;
        return super.latexArgs(s);
    }

    latexFormat() {
        return '\\left[{%s}\\right]{%s}';
    }

    /** PHP `LeanStack::push_args_indented`: no-op. */
    push_args_indented(_indent, _newlineCount, _functionCall = true) {}

    strFormat() {
        return '[%s] %s';
    }
}

/**
 * Port of LeanBracket::push_right. When [i < n] pattern, replace with LeanStack.
 */
class LeanBracket extends LeanPairedGroup {
    push_right(funcName) {
        if (funcName === 'LeanBracket') {
            const lt = this.arg;
            // arg can be Lean_lt (i < n) or LeanArgsSpaceSeparated e.g. ( LeanToken, Lean_lt ) from push_left
            let bound = lt;
            if (lt instanceof LeanArgsSpaceSeparated && lt.args.length >= 2) {
                const last = lt.args[lt.args.length - 1];
                if (last?.constructor?.name === 'Lean_lt' && last.lhs instanceof LeanToken) bound = last;
            }
            const ok = bound && bound.constructor?.name === 'Lean_lt' && bound.lhs instanceof LeanToken;
            if (ok) {
                const scope = new LeanCaret(this.indent, this.level);
                const stack = new LeanStack(bound, this.indent, this.level);
                stack.scope = scope;
                this.parent.replace(this, stack);
                return scope;
            }
        }
        return super.push_right(funcName);
    }

    latexFormat() {
        return '\\left[ {%s} \\right]';
    }

    toString() {
        const s = super.toString();
        const ind = this.indent ?? 0;
        if (ind > 0 && this.parent?.constructor?.name === 'LeanModule') return ' '.repeat(ind) + s;
        return s;
    }
}

/** PHP `LeanBrace`. */
class LeanBrace extends LeanPairedGroup {
    is_Expr() {
        return false;
    }
    get stack_priority() {
        return 17;
    }
    get operator() {
        return '{}';
    }
    latexFormat() {
        return '\\left\\{ {%s} \\right\\}';
    }
}

/** PHP `LeanAngleBracket`. */
class LeanAngleBracket extends LeanPairedGroup {
    get stack_priority() {
        return 10;
    }
    get operator() {
        return ['⟨', '⟩'];
    }
    latexFormat() {
        return '\\langle {%s} \\rangle';
    }

    /** PHP `LeanAngleBracket::tokens_comma_separated`. */
    tokens_comma_separated() {
        const a = this.arg;
        if (a instanceof LeanArgsCommaSeparated) return a.tokens_comma_separated();
        return [a];
    }
}

/** PHP `LeanAbs`. */
class LeanAbs extends LeanPairedGroup {
    get stack_priority() {
        return 17;
    }
    get operator() {
        return '||';
    }
    latexFormat() {
        return '\\left| {%s} \\right|';
    }
}

/** PHP `LeanNorm`. */
class LeanNorm extends LeanPairedGroup {
    get stack_priority() {
        return 17;
    }
    get operator() {
        return ['‖', '‖'];
    }
    latexFormat() {
        return '\\left\\lVert {%s} \\right\\rVert';
    }
}

/** PHP `LeanCeil`. */
class LeanCeil extends LeanPairedGroup {
    static input_priority = 72;
    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['⌈', '⌉'];
    }
    latexFormat() {
        return '\\left\\lceil {%s} \\right\\rceil';
    }
}

/** PHP `LeanFloor`. */
class LeanFloor extends LeanPairedGroup {
    static input_priority = 72;
    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['⌊', '⌋'];
    }
    latexFormat() {
        return '\\left\\lfloor {%s} \\right\\rfloor';
    }
}

/** PHP `LeanDoubleAngleQuotation`. */
class LeanDoubleAngleQuotation extends LeanPairedGroup {
    is_Expr() {
        return false;
    }
    get stack_priority() {
        return 22;
    }
    get operator() {
        return ['«', '»'];
    }
    latexFormat() {
        return '\\left\\langle{%s}\\right\\rangle'; // «» guillemets
    }
}

/** PHP `LeanUsing`: tactic modifier `using`. */
class LeanUsing extends LeanUnary {
    is_indented() {
        return false;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
    latexFormat() {
        return `${this.command} %s`;
    }
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            this.arg = new LeanStatements([caret], ind, caret.level);
            for (let i = 1; i < newlineCount; i++) {
                caret = new LeanCaret(ind, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
    get operator() {
        return 'using';
    }
    get command() {
        return 'using';
    }
}

/** PHP `LeanFrom`. */
class LeanFrom extends LeanUnary {
    is_indented() {
        return this.parent instanceof LeanArgsCommaNewLineSeparated;
    }
    sep() {
        return this.arg instanceof LeanStatements ? '\n' : ' ';
    }
    strFormat() {
        const s = this.sep();
        return `${this.operator}${s}%s`;
    }
    latexFormat() {
        const s = this.sep();
        return `${this.command}${s}%s`;
    }
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            this.arg = new LeanStatements([caret], ind, caret.level);
            for (let i = 1; i < newlineCount; i++) {
                caret = new LeanCaret(ind, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
    relocate_last_comment() {
        this.arg.relocate_last_comment();
    }
    echo() {
        this.arg.echo?.();
    }
    set_line(line) {
        this.line = line;
        let L = line;
        if (this.arg instanceof LeanStatements) L++;
        return this.arg.set_line(L);
    }
    get operator() {
        return 'from';
    }
    get command() {
        return 'from';
    }
}

/** PHP `LeanCalc`. */
class LeanCalc extends LeanUnary {
    is_indented() {
        const p = this.parent;
        return !p || p instanceof LeanStatements || p instanceof LeanIte;
    }

    sep() {
        return this.arg instanceof LeanArgsNewLineSeparated ? '\n' : ' ';
    }

    strFormat() {
        const s = this.sep();
        return `${this.operator}${s}%s`;
    }

    latexFormat() {
        const s = this.sep();
        return `${this.command}${s}%s`;
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret === this.arg) {
            if (caret instanceof LeanCaret) {
                let ind = indent;
                if (ind === this.indent) ind = this.indent + 2;
                caret.indent = ind;
                const nl = new LeanArgsNewLineSeparated([caret], ind, caret.level);
                this.replace(caret, nl);
                return nl.push_newlines(newlineCount - 1);
            }
            if (caret instanceof LeanAssign) {
                const new_ = this.push_args_indented(indent, newlineCount, false);
                if (new_) return new_;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    relocate_last_comment() {
        this.arg.relocate_last_comment();
    }

    get operator() {
        return 'calc';
    }

    get command() {
        return 'calc';
    }

    get stack_priority() {
        return LeanAssign.input_priority - 1;
    }

    set_line(line) {
        this.line = line;
        let L = line;
        if (this.arg instanceof LeanArgsNewLineSeparated) L++;
        return this.arg.set_line(L);
    }

    echo() {
        const arg = this.arg;
        if (arg instanceof LeanArgsNewLineSeparated) {
            for (const stmt of arg.args) stmt.echo?.();
        }
    }

    /**
     * PHP `LeanCalc::split`: `clone $this` then detach body;
     * must use deep `clone()` so `this.args` is not shared with the original (see `LeanBar.split`).
     * @param {Record<string, unknown>} [syntax]
     */
    split(syntax) {
        const arg = this.arg;
        if (arg instanceof LeanArgsNewLineSeparated) {
            if (syntax && typeof syntax === 'object') syntax.calc = true;
            const self = this.clone();
            const stmts = /** @type {LeanArgsNewLineSeparated} */ (self.arg).args;
            self.arg = new LeanCaret(this.indent, this.level);
            const statements = [self];
            for (const stmt of stmts) statements.push(...stmt.split(syntax));
            return statements;
        }
        if (arg instanceof LeanArgsIndented) {
            if (syntax && typeof syntax === 'object') syntax.calc = true;
            const self = this.clone();
            const a = /** @type {LeanArgsIndented} */ (self.arg);
            const content = a.rhs;
            a.rhs = new LeanCaret(content.indent, content.level);
            const statements = [self];
            statements.push(...content.split(syntax));
            return statements;
        }
        return [this];
    }
}

/** PHP `LeanMOD`. */
class LeanMOD extends LeanUnary {
    is_indented() {
        return false;
    }
    sep() {
        return ' ';
    }
    strFormat() {
        const s = this.sep();
        return `${this.operator}${s}%s`;
    }
    latexFormat() {
        const s = this.sep();
        return `${this.command}\\${s}%s`;
    }
    get operator() {
        return 'MOD';
    }
    get command() {
        return '\\operatorname{MOD}';
    }
}

/** PHP `LeanGeneralizing`. */
class LeanGeneralizing extends LeanUnary {
    is_indented() {
        return false;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
    latexFormat() {
        return `${this.command} %s`;
    }
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            this.arg = new LeanStatements([caret], ind, caret.level);
            for (let i = 1; i < newlineCount; i++) {
                caret = new LeanCaret(ind, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
    get operator() {
        return 'generalizing';
    }
    get command() {
        return 'generalizing';
    }
}

/** PHP `LeanIn`: tactic modifier `in` (not `Lean_in` ∈). */
class LeanIn extends LeanUnary {
    is_indented() {
        return false;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
    latexFormat() {
        return `${this.command} %s`;
    }
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            let ind = indent;
            if (ind === this.indent) ind = this.indent + 2;
            caret.indent = ind;
            this.arg = new LeanStatements([caret], ind, caret.level);
            for (let i = 1; i < newlineCount; i++) {
                caret = new LeanCaret(ind, caret.level);
                this.arg.push(caret);
            }
            return caret;
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }
    get stack_priority() {
        return 18;
    }
    get operator() {
        return 'in';
    }
    get command() {
        return 'in';
    }
}

/** PHP LeanAt extends LeanUnary: modifier "at %s". */
export class LeanAt extends LeanUnary {
    get operator() {
        return 'at';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP `LeanTacticBlock`; method order README Step 3 §2 (alphabetic). */
class LeanTacticBlock extends LeanUnary {
    get command() {
        return '\\cdot';
    }

    get operator() {
        return '·';
    }

    insert_line_comment(caret, comment) {
        if (caret instanceof LeanCaret) {
            const ind = this.indent + 2;
            const line = new LeanLineComment(comment, ind, caret.level);
            this.arg = new LeanStatements([line], ind, caret.level);
            return line;
        }
        throw new Error('LeanTacticBlock.insert_line_comment: unexpected');
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.arg) {
            if (caret instanceof LeanCaret) {
                if (this.indent <= indent) {
                    let ind = indent;
                    if (ind === this.indent) ind = this.indent + 2;
                    caret.indent = ind;
                    const stmts = new LeanStatements([caret], ind, caret.level);
                    this.arg = stmts;
                    let last = caret;
                    for (let i = 1; i < newlineCount; i++) {
                        last = new LeanCaret(ind, caret.level);
                        stmts.push(last);
                    }
                    return last;
                }
            } else if (caret instanceof LeanStatements) {
                const block = caret;
                if (indent >= block.indent) {
                    let last = /** @type {LeanCaret | null} */ (null);
                    for (let i = 0; i < newlineCount; i++) {
                        last = new LeanCaret(block.indent, block.level);
                        block.push(last);
                    }
                    return last;
                }
            } else if (this.indent < indent) {
                const oldArg = this.arg;
                oldArg.indent = indent;
                const c = new LeanCaret(indent, oldArg.level);
                this.arg = new LeanStatements([oldArg, c], indent, c.level);
                return c;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    is_indented() {
        return true;
    }

    latexFormat() {
        const s = this.sep();
        return `${this.command}${s}%s`;
    }

    sep() {
        const a = this.arg;
        return a instanceof LeanStatements ? '\n' : a instanceof LeanCaret ? '' : ' ';
    }

    /** PHP `LeanTacticBlock::strFormat`. */
    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }

    /**
     * PHP `LeanTacticBlock::echo`.
     * @returns {void | (Lean | number)[]}
     */
    echo() {
        const statements = this.arg;
        if (!(statements instanceof LeanStatements)) return;
        statements.echo();
        const p = this.parent;
        if (p instanceof LeanSequentialTacticCombinator) {
            let token;
            const gp = p.parent;
            if (gp instanceof LeanTactic) {
                const w = gp.with;
                if (w) token = w.unique_token(statements.indent);
            }
            if (token == null) token = new LeanToken('⊢', statements.indent, statements.level);
            statements.unshift(new LeanTactic('echo', token, statements.indent, statements.level));
        } else if (p instanceof LeanStatements) {
            const ix = p.args.indexOf(this);
            if (ix < 0) return;
            let tacticBlockCount = 0;
            for (let i = ix - 1; i >= 0; i--) {
                const stmt = p.args[i];
                if (stmt.is_comment()) continue;
                if (stmt instanceof LeanTacticBlock) {
                    tacticBlockCount++;
                    continue;
                }
                if (stmt instanceof LeanTactic) {
                    if (stmt.tacticName === 'echo') continue;
                    const st = stmt.tacticName;
                    const indent = statements.indent;
                    const level = statements.level;
                    switch (st) {
                        case 'rcases': {
                            const w = stmt.with;
                            const tokens = w?.tokens_bar_separated?.() ?? [];
                            if (w && tokens.length) {
                                let token = tokens[tacticBlockCount];
                                if (Array.isArray(token)) {
                                    token = token.filter((t) => t.text !== 'rfl');
                                    token = token.map((t) => {
                                        const c = t.clone();
                                        c.indent = indent;
                                        c.level = level;
                                        return c;
                                    });
                                    token =
                                        token.length === 1 ? token[0] : new LeanArgsCommaSeparated(token, indent, level);
                                } else {
                                    token = token.clone();
                                    token.indent = indent;
                                    token.level = level;
                                }
                                statements.unshift(new LeanTactic('echo', token, indent, level));
                            }
                            break;
                        }
                        case "cases'": {
                            const w = stmt.with;
                            const tokens = w?.tokens_space_separated?.() ?? [];
                            if (w instanceof LeanWith && tokens.length) {
                                const token = tokens[tacticBlockCount].clone();
                                token.indent = statements.indent;
                                token.level = statements.level;
                                statements.unshift(
                                    new LeanTactic('echo', token, statements.indent, statements.level),
                                );
                            }
                            break;
                        }
                        case 'obtain': {
                            const assign = stmt.arg;
                            if (assign instanceof LeanAssign) {
                                const bitOr = assign.lhs;
                                if (bitOr instanceof LeanBitOr) {
                                    const tokens = bitOr.tokens_bar_separated();
                                    if (tokens.length) {
                                        const token = tokens[tacticBlockCount].clone();
                                        token.indent = statements.indent;
                                        token.level = statements.level;
                                        statements.unshift(
                                            new LeanTactic('echo', token, statements.indent, statements.level),
                                        );
                                    }
                                }
                            }
                            break;
                        }
                        case 'split_ifs': {
                            const w = stmt.with;
                            if (!(w instanceof LeanWith) || w.args.length !== 1) break;
                            const toks = w.args[0];
                            if (!(toks instanceof LeanArgsSpaceSeparated || toks instanceof LeanToken)) break;
                            statements.unshift(
                                new LeanTactic(
                                    'echo',
                                    new LeanToken('⊢', statements.indent, statements.level),
                                    statements.indent,
                                    statements.level,
                                ),
                            );
                            const infoMap =
                                typeof toks.tactic_block_info === 'function' ? toks.tactic_block_info() : {};
                            const tbi = infoMap[tacticBlockCount] ?? null;
                            if (tbi) {
                                const span = tbi.map((token) => {
                                    const c = token.cache;
                                    return c && typeof c.size === 'number' ? c.size : 1;
                                });
                                    let rest = p.args.slice(ix);
                                    const length = rest.length;
                                    for (let si = 0; si < span.length; si++) {
                                        const span_i = span[si];
                                        let token = tbi[si].clone();
                                        token.indent = this.indent;
                                        const stop = this.tactic_block(rest, span_i);
                                        let newList = rest.slice(0, stop);
                                        const first = newList[0];
                                        if (first instanceof LeanTactic && first.tacticName === 'echo') {
                                            if (first.arg instanceof LeanToken)
                                                first.arg = new LeanArgsCommaSeparated(
                                                    [token, first.arg],
                                                    this.indent,
                                                    token.level,
                                                );
                                            else first.arg.unshift(token);
                                        } else {
                                            newList.unshift(
                                                new LeanTactic('echo', token, this.indent, token.level),
                                            );
                                        }
                                        const last = newList[newList.length - 1];
                                        if (last instanceof LeanTactic && last.tacticName === 'echo') {
                                            if (last.arg instanceof LeanToken)
                                                last.arg = new LeanArgsCommaSeparated(
                                                    [last.arg, token],
                                                    this.indent,
                                                    token.level,
                                                );
                                            else last.arg.push(token);
                                        } else {
                                            newList.push(new LeanTactic('echo', token, this.indent, token.level));
                                        }
                                        rest = [...newList, ...rest.slice(stop)];
                                    }
                                    if (ix > 0) {
                                        const prev = p.args[ix - 1];
                                        if (prev instanceof LeanTactic && prev.tacticName === 'echo') {
                                            const first = rest.shift();
                                            if (prev.arg instanceof LeanToken) {
                                                if (first.arg instanceof LeanToken)
                                                    prev.arg = new LeanArgsCommaSeparated(
                                                        [prev.arg, first.arg],
                                                        this.indent,
                                                        prev.arg.level,
                                                    );
                                                else
                                                    prev.arg = new LeanArgsCommaSeparated(
                                                        [prev.arg, ...first.arg.args],
                                                        this.indent,
                                                        prev.arg.level,
                                                    );
                                            } else {
                                                if (first.arg instanceof LeanToken) prev.arg.push(first.arg);
                                                else for (const a of first.arg.args) prev.arg.push(a);
                                            }
                                        }
                                    }
                                    return [length, ...rest];
                            }
                            break;
                        }
                        case 'by_cases': {
                            const colon = stmt.arg;
                            if (colon instanceof LeanColon && colon.lhs instanceof LeanToken) {
                                const spaceToks = colon.lhs.tokens_space_separated?.() ?? [];
                                const token = spaceToks[tacticBlockCount];
                                if (token) {
                                    const c = token.clone();
                                    c.indent = this.indent;
                                    c.level = this.level;
                                    const echo = new LeanTactic('echo', c, this.indent, this.level);
                                    return [1, echo, this, echo.clone()];
                                }
                            }
                            break;
                        }
                        case 'split': {
                            const at = stmt.at;
                            if (at) {
                                const t = at.arg;
                                if (t instanceof LeanToken) {
                                    const c = t.clone();
                                    c.indent = statements.indent;
                                    c.level = statements.level;
                                    statements.unshift(
                                        new LeanTactic('echo', c, statements.indent, statements.level),
                                    );
                                }
                            }
                            break;
                        }
                        default: {
                            let token = new LeanToken('⊢', statements.indent, statements.level);
                            const stc = stmt.sequential_tactic_combinator;
                            if (stc) {
                                const tactic = stc.arg;
                                const tacticToken = tactic?.get_echo_token?.();
                                if (tacticToken) {
                                    if (tacticToken instanceof LeanArgsCommaSeparated) {
                                        tacticToken.push(token);
                                        token = tacticToken;
                                    } else {
                                        token = new LeanArgsCommaSeparated(
                                            [tacticToken, token],
                                            statements.indent,
                                            statements.level,
                                        );
                                    }
                                }
                            }
                            statements.unshift(new LeanTactic('echo', token, statements.indent, statements.level));
                        }
                    }
                }
                break;
            }
        }
    }

    /** PHP `LeanTacticBlock::tactic_block`. */
    tactic_block(args, span) {
        let count = 0;
        let j = 0;
        while (count < span && j < args.length) {
            if (args[j] instanceof LeanTacticBlock) count++;
            j++;
        }
        return j;
    }

    /**
     * PHP `LeanTacticBlock::split`.
     * @param {Record<string, unknown>} [syntax]
     */
    split(syntax) {
        if (this.arg instanceof LeanStatements) {
            const self = this.clone();
            const stmts = self.arg;
            self.arg = new LeanCaret(this.indent, self.arg.level);
            const statements = [self];
            stmts.swap_echo_star(syntax, statements);
            return statements;
        }
        return [this];
    }

    /** PHP `LeanTacticBlock::set_line`. */
    set_line(line) {
        this.line = line;
        if (this.arg instanceof LeanStatements) line++;
        return this.arg.set_line(line);
    }
}

/**
 * PHP `LeanSequentialTacticCombinator`: unary `·` / `<;>` combinator.
 * @extends {LeanUnary}
 */
export class LeanSequentialTacticCombinator extends LeanUnary {
    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {boolean} [newline]
     */
    constructor(arg, indent, level, newline = false) {
        super(arg, indent, level);
        /** @type {boolean} */
        this.newline = !!newline;
    }

    get operator() {
        return '<;>';
    }

    get command() {
        return '<;>';
    }

    /** @param {Record<string, unknown>} [_syntax] */
    echo() {
        let arg = this.arg;
        if (arg instanceof LeanTacticBlock) {
            arg.echo?.();
            return;
        }
        if (arg.indent > 0) {
            const indent = arg.indent;
            const level = arg.level;
            const echo = new LeanTactic('echo', new LeanToken('⊢', indent, level), indent, level);
            const parentTactic = this.parent;
            if (
                parentTactic instanceof LeanTactic &&
                parentTactic.tacticName === 'by_cases' &&
                parentTactic.has_tactic_block_followed?.()
            ) {
                let a = arg;
                let stc;
                while ((stc = a.sequential_tactic_combinator) && stc.arg?.indent) a = stc;
                a.push(new LeanSequentialTacticCombinator(echo, indent, level, true));
            } else {
                echo.push(new LeanSequentialTacticCombinator(arg, indent, level, this.newline));
                this.arg = echo;
                arg.echo?.();
            }
        }
    }

    getEcho() {
        if (this.newline) {
            const e = this.arg;
            if (e instanceof LeanTactic && e.tacticName === 'echo') return e;
        }
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret instanceof LeanCaret && caret === this.arg) {
            if (next === '·' || next === '.') {
                if (indent === this.indent) {
                    caret.indent = indent;
                    return caret;
                }
            } else {
                let ind = indent;
                if (ind > this.indent) ind = this.indent + 2;
                else ind = this.indent;
                caret.indent = ind;
                return caret;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_tactic(caret, type) {
        if (caret instanceof LeanCaret) {
            this.arg = new LeanTactic(type, caret, caret.indent, caret.level);
            return caret;
        }
        throw new Error(`LeanSequentialTacticCombinator.insert_tactic: unexpected`);
    }

    is_indented() {
        return !!this.newline;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    sep() {
        if (this.arg instanceof LeanTacticBlock) return '\n';
        // Dangling `<;>` before `·` / next tactic: newline, not a trailing space before empty caret.
        if (this.arg instanceof LeanCaret) return '\n';
        // `constructor <;>` then a more-indented `intro` / tactic on the next line (OrInS-style).
        if (this.arg instanceof LeanTactic && this.arg.indent > this.indent) return '\n';
        return this.arg.indent > 0 && !this.newline ? '\n' : ' ';
    }

    set_line(line) {
        this.line = line;
        if (this.arg instanceof LeanTacticBlock || this.arg.indent >= this.indent) line++;
        return this.arg.set_line(line);
    }

    /**
     * @param {Record<string, unknown>} [syntax]
     * @returns {Lean[]}
     */
    split(syntax) {
        if (!this.newline) return [this];
        const arg = this.arg;
        const args = arg.split(syntax);
        const self = this.clone();
        self.arg = args[0];
        args[0] = self;
        return args;
    }

    strFormat() {
        const sep = this.sep();
        return `${this.operator}${sep}%s`;
    }
}

/**
 * PHP `abstract class LeanSyntax extends LeanArgs`.
 * Defines `insert` and `__set`-style behavior for `arg` / `sequential_tactic_combinator`; `LeanTactic`, `Lean_let`, `Lean_show` extend this (not `LeanUnary`).
 */
export class LeanSyntax extends LeanArgs {
    get arg() {
        return this.args[0];
    }

    set arg(v) {
        this.args[0] = v;
        v.parent = this;
    }

    set sequential_tactic_combinator(val) {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanSequentialTacticCombinator) {
                this.args[i] = val;
                val.parent = this;
                return;
            }
        }
    }

    get sequential_tactic_combinator() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanSequentialTacticCombinator) return this.args[i];
        }
    }

    insert(caret, func, _type) {
        const last = this.args[this.args.length - 1];
        if (caret === last) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            const newCaret = new LeanCaret(this.indent, caret.level);
            this.push(new Ctor(newCaret, this.indent, caret.level));
            return newCaret;
        }
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }
}

/** PHP `Lean_let` extends `LeanSyntax`; method order README Step 3 §2 (alphabetic). */
class Lean_let extends LeanSyntax {
    static input_priority = 7;

    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    get command() {
        return 'let';
    }

    echo() {
        const token = this.get_echo_token();
        if (token) {
            const by = this.args[0]?.rhs;
            if (by instanceof LeanBy) {
                const stmt = by.arg;
                if (stmt instanceof LeanStatements) stmt.echo();
            }
            return [1, this, new LeanTactic('echo', token, this.indent, token.level)];
        }
    }

    get_echo_token() {
        const assign = this.args[0];
        if (assign instanceof LeanAssign) {
            const angleBracket = assign.lhs;
            if (angleBracket instanceof LeanAngleBracket) {
                const token = angleBracket.tokens_comma_separated();
                if (token.length === 1) return token[0];
                return new LeanArgsCommaSeparated(token, this.indent, angleBracket.level);
            }
        }
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.args[0]) {
            if (next === '<' && this.parent instanceof LeanSequentialTacticCombinator) {
                const c = new LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_sequential_tactic_combinator(caret, nextToken) {
        const last = this.args[this.args.length - 1];
        if (caret === last) {
            if (caret instanceof LeanCaret) {
                this.replace(
                    caret,
                    new LeanSequentialTacticCombinator(caret, this.indent, caret.level, nextToken !== '\n'),
                );
            } else {
                const c = new LeanCaret(0, 0);
                this.push(new LeanSequentialTacticCombinator(c, this.indent, c.level));
            }
            return caret;
        }
        throw new Error(`insert_sequential_tactic_combinator is unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return !(this.parent instanceof LeanSequentialTacticCombinator);
    }

    jsonSerialize() {
        const a0 = this.args[0];
        return {
            [this.operator]: typeof a0?.jsonSerialize === 'function' ? a0.jsonSerialize() : a0,
        };
    }

    /** PHP `Lean_let::latexFormat`. */
    latexFormat() {
        return `{\\color{#00f}${this.command}}\\ ` + Array(this.args.length).fill('%s').join('\\ ');
    }

    get operator() {
        return 'let';
    }

    /**
     * PHP `Lean_let::split`.
     * @param {Record<string, unknown>} [syntax]
     */
    split(syntax) {
        const assign = this.args[0];
        if (assign instanceof LeanAssign) {
            const by = assign.rhs;
            if (by instanceof LeanBy && by.arg instanceof LeanStatements) {
                const statements = assign.split(syntax);
                const Ctor = /** @type {typeof Lean_let} */ (this.constructor);
                statements[0] = new Ctor(statements[0], this.indent, assign.level);
                return statements;
            }
        }
        return [this];
    }

    get stack_priority() {
        return 7;
    }

    /** PHP `Lean_let::strFormat`. */
    strFormat() {
        const func = this.operator;
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof LeanCaret);
            else if (arg instanceof LeanSequentialTacticCombinator && arg.newline) parts.push('\n');
            else parts.push(' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }
}

/** PHP `Lean_have`. */
class Lean_have extends Lean_let {
    get command() {
        return 'have';
    }

    get operator() {
        return 'have';
    }

    get_echo_token() {
        const assign = this.args[0];
        if (!(assign instanceof LeanAssign)) return;
        let token = assign.lhs;
        if (token instanceof LeanColon) token = token.lhs;
        if (token instanceof LeanCaret) token = new LeanToken('this', this.indent, token.level);
        if (
            token instanceof LeanAngleBracket &&
            token.arg instanceof LeanArgsCommaSeparated &&
            token.arg.args.every((arg) => arg instanceof LeanToken)
        ) {
            token = token.arg;
        }
        if (token instanceof LeanToken || token instanceof LeanArgsCommaSeparated) return token;
    }

    sep() {
        const assign = this.args[0];
        if (assign instanceof LeanAssign) {
            const lhs = assign.lhs;
            if (lhs instanceof LeanCaret) return '';
            if (lhs instanceof LeanColon && lhs.lhs instanceof LeanCaret) return '';
        }
        return ' ';
    }

    /** PHP `Lean_have::strFormat`. */
    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }
}

/** PHP `Lean_show` extends `LeanSyntax`. */
class Lean_show extends LeanSyntax {
    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    get stack_priority() {
        return 7;
    }

    get operator() {
        return 'show';
    }

    is_indented() {
        const p = this.parent;
        return p instanceof LeanStatements || p instanceof LeanArgsNewLineSeparated;
    }

    jsonSerialize() {
        return {
            [this.operator]: super.jsonSerialize(),
        };
    }

    latexFormat() {
        const f = `{\\color{#00f}${this.func}}`;
        return `${f}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
    }

    strFormat() {
        return `${this.func} ${Array(this.args.length).fill('%s').join(' ')}`;
    }
}

export class LeanTactic extends LeanSyntax {
    /**
     * @param {string} name
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     */
    constructor(name, arg, indent, level) {
        super([arg], indent, level);
        this.tacticName = name;
        /** @type {boolean | undefined} PHP `$only` */
        this.only = undefined;
    }

    _lastOf(Cls) {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof Cls) return this.args[i];
        }
    }

    get arrow() {
        return this._lastOf(LeanRightarrow);
    }

    get at() {
        return this._lastOf(LeanAt);
    }

    get by() {
        return this._lastOf(LeanBy);
    }

    /** PHP `$this->func` */
    get func() {
        return this.tacticName;
    }

    get modifiers() {
        return this.args.slice(1);
    }

    get with() {
        return this._lastOf(LeanWith);
    }

    /** PHP `LeanTactic::is_inline_tactic_block`. */
    is_inline_tactic_block() {
        return this.tacticName === 'repeat' || this.tacticName === 'try';
    }

    /** PHP `LeanTactic::__get('stack_priority')`. */
    get stack_priority() {
        if (this.parent instanceof LeanBy) return LeanColon.input_priority;
        if (this.tacticName === 'obtain') return LeanAssign.input_priority - 1;
        return LeanAssign.input_priority;
    }

    /** PHP `LeanTactic::insert_newline`. */
    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.arg) {
            if (this.indent < indent && caret instanceof LeanArgsSpaceSeparated) {
                const new_ = new LeanCaret(this.indent, caret.level);
                caret.push(new_);
                return new_;
            }
            if (next === '<') {
                const c = new LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    /** PHP `LeanTactic::insert_comma`. */
    insert_comma(caret) {
        if (caret === this.arg) {
            if (
                caret instanceof LeanToken ||
                caret instanceof LeanBinary ||
                caret instanceof LeanPairedGroup
            ) {
                const new_ = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanArgsCommaSeparated([caret, new_], this.indent, caret.level));
                return new_;
            }
            if (caret instanceof LeanArgsCommaSeparated) {
                const new_ = new LeanCaret(this.indent, caret.level);
                caret.push(new_);
                return new_;
            }
        }
        return super.insert_comma(caret);
    }

    /** PHP `LeanTactic::insert_semicolon`. */
    insert_semicolon(caret) {
        if (caret === this.arg) {
            if (this.is_inline_tactic_block()) {
                const new_ = new LeanCaret(this.indent, caret.level);
                if (caret instanceof LeanArgsSemicolonSeparated) caret.push(new_);
                else this.replace(caret, new LeanArgsSemicolonSeparated([caret, new_], this.indent, caret.level));
                return new_;
            }
            if (this.parent instanceof LeanBy) {
                const new_ = new LeanCaret(this.indent, caret.level);
                if (caret instanceof LeanArgsSemicolonSeparated) caret.push(new_);
                else this.parent.replace(this, new LeanArgsSemicolonSeparated([this, new_], this.indent, caret.level));
                return new_;
            }
        }
        return super.insert_semicolon(caret);
    }

    /** Port of `LeanTactic::insert_line_comment` / `push_line_comment`. */
    insert_line_comment(_caret, comment) {
        return this.push_line_comment(comment);
    }

    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }

    /** PHP `LeanTactic::has_tactic_block_followed`. */
    has_tactic_block_followed() {
        const p = this.parent;
        if (!(p instanceof LeanStatements)) return;
        const stmts = p.args;
        const idx = stmts.indexOf(this);
        if (idx < 0) return;
        for (let i = idx + 1; i < stmts.length; i++) {
            const stmt = stmts[i];
            if (stmt instanceof LeanTacticBlock) return true;
            if (!stmt.is_comment()) break;
        }
    }

    /**
     * PHP `LeanTactic::get_echo_token`.
     * @returns {Lean | Lean[] | undefined}
     */
    get_echo_token() {
        const at = this.at;
        if (at) {
            let token = at.arg;
            if (this.tacticName === 'split') {
                if (this.has_tactic_block_followed()) return;
            } else {
                if (token instanceof LeanArgsSpaceSeparated) {
                    token = new LeanArgsCommaSeparated(
                        token.args.map((a) => a.clone()),
                        this.indent,
                        token.level,
                    );
                }
            }
            return token;
        }
        let token = [];
        let turnstile = '⊢';
        const arg = this.arg;
        switch (this.tacticName) {
            case 'intro':
            case 'by_contra':
                if (arg instanceof LeanToken) token.push(arg.clone());
                else if (arg instanceof LeanArgsSpaceSeparated) {
                    for (const a of arg.tokens_space_separated()) {
                        if (a instanceof LeanToken) token.push(a.clone());
                        else if (Array.isArray(a)) for (const x of a) token.push(x.clone());
                    }
                } else if (arg instanceof LeanAngleBracket) {
                    const inner = arg.arg;
                    if (inner instanceof LeanToken) token.push(inner.clone());
                    else if (inner instanceof LeanArgsCommaSeparated)
                        token = inner.args.map((x) => x.clone());
                }
                break;
            case 'denote':
            case "denote'":
                if (arg instanceof LeanColon) {
                    const v = arg.lhs;
                    if (v instanceof LeanToken) token.push(v.clone());
                }
                turnstile = null;
                break;
            case 'by_cases':
                if (arg instanceof LeanColon) {
                    const v = arg.lhs;
                    if (v instanceof LeanToken) {
                        if (this.has_tactic_block_followed()) return;
                        token.push(v.clone());
                    }
                }
                break;
            case 'split_ifs': {
                const w = this.with;
                if (w && w.sep() === ' ') {
                    if (this.has_tactic_block_followed()) return;
                    const toks = w.tokens_space_separated();
                    if (toks.length) token.push(toks[0].clone());
                }
                break;
            }
            case "cases'": {
                const w = this.with;
                if (w && w.sep() === ' ' && this.sequential_tactic_combinator) {
                    const ut = w.unique_token(this.indent);
                    if (ut) token.push(ut);
                }
                break;
            }
            case 'injection': {
                const w = this.with;
                if (w && w.sep() === ' ') {
                    let v = w.args[0];
                    if (v instanceof LeanArgsSpaceSeparated) token = v.args;
                    else token = [v];
                    turnstile = null;
                }
                break;
            }
            case 'rcases': {
                const w = this.with;
                const bars = w?.tokens_bar_separated?.();
                if (w && bars?.length) {
                    if (this.has_tactic_block_followed()) return;
                    for (const br of bars) {
                        if (Array.isArray(br))
                            token.push(...br.filter((t) => t.text !== 'rfl'));
                        else if (br.text !== 'rfl') token.push(br);
                        break;
                    }
                }
                break;
            }
            case 'obtain': {
                const assign = arg;
                if (assign instanceof LeanAssign) {
                    const lhs = assign.lhs;
                    if (lhs instanceof LeanAngleBracket) {
                        for (const t of lhs.tokens_comma_separated()) {
                            if (t.text !== 'rfl') token.push(t);
                        }
                    } else if (lhs instanceof LeanBitOr) {
                        if (this.has_tactic_block_followed()) return;
                        for (const br of lhs.tokens_bar_separated()) {
                            if (Array.isArray(br))
                                token.push(...br.filter((t) => t.text !== 'rfl'));
                            else if (br.text !== 'rfl') token.push(br);
                            break;
                        }
                    }
                }
                break;
            }
            case 'specialize': {
                let a = arg;
                if (a instanceof LeanArgsSpaceSeparated && (a = a.args[0]) instanceof LeanToken) token.push(a.clone());
                turnstile = null;
                break;
            }
            case 'contrapose':
            case 'contrapose!':
                if (arg instanceof LeanToken) token.push(arg.clone());
                break;
            case 'sorry':
            case 'echo':
                return;
            case 'try':
                if (arg instanceof LeanTactic && arg.tacticName === 'echo') return;
                break;
            default:
                break;
        }
        if (this.has_tactic_block_followed() || this.parent instanceof LeanSequentialTacticCombinator);
        else if (turnstile) token.push(new LeanToken(turnstile, this.indent, this.level));
        if (token.length === 0) return;
        if (token.length === 1) return token[0];
        return new LeanArgsCommaSeparated(token, this.indent, this.level);
    }

    /** PHP `LeanTactic::echo`. */
    echo() {
        const tok = this.get_echo_token();
        const stc = this.sequential_tactic_combinator;
        const hasStc = stc && stc.arg?.indent;
        if (tok) {
            const echo = new LeanTactic('echo', tok, this.indent, this.level);
            if (tok instanceof LeanToken && tok.text === '*') return [1, echo, this];
            const by = this.by;
            if (by && by.arg instanceof LeanStatements) by.echo?.();
            if (hasStc && stc.newline) {
                echo.push(stc);
                this.sequential_tactic_combinator = new LeanSequentialTacticCombinator(echo, this.indent, this.level, true);
                stc.echo?.();
                return;
            }
            return [1, this, echo];
        }
        if (hasStc) stc.echo?.();
        else {
            const block = this.repeat_block();
            if (block) block.echo?.();
        }
    }

    insert_only(caret) {
        if (caret !== this.args[this.args.length - 1]) {
            throw new Error(`LeanTactic.insert_only: unexpected for ${this.constructor.name}`);
        }
        this.only = true;
        return caret;
    }

    insert_sequential_tactic_combinator(caret, nextToken) {
        const last = this.args[this.args.length - 1];
        if (caret !== last) {
            throw new Error(`LeanTactic.insert_sequential_tactic_combinator: unexpected for ${this.constructor.name}`);
        }
        if (caret instanceof LeanCaret) {
            this.replace(
                caret,
                new LeanSequentialTacticCombinator(caret, this.indent, caret.level, nextToken !== '\n'),
            );
            return caret;
        }
        const ph = new LeanCaret(0, 0);
        this.push(new LeanSequentialTacticCombinator(ph, this.indent, ph.level));
        return ph;
    }

    insert_tactic(caret, type) {
        const last = this.args[this.args.length - 1];
        if (last !== caret || !(caret instanceof LeanCaret)) {
            throw new Error(`LeanTactic.insert_tactic: unexpected for ${this.constructor.name}`);
        }
        if (this.is_inline_tactic_block()) {
            this.replace(caret, new LeanTactic(type, caret, this.indent, caret.level));
            return caret;
        }
        return this.insert_word(caret, type);
    }

    /** PHP `LeanTactic::is_indented`. */
    is_indented() {
        const p = this.parent;
        if (!p) return true;
        if (p instanceof LeanStatements || p instanceof LeanIte) return true;
        if (p instanceof LeanArgsSpaceSeparated && p.parent instanceof LeanTactic) return true;
        if (p instanceof LeanSequentialTacticCombinator && p.arg === this) return true;
        if (p instanceof LeanSequentialTacticCombinator) {
            return this.indent >= p.indent && !p.newline;
        }
        return false;
    }

    jsonSerialize() {
        return {
            [this.tacticName]: this.arg.jsonSerialize?.() ?? this.arg,
            only: this.only,
            modifiers: this.modifiers.map((m) => m.jsonSerialize?.() ?? m),
        };
    }

    latexFormat() {
        let func = escapeSpecialsForLatex(this.tacticName);
        if (this.only) func += '\\ only';
        const color = this.tacticName === 'sorry' ? '708' : '00f';
        func = `{\\color{#${color}}${func}}`;
        if (!(this.arg instanceof LeanCaret)) func += '\\ ';
        return func + Array(this.args.length).fill('%s').join('\\ ');
    }

    relocate_last_comment() {
        const a = this.args[this.args.length - 1];
        if (a instanceof LeanRightarrow || a instanceof LeanWith) a.relocate_last_comment?.();
    }

    repeat_block() {
        if (this.tacticName === 'repeat') {
            const brace = this.arg;
            if (brace instanceof LeanBrace) {
                const block = brace.arg;
                if (block instanceof LeanStatements) return block;
            }
        }
    }

    /**
     * PHP `LeanTactic::split`.
     * @param {Record<string, unknown>} [syntax]
     * @returns {Lean[]}
     */
    split(syntax) {
        if (!syntax) syntax = {};
        syntax[this.tacticName] = true;
        const w = this.with;
        if (w && w.sep() === '\n') {
            const self = this.clone();
            if (self.with) self.with.args = [];
            const statements = [self];
            for (const stmt of w.args) statements.push(...stmt.split(syntax));
            return statements;
        }
        const stc = this.sequential_tactic_combinator;
        if (stc) {
            let block = stc.arg;
            if (block instanceof LeanTacticBlock) {
                if (block.arg instanceof LeanStatements) {
                    const self = this.clone();
                    const inner = self.sequential_tactic_combinator.arg;
                    const stmts = inner.arg;
                    inner.arg = new LeanCaret(0, 0);
                    const statements = [self];
                    stmts.swap_echo_star?.(syntax, statements);
                    return statements;
                }
            } else if (
                (block instanceof LeanTactic || block?.constructor?.name === 'Lean_have' || block?.constructor?.name === 'Lean_let') &&
                block.indent >= this.indent
            ) {
                const self = this.clone();
                if (stc.newline) {
                    block = self.sequential_tactic_combinator;
                    const la = self.args[self.args.length - 1];
                    if (la instanceof LeanSequentialTacticCombinator) self.args.pop();
                } else {
                    block = self.sequential_tactic_combinator.arg;
                    self.sequential_tactic_combinator.arg = new LeanCaret(0, 0);
                }
                const arr = [self];
                arr.push(...block.split(syntax));
                return arr;
            }
        } else {
            const rb = this.repeat_block();
            if (rb) {
                const self = this.clone();
                self.arg = new LeanBrace(new LeanCaret(this.indent, this.level), this.indent, this.level);
                const arr = [self];
                for (const stmt of rb.args) arr.push(...stmt.split(syntax));
                const rbrace = new LeanBrace(new LeanCaret(this.indent, this.level), this.indent, this.level);
                rbrace.is_closed = false;
                arr.push(rbrace);
                return arr;
            }
        }
        const by = this.by;
        if (by && by.arg instanceof LeanStatements) {
            const self = this.clone();
            self.by.arg = new LeanCaret(by.indent, by.level);
            const statements = [self];
            by.arg.swap_echo_star?.(syntax, statements);
            return statements;
        }
        return [this];
    }

    /** PHP `LeanTactic::strFormat`. */
    strFormat() {
        let func = this.tacticName;
        if (this.only) func += ' only';
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof LeanCaret);
            else if (arg instanceof LeanSequentialTacticCombinator && arg.newline) parts.push('\n');
            else parts.push(' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }

    /**
     * Port of `LeanTactic::getEcho`.
     * @returns {LeanTactic | undefined}
     */
    getEcho() {
        if (this.tacticName === 'echo') return this;
        if (this.tacticName === 'try' && this.arg instanceof LeanTactic && this.arg.tacticName === 'echo') return this.arg;
    }
}

/**
 * PHP `LeanIte`: `if … then … else …`.
 */
export class LeanIte extends LeanArgs {
    static input_priority = 60;

    get stack_priority() {
        return 23;
    }

    get if() {
        return this.args[0];
    }
    set if(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get then() {
        return this.args[1] ?? null;
    }
    set then(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    get else() {
        return this.args[2] ?? null;
    }
    set else(v) {
        while (this.args.length < 3) this.args.push(undefined);
        this.args[2] = v;
        if (v != null && typeof v === 'object') v.parent = this;
    }

    echo() {
        const if_ = this.args[0];
        let token = null;
        if (if_ instanceof LeanColon && if_.args[0] instanceof LeanToken) token = if_.args[0];
        const then = this.then;
        const else_ = this.else;
        if (then) this.echo_then(token);
        if (else_) this.echo_else(token);
    }

    /** @param {LeanToken | null} token */
    echo_else(token) {
        const part = this.else;
        part.echo?.();
        if (token) {
            if (part instanceof LeanIte) LeanIte.echo_part(part.then, token);
            else LeanIte.echo_part(part, token);
        }
    }

    /** @param {LeanToken | null} token */
    echo_then(token) {
        const part = this.then;
        part.echo?.();
        if (token) LeanIte.echo_part(part, token);
    }

    insert_colon(caret) {
        if (caret === this.if) {
            const c = new LeanCaret(caret.indent, caret.level);
            this.replace(caret, new LeanColon(caret, c, caret.indent, caret.level));
            return c;
        }
        return caret.push_binary('LeanColon');
    }

    insert_else(caret) {
        if (!this.else) {
            const c = new LeanCaret(this.indent + 2, caret.level);
            this.else = c;
            return c;
        }
        if (this.parent) return this.parent.insert_else(this);
    }

    insert_if(caret) {
        if (caret instanceof LeanCaret) {
            if (caret === this.else) {
                this.else = new LeanIte([caret], this.indent, caret.level);
                return caret;
            }
            if (caret === this.then) {
                if (caret.indent < this.indent + 2) caret.indent = this.indent + 2;
                this.then = new LeanIte([caret], caret.indent, caret.level);
                return caret;
            }
        }
        throw new Error(`LeanIte.insert_if: unexpected for ${this.constructor.name}`);
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.then) {
            if (caret instanceof LeanTactic || caret instanceof Lean_let) {
                const stmt = new LeanStatements([caret], caret.indent, caret.level);
                this.then = stmt;
                for (let i = 0; i < newlineCount; i++) {
                    caret = new LeanCaret(caret.indent, caret.level);
                    stmt.push(caret);
                }
            }
            return caret;
        }
        if (caret === this.else) {
            if (caret instanceof LeanCaret) return caret;
            if (indent > this.indent && (caret instanceof LeanTactic || caret instanceof Lean_let)) {
                const stmt = new LeanStatements([caret], caret.indent, caret.level);
                this.else = stmt;
                for (let i = 0; i < newlineCount; i++) {
                    caret = new LeanCaret(caret.indent, caret.level);
                    stmt.push(caret);
                }
                return caret;
            }
        }
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
    }

    insert_tactic(caret, func) {
        if (caret instanceof LeanCaret) {
            this.replace(
                caret,
                new LeanTactic(func, caret, this.indent + 2, caret.level),
            );
            return caret;
        }
        const c = new LeanCaret(this.indent + 2, caret.level);
        this.replace(
            caret,
            new LeanStatements(
                [caret, new LeanTactic(func, c, this.indent + 2, caret.level)],
                this.indent + 2,
                caret.level,
            ),
        );
        return c;
    }

    insert_then(caret) {
        if (!this.then) {
            const c = new LeanCaret(this.indent + 2, caret.level);
            this.then = c;
            return c;
        }
        throw new Error(`LeanIte.insert_then: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        const p = this.parent;
        return (
            !p ||
            p instanceof LeanStatements ||
            (p instanceof LeanIte && (!p.then || this === p.then))
        );
    }

    /**
     * PHP `LeanIte::latexArgs`.
     * @param {Record<string, unknown>} [syntax]
     */
    latexArgs(syntax) {
        const cases = [];
        let cur = /** @type {LeanIte | Lean} */ (this);
        while (true) {
            const [if_, then, els] = cur.strip_parenthesis();
            const ifL = if_.toLatex(syntax);
            const thenL = then.toLatex(syntax);
            cases.push(`{${thenL}} & {\\color{blue}\\text{if}}\\ ${ifL} `);
            if (!(els instanceof LeanIte)) {
                cases.push(els.toLatex(syntax));
                break;
            }
            cur = els;
        }
        return cases;
    }

    latexFormat() {
        let n = 0;
        let cur = /** @type {LeanIte | Lean} */ (this);
        while (true) {
            const [, , els] = cur.strip_parenthesis();
            n++;
            if (!(els instanceof LeanIte)) break;
            cur = els;
        }
        const rows = Array(n).fill('%s').join('\\\\');
        return `\\begin{cases} ${rows} \\\\ {%s} & {\\color{blue}\\text{else}} \\end{cases}`;
    }

    relocate_last_comment() {
        const els = this.else;
        if (els instanceof LeanStatements || els instanceof LeanIte) els.relocate_last_comment();
    }

    set_line(line) {
        this.line = line;
        const if_ = this.args[0];
        const then = this.args[1];
        const else_ = this.args[2];
        line = if_.set_line(line);
        line++;
        line = then.set_line(line);
        line++;
        if (!(else_ instanceof LeanIte)) line++;
        return else_.set_line(line);
    }

    /**
     * PHP `LeanIte::split`.
     * @param {Record<string, unknown>} [syntax]
     */
    split(syntax) {
        const then = this.then;
        const else_ = this.else;
        if (then && else_) {
            const self = this.clone();
            const sIf = self.args[0];
            const sThen = self.args[1];
            const sElse = self.args[2];
            self.args = [sIf];
            const statements = [self];
            if (sThen instanceof LeanStatements) sThen.swap_echo_star(syntax, statements);
            else statements.push(sThen);
            if (sElse instanceof LeanIte) {
                const sp = sElse.split(syntax);
                sp[0].args[2] = 0;
                statements.push(...sp);
            } else {
                statements.push(new LeanIte([], this.indent, else_.level));
                if (sElse instanceof LeanStatements) sElse.swap_echo_star(syntax, statements);
                else statements.push(sElse);
            }
            return statements;
        }
        return [this];
    }

    strFormat() {
        const if_ = this.args[0];
        const then = this.args[1];
        const else_ = this.args[2];
        if (!then && !else_) {
            if (if_ == null) return 'else';
            if (else_ === 0) return 'else if %s then';
            return 'if %s then';
        }
        const indent_else = ' '.repeat(this.indent);
        const sep = else_ instanceof LeanIte ? ' ' : '\n';
        const thenFmt = then == null ? '' : '%s';
        const elseFmt = else_ == null ? '' : '%s';
        return `if %s then\n${thenFmt}\n${indent_else}else${sep}${elseFmt}`;
    }

    /**
     * PHP `LeanIte::echo_part`.
     * @param {Lean} part
     * @param {LeanToken} token
     */
    static echo_part(part, token) {
        const echo = new LeanTactic('echo', token.clone(), part.indent, part.level);
        if (part instanceof LeanStatements) part.unshift(echo);
        else if (part.parent)
            part.parent.replace(part, new LeanStatements([echo, part], part.indent, part.level));
    }
}

export class LeanParser extends AbstractParser {
    constructor() {
        super(null);
        this.tokens = [];
        this.start_idx = 0;
        this.root = null;
    }

    init() {
        const caret = new LeanCaret(0, 0);
        this.caret = caret;
        this.root = new LeanModule([caret], 0, 0);
    }

    /**
     * Like `AbstractParser::parse` but never leave `this.caret` undefined if `Lean::parse` forgets to return.
     */
    parse(token, ...kwargs) {
        const next = this.caret.parse(token, ...kwargs);
        this.caret = next ?? this.caret;
        return this.caret;
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
        while (this.start_idx < length) {
            this.parse(tokens[this.start_idx], this);
            this.start_idx++;
        }
        return this.root;
    }
}

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
    Lean_theorem,
    Lean_lemma,
    LeanCaret,
    Lean_let,
    Lean_have,
    Lean_fun,
    Lean_match,
    LeanWith,
    LeanToken,
    LeanLineComment,
    LeanBlockComment,
    LeanDocString,
    LeanProperty,
    LeanGetElem,
    LeanGetElemQue,
    LeanGetElemQuote,
    LeanStack,
    LeanBracket,
    LeanBrace,
    LeanAngleBracket,
    LeanAbs,
    LeanNorm,
    LeanCeil,
    LeanFloor,
    LeanFrom,
    LeanDoubleAngleQuotation,
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
    LeanVConstruct,
    LeanAppend,
    Lean_bigcap,
    Lean_bigcup,
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
    LeanEq,
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
    Lean_lnot,
    Lean_namespace,
    LeanNegPart,
    LeanNot,
    Lean_open,
    LeanPipeForward,
    LeanPlus,
    LeanPosPart,
    LeanQuarticRoot,
    Lean_set_option,
    Lean_show,
    Lean_sum,
    LeanSquare,
    Lean_sqrt,
    LeanTesseract,
    LeanTranspose,
    Lean_uparrow,
    LeanUparrow,
    LeanUsing,
};

/**
 * Resolve an AST class by name. Mirrors PHP `new $ClassName(...)`
 * Looks up `LEAN_CLASSES` (concrete classes only).
 * @param {string} name
 */
function getLeanClass(name) {
    const C = LEAN_CLASSES[name];
    if (C) return C;
    throw new Error(`getLeanClass: unknown class ${name} (add to LEAN_CLASSES)`);
}

/**
 * PHP `Lean::toString()` (lean.php) — `strFormat` + `strArgs` + `sprintf` only. It does not recurse into
 * children itself: nested `Lean` values are coerced the same way as PHP `%s` on objects (`__toString`), here
 * `String(arg)` → `Lean.prototype.toString()` → optional indent + this body. Layout details live in `strFormat` /
 * `strArgs` on each class.
 *
 * @param {unknown} node
 * @returns {string}
 */
function leanPhpToStringBody(node) {
    if (!(node instanceof Lean)) return String(node);
    const format = node.strFormat();
    const args = node.strArgs();
    if (args.length === 0) return format;
    return String(format).format(...args.map((a) => (a instanceof Lean ? String(a) : a)));
}

/**
 * Port of global `compile`.
 * @param {string} code
 */
export function compile(code) {
    return LeanParser.instance.build(code);
}

// Align with PHP `LeanParser::$instance`
LeanParser._instance = new LeanParser();
Object.defineProperty(LeanParser, 'instance', {
    get() {
        if (!LeanParser._instance) LeanParser._instance = new LeanParser();
        return LeanParser._instance;
    },
});
