import '../utility.js';
import { IndentedNode, AbstractParser, Closable } from './node.js';
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

function escapeSpecialsForLatex(token) {
    const s = String(token);
    const m = /^(\w+?)_(.+)$/.exec(s);
    if (m) {
        const [, head, tail] = m;
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        return head.length === 1 ? `${head}_{${escTail}}` : `${head}\\_${escTail}`;
    }
    if (/\w_$/.test(s)) return s.slice(0, -1) + '\\_';
    return s;
}

/** Abstract Lean AST node; method order follows `scripts/reorder_lean_class.py` preset `lean`. */
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
        const format = this.strFormat();
        const args = this.strArgs();
        const inner =
            args.length === 0
                ? format
                : String(format).format(...args.map((a) => (a instanceof Lean ? String(a) : a)));
        return (this.is_indented() ? ' '.repeat(this.indent) : '') + inner;
    }

    /**
     * Subclasses must override or inherit `toJSON` from a base that does (e.g. `LeanArgs`, `LeanUnary`, `LeanBinary`).
     * Direct `node.toJSON()` calls must not use optional chaining so missing implementations fail fast.
     */
    toJSON() {
        throw new Error(`${this.constructor.name}.toJSON() is not implemented`);
    }

    append($new, _type) {
        if (this.parent) return this.parent.append(this, $new, _type);
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
        if (this.parent) return this.parent.insert_only(caret);
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
        if (caret instanceof LeanCaret) {
            const level = caret.level;
            const newTok = new LeanToken(word, caret.indent, level);
            caret.parent.replace(caret, new LeanArgsSpaceSeparated([caret, newTok], caret.indent, level));
            return newTok;
        }
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
            case 'protected': {
                let access = token;
                while (tokens[++self.start_idx] === ' ');
                if (tokens[self.start_idx] === 'nonrec') {
                    access += ' nonrec';
                    self.start_idx++;
                    while (tokens[++self.start_idx] === ' ');
                }
                return this.push_accessibility(`Lean_${tokens[self.start_idx]}`, access);
            }
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
                // When a callee omits `return` (PHP can yield null in the same situations), keep this caret so
                // `AbstractParser.parse` matches practical parse completion without a `LeanParser` override.
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
                // PHP `Lean::parse` treats non-property `is` as `Lean_is` / `Lean_is_not` only. In JS we also
                // treat `is` as a plain identifier under import/open/def/… (e.g. `Setoid.is.All_SetoidGetS`)
                // so round-trip and lemma paths match the tokenizer/AST shape the repo relies on.
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
                if (this instanceof LeanCaret) return this.parent.insert_word(this, token);
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
            case 'if': {
                let n = this.parent;
                while (n && typeof n.insert_if !== 'function') n = n.parent;
                if (!n) throw new Error('insert_if is unexpected');
                return n.insert_if(this);
            }
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
    }

    push_accessibility($new, _accessibility) {
        if (this.parent) return this.parent.push_accessibility($new, _accessibility);
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

    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join(' ');
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

export class LeanCaret extends Lean {
    append($new, $func) {
        if (typeof $new === 'string') {
            const Ctor = getLeanClass($new);
            this.parent.replace(this, new Ctor(this, this.indent, this.level));
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
        this.parent.replace(this, new (getLeanClass($new))($accessibility, this, this.indent, this.level));
        return this;
    }

    push_block_comment(comment, docstring) {
        const parent = this.parent;
        const Cls = docstring ? LeanDocString : LeanBlockComment;
        parent.replace(this, new Cls(comment, this.indent, this.level));
        parent.push(this);
        return this;
    }

    push_left($func, $prevToken) {
        const Ctor = getLeanClass($func);
        this.parent.replace(this, new Ctor(this, this.indent, this.level));
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
        return (vars?.[this.text] ?? null) === 'Prop';
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
 * Port of PHP trait `LeanMultipleLine` (`set_line`): advance one logical line between each child.
 * Used by `LeanStatements`, `LeanModule`, `LeanArgsNewLineSeparated`, `LeanArgsCommaNewLineSeparated`.
 * @param {{ line: unknown; args: Lean[] }} self
 * @param {number} line
 */
function leanMultipleLineSetLine(self, line) {
    self.line = line;
    for (const arg of self.args) {
        line = arg.set_line(line) + 1;
    }
    return line - 1;
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
            this.replace(caret, new LeanTactic(func, caret, this.indent, caret.level));
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
            const n = inner?.constructor?.name;
            if (n === 'LeanMethodChaining' || n === 'Lean_rightarrow' || n === 'LeanColon') return arg;
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

/**
 * Abstract paired delimiters. Uses `Closable(LeanUnary)` like `MarkdownLink extends Closable(MarkdownArgs)` in `markdown.js`.
 */
class LeanPairedGroup extends Closable(LeanUnary) {
    static input_priority = 60;

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

    insert_if(caret) {
        if (this.arg === caret && caret instanceof LeanCaret) {
            this.arg = new LeanIte([caret], caret.indent, caret.level);
            return caret;
        }
        if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
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
}

/** Parentheses: inner `level` for rainbow LaTeX. Method order follows the reference `LeanParenthesis` class. */
export class LeanParenthesis extends LeanPairedGroup {
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

    get stack_priority() {
        return 10;
    }

    get operator() {
        return '()';
    }

    append($new, _func) {
        const indent = this.indent;
        const level = this.level;
        const caret = new LeanCaret(indent, level);
        if (typeof $new === 'string') {
            const Ctor = getLeanClass($new);
            const node = new Ctor(caret, indent, level);
            if (this.parent instanceof LeanArgsSpaceSeparated) {
                this.parent.push(node);
            } else {
                this.arg = new LeanArgsSpaceSeparated([this.arg, node], indent, level);
            }
            return caret;
        }
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, $new], indent, level));
        return $new;
    }

    argFormat() {
        const arg = this.arg;
        if (arg instanceof LeanBy) {
            const stmt = arg.arg;
            if (stmt instanceof LeanStatements) {
                const last = stmt.args[stmt.args.length - 1];
                if (last instanceof LeanCaret) {
                    return `%s${' '.repeat(this.indent)}`;
                }
            }
        }
        return '%s';
    }

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

    insert_unary(caret, funcName) {
        if (caret !== this.arg) {
            throw new Error(`insert_unary is unexpected for ${this.constructor.name}`);
        }
        const indent = this.indent;
        const Ctor = getLeanClass(funcName);
        let caretOut;
        let newNode;
        if (caret instanceof LeanCaret) {
            newNode = new Ctor(caret, indent, caret.level);
            caretOut = caret;
        } else {
            const lev = caret.level;
            caretOut = new LeanCaret(indent, lev);
            newNode = new LeanArgsSpaceSeparated(
                [this.arg, new Ctor(caretOut, indent, lev)],
                indent,
                lev,
            );
        }
        this.arg = newNode;
        return caretOut;
    }

    is_indented() {
        const parent = this.parent;
        if (parent instanceof LeanStatements && this.indent > 0) return true;
        return (
            parent instanceof LeanArgsNewLineSeparated ||
            parent instanceof LeanArgsCommaNewLineSeparated ||
            (parent instanceof LeanIte && this !== parent.if)
        );
    }

    isProp(vars) {
        return this.arg.isProp(vars);
    }

    latexArgs(syntax) {
        const arg = this.arg;
        if (arg instanceof LeanColon) {
            if (arg.lhs instanceof LeanBrace) return arg.lhs.latexArgs?.(syntax) ?? [arg.lhs.toLatex(syntax)];
            if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return [arg.lhs.toLatex(syntax)];
        }
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const arg = this.arg;
        if (arg instanceof LeanColon) {
            if (arg.lhs instanceof LeanBrace) return arg.lhs.latexFormat?.() ?? '%s';
            if (arg.rhs instanceof LeanToken && arg.rhs.text === 'Bool') return '\\left|{%s}\\right|';
        }
        return this.toColor();
    }

    regexp() {
        return this.arg.regexp();
    }

    toColor() {
        let n = (this.arg.level ?? 0) & 7;
        const b = '9f'[n & 1];
        n >>= 1;
        const g = '9f'[n & 1];
        n >>= 1;
        const r = '9f'[n & 1];
        return `\\colorbox{#${r}${g}${b}}{$\\mathord{\\left(%s\\right)}$}`;
    }
}

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

    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    strArgs() {
        let arg = this.arg;
        if (arg instanceof LeanArgsCommaNewLineSeparated) {
            arg = `\n${arg}\n${' '.repeat(this.indent)}`;
        }
        return [arg];
    }

    tokens_comma_separated() {
        const a = this.arg;
        if (a instanceof LeanArgsCommaSeparated) return a.tokens_comma_separated();
        return [a];
    }
}

/**
 * Square brackets. Declaration order matches the reference `LeanBracket` class: virtual `stack_priority` /
 * `operator`, `is_Expr`, `latexFormat`, `push_right`, `strArgs`. `toString` is a JS-only indent tweak when the
 * parent is `LeanModule` (no separate method in the reference class).
 */
class LeanBracket extends LeanPairedGroup {
    is_Expr() {
        return false;
    }

    latexFormat() {
        return '\\left[ {%s} \\right]';
    }

    get operator() {
        return '[]';
    }

    push_right(funcName) {
        if (funcName === this.constructor.name) {
            const lt = this.arg;
            if (lt instanceof Lean_lt && lt.lhs instanceof LeanToken) {
                const level = this.level;
                const stack = new LeanStack(lt, this.indent, level);
                const scope = new LeanCaret(this.indent, level);
                stack.scope = scope;
                this.parent.replace(this, stack);
                return scope;
            }
        }
        return super.push_right(funcName);
    }

    /** Like `LeanAngleBracket.push_token`: after `]` the caret is this node; splice a following identifier (e.g. `[i] X[i]'`). */
    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    get stack_priority() {
        return 17;
    }

    strArgs() {
        let arg = this.arg;
        if (arg instanceof LeanArgsCommaNewLineSeparated) {
            arg = `\n${arg}\n${' '.repeat(this.indent)}`;
        }
        return [arg];
    }
}

class LeanBrace extends LeanPairedGroup {
    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent) {
            if (caret instanceof LeanCaret) {
                if (indent === this.indent) {
                    indent = this.indent + 2;
                }
                caret.indent = indent;
                this.arg = new LeanStatements([caret], indent, caret.level);
                return caret;
            } else {
                if (indent === this.indent) {
                    return caret;
                }
                throw new Error(`${this.constructor.name}.insert_newline is unexpected for ${caret.constructor.name}`);
            }
        } else {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
    }

    is_Expr() {
        return false;
    }

    is_indented() {
        const p = this.parent;
        return !(p instanceof LeanQuantifier || p instanceof LeanBinaryBoolean || p instanceof LeanColon || p instanceof LeanSetOperator || p instanceof LeanTactic || p instanceof LeanAssign);
    }

    latexFormat() {
        return '\\left\\{ {%s} \\right\\}';
    }

    get operator() {
        return '{}';
    }

    get stack_priority() {
        return 17;
    }
}

class LeanAbs extends LeanPairedGroup {
    get operator() {
        return '||';
    }
    get stack_priority() {
        return 17;
    }
    insert_bar(caret, prevToken, next) {
        return this.push_right('LeanAbs');
    }
    latexFormat() {
        return '\\left| {%s} \\right|';
    }
}

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
        if (this.constructor.name === 'LeanArgsIndented' && caret instanceof LeanCaret) {
            const last = this.args[this.args.length - 1];
            if (last === caret) {
                this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
                return caret;
            }
            if (this.parent && typeof this.parent.insert_if === 'function') return this.parent.insert_if(caret);
            throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
        }
        if (this.rhs === caret && caret instanceof LeanCaret) {
            this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_if is unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, func) {
        return this.insert_word(caret, func);
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }

    latexFormat() {
        return `{%s} ${this.command} {%s}`;
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

    // JS-only extensions (alphabetical order)

    /** Forward echo to rhs. */
    echo() {
        this.rhs?.echo?.();
    }

    /** Handle newline insertion for tactic contexts. */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.parent instanceof LeanTactic && indent > this.indent) {
            return this.parent.push_args_indented(indent, newlineCount, false);
        }
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
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

/** Property access `Foo.bar`. */
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
                        [this, new (getLeanClass(func))(newCaret, newCaret.indent, newCaret.level)],
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

    insert_newline(caret, newlineCount, indent, next) {
        if (this.parent instanceof LeanTactic && indent > this.indent) {
            return this.parent.push_args_indented(indent, newlineCount, false);
        }
        return this.parent.insert_newline(this, newlineCount, indent, next);
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
            (parent instanceof LeanArgsIndented && parent.rhs === this) ||
            (parent instanceof LeanIte && parent.else === this);
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
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    let arg = '%s';
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
                case 'fmod':
                    return [this.lhs.toLatex(syntax)];
                case 'card':
                    if (!(lhs instanceof LeanToken && this.parent instanceof LeanArgsSpaceSeparated && this.parent.args[0] === this)) {
                        return [this.lhs.toLatex(syntax)];
                    }
                    break;
                case 'softmax':
                    if (syntax) syntax.softmax = true;
                    break;
            }
        }
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const [lhs, rhs] = this.args;
        if (rhs instanceof LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    let arg = '%s';
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
                    return `\\\\${rhs.text} {%s}`;
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

    is_indented() {
        return false;
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
        // Only ` : ` when a real space separates colon from rhs; keep `main:\n` / `x:` shapes stable.
        if (!this.parent?.constructor?.name?.includes('GetElem') && sep === ' ') {
            first += ' ';
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
        this.rhs?.echo?.();
    }

    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
        throw new Error(`insert is unexpected for ${this.constructor.name}`);
    }

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

    insert_tactic(caret, type) {
        return this.insert_word(caret, type);
    }

    is_indented() {
        const p = this.parent;
        return !p || p instanceof LeanArgsNewLineSeparated || (p instanceof LeanArgsIndented && p.rhs === this);
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
        return ' ';
    }

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

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanBinaryBoolean extends LeanBinary {
    /**
     * @param {Record<string, unknown>} [_vars]
     */
    isProp(_vars) {
        return true;
    }

    append(new_, type) {
        const indent = this.indent;
        const level = this.level;
        const caret = new LeanCaret(indent, level);
        if (typeof new_ === 'string') {
            const Ctor = getLeanClass(new_);
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
        return caret.push_binary('LeanColon');
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.rhs === caret && indent > this.indent) {
            if (caret instanceof LeanCaret) {
                caret.indent = indent;
                this.rhs = new LeanStatements([caret], indent, caret.level);
                return caret;
            }
            return this.parent.push_args_indented(indent, newlineCount, false);
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanRelational extends LeanBinaryBoolean {
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
    get operator() {
        return '>';
    }
}
export class Lean_ge extends LeanRelational {
    get operator() {
        return '≥';
    }
}
export class Lean_lt extends LeanRelational {
    get operator() {
        return '<';
    }
}
export class Lean_le extends LeanRelational {
    get operator() {
        return '≤';
    }
}
export class LeanEq extends LeanRelational {
    get command() {
        return '=';
    }

    get operator() {
        return '=';
    }
}
export class LeanBEq extends LeanRelational {
    get command() {
        return '\\!\\!=';
    }

    get operator() {
        return '==';
    }
}
export class Lean_bne extends LeanRelational {
    get command() {
        return '!=';
    }

    get operator() {
        return '!=';
    }
}
export class Lean_ne extends LeanRelational {
    get operator() {
        return '≠';
    }
}
export class Lean_equiv extends LeanRelational {
    static input_priority = 32;

    get operator() {
        return '≡';
    }
}
export class LeanNotEquiv extends LeanRelational {
    static input_priority = 32;

    get command() {
        return '\\not\\equiv';
    }

    get operator() {
        return '≢';
    }
}
export class Lean_simeq extends LeanRelational {
    static input_priority = 50;

    get operator() {
        return '≃';
    }

    latexArgs(syntax) {
        if (syntax) syntax['≃'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_approx extends LeanRelational {
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
    static input_priority = 50;

    get command() {
        return '{\\color{red}{\\ \\mid\\ }}';
    }

    get operator() {
        return '∣';
    }
}

/** Set / arrow: `∈` (membership). */
export class Lean_in extends LeanBinaryBoolean {
    static input_priority = 50;

    get operator() {
        return '∈';
    }

    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon)) lhs = lhs.arg;
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
export class Lean_notin extends LeanBinaryBoolean {
    static input_priority = 50;

    get operator() {
        return '∉';
    }

    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof LeanParenthesis) lhs = lhs.arg;
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
/** `↔`. */
export class Lean_leftrightarrow extends LeanBinaryBoolean {
    static input_priority = 20;

    get operator() {
        return '↔';
    }
}

export class LeanArithmetic extends LeanBinary {
    static input_priority = 67;

    insert_newline(caret, newlineCount, indent, next) {
        if (caret instanceof LeanCaret)
            return caret;
        return this.parent.insert_newline(this, newlineCount, indent, next);
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
    static input_priority = 65;

    get command() {
        return '+';
    }

    get operator() {
        return '+';
    }
}

export class LeanSub extends LeanArithmetic {
    static input_priority = 65;

    get command() {
        return '-';
    }

    get operator() {
        return '-';
    }
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

    get operator() {
        return '*';
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
        const command = this.command;
        if (command) {
            return `${this.lhs.toLatex()} ${command} ${this.rhs.toLatex()}`;
        }
        return `%s  %s`;
    }
}

export class Lean_times extends LeanArithmetic {
    static input_priority = 72;

    get operator() {
        return '×';
    }
}

export class LeanMatMul extends LeanArithmetic {
    static input_priority = 70;

    get operator() {
        return '@';
    }

    get command() {
        return '{\\color{red}\\times}';
    }
}

export class Lean_bullet extends LeanArithmetic {
    static input_priority = 73;

    get operator() {
        return '•';
    }
}

export class Lean_odot extends LeanArithmetic {
    static input_priority = 73;

    get operator() {
        return '⊙';
    }
}

export class Lean_otimes extends LeanArithmetic {
    static input_priority = 32;

    get operator() {
        return '⊗';
    }
}

export class Lean_oplus extends LeanArithmetic {
    static input_priority = 30;

    get operator() {
        return '⊕';
    }
}

export class LeanDiv extends LeanArithmetic {
    static input_priority = 70;

    get operator() {
        return '/';
    }

    latexArgs(syntax) {
        let lhs = this.lhs;
        let rhs = this.rhs;
        if (!(lhs instanceof LeanDiv)) {
            if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon))
                lhs = lhs.arg;
            if (rhs instanceof LeanParenthesis && !(rhs.arg instanceof LeanColon))
                rhs = rhs.arg;
        }
        return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
    }

    latexFormat() {
        const lhs = this.lhs;
        const rhs = this.rhs;
        if (lhs instanceof LeanDiv || (rhs instanceof LeanParenthesis && rhs.arg instanceof LeanDiv)) {
            return '\\left. {%s} \\right/ {%s}';
        }
        return '\\frac {%s} {%s}';
    }
}

export class LeanFDiv extends LeanArithmetic {
    static input_priority = 70;

    get command() {
        return '/\\!\\!/';
    }

    get operator() {
        return '//';
    }
}

export class LeanBitAnd extends LeanArithmetic {
    static input_priority = 68;

    get command() {
        return '\\&';
    }

    get operator() {
        return '&';
    }
}

export class LeanBitwiseAnd extends LeanArithmetic {
    static input_priority = 60;

    get command() {
        return '\\&\\!\\!\\&\\!\\!\\&';
    }

    get operator() {
        return '&&&';
    }
}

export class LeanBitwiseXor extends LeanArithmetic {
    static input_priority = 60;

    get command() {
        return '\\^\\^\\^';
    }

    get operator() {
        return '^^^';
    }
}

export class LeanBitOr extends LeanArithmetic {
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
        throw new Error(`LeanBitOr.insert_bar: unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        return false;
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

export class LeanBitwiseOr extends LeanArithmetic {
    static input_priority = 55;

    get command() {
        return '|\\!\\!|\\!\\!|';
    }

    get operator() {
        return '|||';
    }
}

export class LeanPow extends LeanArithmetic {
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

    latexArgs(syntax) {
        let lhs = this.lhs;
        let rhs = this.rhs;
        if (lhs instanceof LeanParenthesis) {
            const inner = lhs.arg;
            if (inner instanceof Lean_sqrt || inner instanceof LeanPairedGroup ||
                (inner instanceof LeanArgsSpaceSeparated && (inner.is_Abs?.() || inner.is_Bool?.())))
                lhs = inner;
        }
        if (rhs instanceof LeanParenthesis) {
            const inner = rhs.arg;
            if (inner instanceof Lean_sqrt || inner instanceof LeanPairedGroup ||
                (inner instanceof LeanArgsSpaceSeparated && (inner.is_Abs?.() || inner.is_Bool?.())))
                rhs = inner;
        }
        return [lhs.toLatex(syntax), rhs.toLatex(syntax)];
    }
}

export class Lean_ll extends LeanArithmetic {
    get operator() {
        return '<<';
    }
}

export class Lean_lll extends LeanArithmetic {
    get operator() {
        return '<<<';
    }
}

export class Lean_gg extends LeanArithmetic {
    get operator() {
        return '>>';
    }
}

export class Lean_ggg extends LeanArithmetic {
    static input_priority = 75;

    get operator() {
        return '>>>';
    }
}

export class LeanModular extends LeanArithmetic {
    static input_priority = 70;

    get command() {
        return '\\%\\%';
    }

    get operator() {
        return '%';
    }
}

export class LeanConstruct extends LeanArithmetic {
    static input_priority = 67;

    get command() {
        return '::';
    }

    get operator() {
        return '::';
    }
}

export class LeanVConstruct extends LeanArithmetic {
    static input_priority = 67;

    get command() {
        return '::_v';
    }

    get operator() {
        return '::ᵥ';
    }
}

export class LeanAppend extends LeanArithmetic {
    static input_priority = 65;

    get command() {
        return '+\\!\\!+';
    }

    get operator() {
        return '++';
    }
}

export class Lean_sqcup extends LeanArithmetic {
    static input_priority = 68;

    get operator() {
        return '⊔';
    }
}

export class Lean_sqcap extends LeanArithmetic {
    static input_priority = 69;

    get operator() {
        return '⊓';
    }
}

export class Lean_cdotp extends LeanArithmetic {
    static input_priority = 71;

    get operator() {
        return '⬝';
    }

    get command() {
        return '{\\color{red}\\cdotp}';
    }
}

export class Lean_circ extends LeanArithmetic {
    static input_priority = 90;

    get operator() {
        return '∘';
    }
}

export class Lean_blacktriangleright extends LeanArithmetic {
    static input_priority = 47;

    get operator() {
        return '▸';
    }

    is_indented() {
        return this.parent instanceof LeanArgsNewLineSeparated;
    }
}

class LeanUnaryArithmetic extends LeanUnary {}

export class LeanUnaryArithmeticPost extends LeanUnaryArithmetic {
    static input_priority = 72;

    get stack_priority() {
        return 60;
    }
}

class LeanUnaryArithmeticPre extends LeanUnaryArithmetic {}

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

/** Postfix cube `³`. */
class LeanCube extends LeanUnaryArithmeticPost {
    get operator() {
        return '³';
    }
    strFormat() {
        return `%s${this.operator}`;
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

export class LeanGetElem extends LeanBinary {
    static input_priority = 88;

    get stack_priority() {
        return 18;
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    latexFormat() {
        return '{%s}_{%s}';
    }

    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    sep() {
        return '';
    }

    strFormat() {
        return '%s[%s]';
    }
}

export class LeanGetElemQue extends LeanBinary {
    static input_priority = 88;

    get stack_priority() {
        return 18;
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    latexFormat() {
        return '{%s}_{%s?}';
    }

    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    sep() {
        return '';
    }

    strFormat() {
        return '%s[%s]?';
    }
}

export class LeanGetElemQuote extends LeanArgs {
    static input_priority = 88;

    get stack_priority() {
        return 18;
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    latexFormat() {
        return "{%s}_{%s{\\color{red}\\text{'}}%s}";
    }

    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    strFormat() {
        return "%s[%s]'%s";
    }
}

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

/** Set-theoretic binary (`\\`, `∪`, `∩`); abstract base like `LeanSetOperator`. */
export class LeanSetOperator extends LeanBinary {
    sep() {
        return ' ';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class Lean_setminus extends LeanSetOperator {
    static input_priority = 70;

    get operator() {
        return '\\';
    }
}

export class Lean_cup extends LeanSetOperator {
    static input_priority = 65;

    get operator() {
        return '∪';
    }
}

export class Lean_cap extends LeanSetOperator {
    static input_priority = 70;

    get operator() {
        return '∩';
    }
}

/** Logic connectives under `LeanStatements` (`&&`, `∨`, …); hanging newline via `hanging_indentation`. */
export class LeanLogic extends LeanBinaryBoolean {
    /** @type {boolean|undefined} */
    hanging_indentation;

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    sep() {
        if (this.hanging_indentation) {
            const ind = this.rhs?.indent ?? 0;
            return '\n' + ' '.repeat(ind);
        }
        return ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanLogicAnd extends LeanLogic {
    static input_priority = 37;

    get stack_priority() {
        return 50;
    }

    get command() {
        return '\\&\\&';
    }

    get operator() {
        return '&&';
    }

    toJSON() {
        const lhs = this.lhs.toJSON();
        const rhs = this.rhs.toJSON();
        const f = this.func;
        const rec = lhs && typeof lhs === 'object' ? /** @type {Record<string, unknown>} */ (lhs) : null;
        if (this.lhs instanceof LeanLogicAnd && rec && Array.isArray(rec[f])) {
            return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
        }
        return { [f]: [lhs, rhs] };
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class LeanLogicOr extends LeanLogic {
    static input_priority = 37;

    get stack_priority() {
        return 36;
    }

    get command() {
        return '\\|\\|';
    }

    get operator() {
        return '||';
    }

    toJSON() {
        const lhs = this.lhs.toJSON();
        const rhs = this.rhs.toJSON();
        const f = this.func;
        const rec = lhs && typeof lhs === 'object' ? /** @type {Record<string, unknown>} */ (lhs) : null;
        if (this.lhs instanceof LeanLogicOr && rec && Array.isArray(rec[f])) {
            return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
        }
        return { [f]: [lhs, rhs] };
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class LeanLogicXor extends LeanLogic {
    static input_priority = 33;

    get command() {
        return '\\^\\^';
    }

    get operator() {
        return '^^';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class Lean_lor extends LeanLogic {
    static input_priority = 30;

    get stack_priority() {
        return 29;
    }

    get operator() {
        return '∨';
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.rhs && caret instanceof LeanCaret) {
            if (indent >= this.indent) {
                let ind = indent;
                if (ind === this.indent) ind = this.indent + 2;
                this.hanging_indentation = true;
                caret.indent = ind;
                return caret;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }
}

export class Lean_land extends LeanLogic {
    static input_priority = 35;

    get stack_priority() {
        return 34;
    }

    get operator() {
        return '∧';
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }
}

/** `⊆`. */
export class Lean_subseteq extends LeanBinaryBoolean {
    static input_priority = 50;

    get operator() {
        return '⊆';
    }
}

/** `⊂`. */
export class Lean_subset extends LeanBinaryBoolean {
    static input_priority = 50;

    get operator() {
        return '⊂';
    }
}

/** `⊇`. */
export class Lean_supseteq extends LeanLogic {
    static input_priority = 50;

    get operator() {
        return '⊇';
    }
}

/** `⊃`. */
export class Lean_supset extends LeanLogic {
    static input_priority = 50;

    get operator() {
        return '⊃';
    }
}



export class LeanStatements extends LeanArgs {
    get stack_priority() {
        return 19;
    }

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

    insert_if(caret) {
        if (!(caret instanceof LeanCaret)) return undefined;
        const last = this.args[this.args.length - 1];
        if (last !== caret) return undefined;
        this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
        return caret;
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

    is_indented() {
        return false;
    }

    isProp(vars) {
        const args = this.args;
        if (args.length === 1) return args[0].isProp?.(vars);
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

    set_line(line) {
        return leanMultipleLineSetLine(this, line);
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
 * Echo term proofs: `String(proof)` often already includes `proof.indent` spaces; `indentText` would add
 * `proofInd` again and widen the line so newline scanning picks a larger continuation indent and folds
 * the proof into `LeanAssign` (round-trip mismatch).
 * @param {string} s
 */
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
 * @param {(s: string, ind: number) => string} indentText
 * @returns {{ cmts: Lean[], proofStr: string, endJ: number, proofIsTactic: boolean } | null}
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



// --- LeanModule::render2vue / merge_proof (server/lean/compiler/render2vue.mjs) ---
/** Escape a single line for use inside `\\text{...}` in KaTeX (render2vue). */
function escapeLatexTextForRender2vue(s) {
    return String(s)
        .replace(/\\/g, '\\textbackslash{}')
        .replace(/\{/g, '\\{')
        .replace(/\}/g, '\\}')
        .replace(/\$/g, '\\$')
        .replace(/&/g, '\\&')
        .replace(/#/g, '\\#')
        .replace(/\^/g, '\\textasciicircum{}')
        .replace(/_/g, '\\_')
        .replace(/%/g, '\\%')
        .replace(/~/g, '\\textasciitilde{}');
}

/** @param {import('../../../static/js/parser/lean.js').Lean} node */
function nameOf(node) {
    return node && node.constructor && node.constructor.name;
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
 * Extract attribute names from LeanAttribute (e.g. @[main] → ['main']).
 * Handles both LeanBracket and LeanArgsSpaceSeparated (from push_left).
 */
function extractAttribute(attr) {
    if (!attr) return null;
    let a = /** @type {*} */ (attr).arg;
    if (nameOf(a) === 'LeanArgsSpaceSeparated') {
        const bracket = a.args.find((x) => nameOf(x) === 'LeanBracket');
        a = bracket || null;
    }
    if (!a || nameOf(a) !== 'LeanBracket') return null;
    a = /** @type {*} */ (a).arg;
    if (a instanceof LeanArgsSpaceSeparated)
        return a.args.map((x) => strStmt(x)).filter(Boolean);
    if (a instanceof LeanToken) return [strStmt(a)];
    return null;
}

/**
 * PHP `escape_specials` (php/parser/lean.php ~9331–9341).
 * @param {string} token
 */
function escapeSpecials(token) {
    return token.replace(/^(\w+?)_(.+)/, (_m, head, tail) => {
        const escTail = tail.replace(/[{}_]/g, (c) => `\\${c}`);
        return head.length === 1 ? `${head}_{${escTail}}` : `${head}\\_${escTail}`;
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
        while (args.length && nameOf(args[args.length - 1]) === 'Lean_rightarrow') {
            const end = args[args.length - 1];
            args.splice(args.length - 1, 1, /** @type {*} */ (end).lhs, /** @type {*} */ (end).rhs);
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
    for (const brace of implicit) {
        if (nameOf(brace) === 'LeanBrace') {
            const colon = /** @type {*} */ (brace).arg;
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

/**
 * PHP `std\zipped` for two arrays (php/std.php ~1856+).
 * @template T, U
 * @param {T[]} a
 * @param {U[]} b
 * @returns {[T, U][]}
 */
function zipped(a, b) {
    const n = Math.min(a.length, b.length);
    /** @type {[T, U][]} */
    const out = [];
    for (let i = 0; i < n; ++i) out.push([a[i], b[i]]);
    return out;
}

/**
 * Build a map from let-binding names to their RHS AST nodes.
 * Used to expand `_` holes in denote tactics (e.g. denote h_Ξ_def : Ξ = _).
 * @param {import('../../../static/js/parser/lean.js').Lean[]} implyStmts
 * @returns {Record<string, import('../../../static/js/parser/lean.js').Lean>}
 */
function buildLetBindings(implyStmts) {
    const bindings = {};
    if (!implyStmts?.length) return bindings;
    for (const stmt of implyStmts) {
        if (nameOf(stmt) !== 'Lean_let' && nameOf(stmt) !== 'Lean_have') continue;
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
            nameNode = arg.rhs?.lhs;
            rhsNode = arg.rhs?.rhs;
        }
        if (nameNode && rhsNode) {
            const name = strStmt(nameNode).trim();
            if (name) bindings[name] = rhsNode;
        }
    }
    return bindings;
}

/**
 * Compute LaTeX for a denote tactic when the RHS hole can be expanded from let bindings.
 * E.g. denote h_Ξ_def : Ξ = _ with let Ξ := (1:...).band_part (l-1) (u-1) yields Ξ = 1.band_part ...
 * Handles both LeanColon (denote h_X : Y = _) and LeanTactic(denote) with LeanColon arg.
 * @param {import('../../../static/js/parser/lean.js').Lean} stmt
 * @param {Record<string, unknown>} syntax
 * @returns {string | null}
 */
function denoteLatexFromLetBindings(stmt, syntax) {
    let tag = '';
    let prop = null;
    if (stmt instanceof LeanColon && stmt.lhs && stmt.rhs) {
        prop = stmt.rhs;
        const lhsStr = strStmt(stmt.lhs).trim();
        const m = lhsStr.match(/^denote\s+(.+)$/);
        tag = m ? m[1].trim() : lhsStr;
    } else if (stmt instanceof LeanTactic && stmt.tacticName === 'denote') {
        const arg = stmt.arg;
        if (arg instanceof LeanColon && arg.lhs && arg.rhs) {
            prop = arg.rhs;
            tag = strStmt(arg.lhs).trim().replace(/^denote\s+/, '') || strStmt(arg.lhs).trim();
        }
    }
    if (!prop || !tag) return null;
    const isHole = (n) => {
        if (n instanceof LeanToken && n.text === '_') return true;
        if (n?.args) {
            const nonCaret = n.args.filter((a) => !(a instanceof LeanCaret));
            return nonCaret.length === 1 && nonCaret[0] instanceof LeanToken && nonCaret[0].text === '_';
        }
        return false;
    };
    let lhsNode = null;
    let rhsNode = null;
    if (prop?.lhs != null && prop?.rhs != null) {
        lhsNode = prop.lhs;
        rhsNode = prop.rhs;
    } else if (prop?.args?.length >= 2) {
        lhsNode = prop.args[0];
        rhsNode = prop.args[1];
    }
    if (!lhsNode || !isHole(rhsNode)) return null;
    const letBindings = syntax?.letBindings ?? {};
    const lhsName = strStmt(lhsNode).trim();
    let expansion = letBindings[lhsName];
    if (!expansion && lhsName.endsWith("'")) {
        expansion = letBindings[lhsName.slice(0, -1)];
    }
    if (!expansion || typeof expansion.toLatex !== 'function') return null;
    const lhsLatex = lhsNode.toLatex(syntax);
    const rhsLatex = expansion.toLatex(syntax);
    const taggedTag = escapeLatexTextForRender2vue(tag);
    return `${lhsLatex} = ${rhsLatex}\\tag*{\\text{${taggedTag}}}`;
}

/**
 * Port of `LeanModule::merge_proof` (php/parser/lean.php ~4685–4725).
 * When echo is false, computes LaTeX for denote tactics from let bindings (syntax.letBindings).
 * @param {import('../../../static/js/parser/lean.js').LeanArgs} proof
 * @param {boolean} echo
 * @param {Record<string, unknown>} [syntax]
 */
function leanModuleMergeProof(proof, echo, syntax = {}) {
    let list = proof.args;
    if (list[0] instanceof LeanLineComment && list[0].text === 'proof') list = list.slice(1);
    list = list.filter((s) => !(s instanceof LeanCaret));
    /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
    const statements = [];
    for (const s of list) statements.push(...s.split(syntax));

    /** @type {[import('../../../static/js/parser/lean.js').Lean[], string | null][]} */
    const code = [];
    /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
    let last = [];

    if (echo) {
        for (const stmt of statements) {
            const echoNode = stmt instanceof LeanTactic ? stmt.getEcho() : undefined;
            if (echoNode) {
                code.push([last, typeof echoNode.line === 'number' ? null : echoNode.line]);
                last = [];
            } else last.push(stmt);
        }
    } else {
        for (const stmt of statements) {
            const isHave = nameOf(stmt) === 'Lean_have';
            if (isHave || stmt instanceof LeanTactic) {
                last.push(stmt);
                code.push([last, null]);
                last = [];
            } else last.push(stmt);
        }
    }
    if (last.length) code.push([last, null]);

    return code.map(([stmts, latex]) => {
        let stepLatex = null;
        if (!echo && !latex) {
            const expanded = stmts
                .map((st) => denoteLatexFromLetBindings(st, syntax))
                .filter(Boolean);
            if (expanded.length === 1) stepLatex = expanded[0];
            else if (expanded.length > 1) stepLatex = `\\begin{gather}\n${expanded.join(' \\\\\n')}\n\\end{gather}`;
            else {
                const fallback = stmts
                    .map((st) => {
                        try {
                            const l = typeof st.toLatex === 'function' ? st.toLatex(syntax) : null;
                            return l && typeof l === 'string' && l.trim() ? l : null;
                        } catch {
                            return null;
                        }
                    })
                    .filter(Boolean);
                if (fallback.length === 1) stepLatex = fallback[0];
                else if (fallback.length > 1) stepLatex = `\\begin{gather}\n${fallback.join(' \\\\\n')}\n\\end{gather}`;
            }
        }
        return {
            lean: unindentTwo(stmts.map((st) => strStmt(st)).join('\n')),
            latex: latex ?? stepLatex,
        };
    });
}

/**
 * Port of `LeanModule::render2vue` (php/parser/lean.php ~4912–5188).
 * @param {LeanModule} mod
 * @param {boolean} echo
 * @param {{ value?: boolean } | null} [modify]
 * @param {Record<string, unknown>} [syntax]
 */
function leanModuleRender2vue(mod, echo, modify = null, syntax = {}) {
    if (!echo) mod.relocate_last_comment();

    /** @type {string[]} */
    const import_ = [];
    /** @type {unknown[]} */
    const open = [];
    /** @type {unknown[]} */
    const set_option = [];
    /** @type {string[]} */
    const def = [];
    /** @type {unknown[]} */
    const lemma = [];
    /** @type {Record<string, string>} */
    const date = {};
    /** @type {unknown[]} */
    const error = [];
    /** @type {string | null} */
    let comment = null;

    const args = mod.args;
    for (let idx = 0; idx < args.length; idx++) {
        const stmt = args[idx];
        if (nameOf(stmt) === 'Lean_import') {
            import_.push(normalizeImportStr(strStmt(/** @type {*} */ (stmt).arg)));
        } else if (stmt instanceof Lean_lemma) {
            /** @type {import('../../../static/js/parser/lean.js').LeanAssign | null} */
            let assignment = stmt.assignment instanceof LeanAssign ? stmt.assignment : null;
            /** @type {number} */
            let assignIdx = -1;
            if (!assignment) {
                let proofStart = args.length;
                for (let k = idx + 1; k < args.length; k++) {
                    const x = args[k];
                    if (x instanceof LeanLineComment && /** @type {*} */ (x).text === 'proof') {
                        proofStart = k;
                        break;
                    }
                    if (x && nameOf(x) === 'LeanTactic') {
                        proofStart = k;
                        break;
                    }
                }
                for (let j = idx + 1; j < proofStart; j++) {
                    const cand = args[j];
                    if (cand instanceof LeanAssign) {
                        const lhs = cand.lhs;
                        if (lhs && (nameOf(lhs) === 'Lean_let' || nameOf(lhs) === 'Lean_have')) continue;
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
                let declspec = assignment.lhs;
                let flatInstImplicit = [];
                let flatExplicit = '';
                let flatGiven = null;
                /** @type {import('../../../static/js/parser/lean.js').Lean[]} */
                let flatImplyStmts = [];
                if (assignIdx >= 0) {
                    let firstAssign = assignIdx;
                    for (let k = idx + 1; k < assignIdx; k++) {
                        if (args[k] instanceof LeanAssign) {
                            firstAssign = k;
                            break;
                        }
                    }
                    /** Collect Lean_let/Lean_have between lemma and main assignment for imply (JS parser may have them as siblings). */
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (nameOf(s) === 'Lean_let' || nameOf(s) === 'Lean_have') {
                            flatImplyStmts.push(s);
                        }
                    }
                    for (let k = idx + 1; k < firstAssign; k++) {
                        const s = args[k];
                        if (nameOf(s) === 'LeanBracket') {
                            flatInstImplicit.push(strStmt(s));
                            continue;
                        }
                        /** (A : T) and (V : T) — recurse into LeanArgsSpaceSeparated or handle LeanParenthesis(LeanColon). */
                        const collectParenColons = (/** @type {*} */ n) => {
                            if (!n) return;
                            if (nameOf(n) === 'LeanParenthesis' && n.arg instanceof LeanColon) {
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
                        if (nameOf(s) === 'LeanParenthesis' && s.arg instanceof LeanColon) {
                            collectParenColons(s);
                            continue;
                        }
                        if (nameOf(s) === 'LeanArgsSpaceSeparated' || nameOf(s) === 'LeanArgsNewLineSeparated') {
                            collectParenColons(s);
                            continue;
                        }
                        if (nameOf(s) === 'LeanColon' && s.lhs) {
                            const lb = s.lhs;
                            if (nameOf(lb) === 'LeanBracket') {
                                const inner = /** @type {*} */ (lb).arg;
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
                            } else if (nameOf(lb) === 'LeanParenthesis' || (nameOf(lb) === 'LeanColon' && lb.rhs)) {
                                if (nameOf(s.rhs) === 'LeanStatements' || nameOf(s.rhs) === 'LeanArgsNewLineSeparated') {
                                    const inner = lb;
                                    if (nameOf(inner) === 'LeanColon' && inner.lhs && inner.rhs) {
                                        const innerLhs = inner.lhs;
                                        if (nameOf(innerLhs) === 'LeanParenthesis' && inner.rhs) {
                                            if (flatGiven === null) flatGiven = [];
                                            const varPart = strStmt(
                                                /** @type {*} */ (innerLhs).arg
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
                                    if (nameOf(lb) === 'LeanParenthesis' && s.rhs) {
                                        const varPart = strStmt(/** @type {*} */ (lb).arg).trim();
                                        const typePart = normalizeTypeStr(strStmt(s.rhs));
                                        leanStr = `(${varPart} : ${typePart})`;
                                    } else {
                                        leanStr = strStmt(s).trim();
                                        if (nameOf(lb) === 'LeanParenthesis' && !leanStr.startsWith('('))
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
                    const rhsArgs = rhsColon && 'args' in rhsColon ? /** @type {{ args?: unknown[] }} */ (rhsColon).args : null;
                    const isImplyList =
                        rhsArgs &&
                        Array.isArray(rhsArgs) &&
                        rhsArgs.length > 0 &&
                        (rhsArgs[0] instanceof LeanLineComment ||
                            nameOf(rhsArgs[0]) === 'Lean_let' ||
                            nameOf(rhsColon) === 'LeanArgsSpaceSeparated' ||
                            nameOf(rhsColon) === 'LeanStatements' ||
                            nameOf(rhsColon) === 'LeanArgsNewLineSeparated');
                    if (!rhsColon || !rhsArgs || !isImplyList) {
                        if (
                            assignIdx >= 0 &&
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
                    let imply = /** @type {import('../../../static/js/parser/lean.js').Lean[]} */ (
                        /** @type {{ args: import('../../../static/js/parser/lean.js').Lean[] }} */ (rhsColon).args.slice()
                    );
                    if (imply[0] instanceof LeanLineComment && imply[0].text === 'imply') imply.shift();

                    const proof0 = assignment.rhs;
                    const by =
                        proof0 instanceof LeanBy
                            ? 'by'
                            : nameOf(proof0) === 'LeanCalc'
                              ? 'calc'
                              : '';
                    const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));

                    let implyLatex;
                    if (imply.length > 1 && nameOf(imply[0]) === 'Lean_let') {
                        implyLatex =
                            '\\begin{align}\n' +
                            imply
                                .map((st) => `&${st.toLatex(syntax)}&& `)
                                .join('\\\\\n') +
                            '\n\\end{align}';
                    } else {
                        implyLatex = imply.map((st) => st.toLatex(syntax)).join('\n');
                    }
                    const assignSuffix = ' :=' + (by ? ` ${by}` : '');
                    implyLatex += `\\tag*{${assignSuffix}}`;
                    const implyOut = { lean: implyLean + assignSuffix, latex: implyLatex };

                    declspec = declspec.lhs;
                    /** @type {string[] | null} */
                    let collectedExplicit = null;
                    /** @type {import('../../../static/js/parser/lean.js').Lean} */
                    let name;
                    if (declspec instanceof LeanToken || declspec instanceof LeanProperty) {
                        name = declspec;
                        declspec = /** @type {*} */ ([]);
                    } else if (
                        declspec &&
                        declspec.args &&
                        declspec.args.length >= 2 &&
                        !(declspec.args[0] && nameOf(declspec.args[0]) === 'LeanParenthesis')
                    ) {
                        /** PHP [name, binders]; skip when args are binders (LeanParenthesis) not name+binders. */
                        const dargs = declspec.args;
                        name = dargs[0];
                        const binders = dargs[1] && dargs[1].args ? dargs[1].args : (dargs.length > 2 ? dargs.slice(1) : []);
                        declspec = binders;
                    } else if (declspec && (declspec.lhs != null || declspec.args)) {
                        /** Parser may produce LeanArgsIndented/LeanArgsSpaceSeparated for (A:T)(V:T). Extract LeanParenthesis nodes. */
                        const collectParens = (/** @type {*} */ n) => {
                            if (!n) return [];
                            if (nameOf(n) === 'LeanParenthesis') return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(declspec);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = /** @type {*} */ (p).arg;
                                if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) lines[lines.length - 1] += ' :';
                            collectedExplicit = lines;
                        }
                        name = stmt.assignment;
                        declspec = /** @type {*} */ ([]);
                    } else {
                        name = stmt.assignment;
                        declspec = /** @type {*} */ ([]);
                    }

                    /** @type {string[]} */
                    const instImplicit = [];
                    /** @type {unknown[]} */
                    const implicit = [];
                    /** @type {string[]} */
                    let explicit = [];
                    /** @type {number | null} */
                    let given = null;
                    /** @type {string[]} */
                    let default_ = [];
                    /** @type {string[]} */
                    const decidables = [];

                    const declList = declspec;
                    for (let i = 0; i < declList.length; ++i) {
                        const st = declList[i];
                        if (nameOf(st) === 'LeanBracket') {
                            instImplicit.push(strStmt(st));
                            const ia = /** @type {*} */ (st).arg;
                            if (ia instanceof LeanArgsSpaceSeparated && ia.args.length === 2) {
                                const [l, r] = ia.args;
                                if (l instanceof LeanToken && l.text === 'Decidable' && r instanceof LeanToken)
                                    decidables.push(strStmt(r));
                            }
                        } else if (nameOf(st) === 'LeanBrace') {
                            st.toLatex(syntax);
                            implicit.push(st);
                        } else if (st instanceof LeanArgsSpaceSeparated) {
                            if (nameOf(st.args[0]) === 'LeanBracket') instImplicit.push(strStmt(st));
                            else if (nameOf(st.args[0]) === 'LeanBrace') implicit.push(st);
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
                            const inner = /** @type {*} */ (st).arg;
                            if (inner instanceof LeanColon) {
                                declList.splice(
                                    i,
                                    0,
                                    new LeanLineComment('given', st.indent, /** @type {*} */ (st).parent),
                                );
                                if (modify) modify.value = true;
                                ++i;
                            }
                            given = i;
                            break;
                        }
                    }

                    /** @type {unknown} */
                    let givenOut = null;
                    if (given !== null) {
                        let givenSlice = declList.slice(/** @type {number} */ (given));
                        /** @type {([string, string] | null)[]} */
                        const latex = [];
                        let givenStart = null;
                        let givenStop = null;
                        /** @type {Record<string, unknown> | null} */
                        let vars = null;

                        for (const [i, st] of givenSlice.entries()) {
                            if (st instanceof LeanParenthesis) {
                                const colon = /** @type {*} */ (st).arg;
                                if (colon instanceof LeanColon) {
                                    const prop = colon.rhs;
                                    if (vars == null) {
                                        vars = parseVars(implicit);
                                        for (const p of decidables) vars[p] = 'Prop';
                                    }
                                    if (prop.isProp(vars)) {
                                        latex.push([prop.toLatex(syntax), latexTag(strStmt(colon.lhs))]);
                                        if (givenStart === null) givenStart = i;
                                    } else if (givenStart !== null) {
                                        givenStop = i;
                                        break;
                                    }
                                } else if (nameOf(colon) === 'LeanAssign') {
                                    break;
                                }
                            } else if (st.is_comment()) latex.push(null);
                            else if (nameOf(st) === 'LeanBrace') {
                                const pivot = i;
                                const par = new LeanParenthesis(/** @type {*} */ (st).arg, st.indent, st.parent);
                                par.is_closed = true;
                                givenSlice[pivot] = par;
                                break;
                            } else if (st instanceof LeanCaret) {
                                // skip
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
                                const L = latex;
                                if (L.length) {
                                    const lastPair = L[L.length - 1];
                                    if (lastPair) lastPair[1] += ' :';
                                }
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
                                    ? `${pair[0]}\\tag*{\\$${pair[1]}$}`
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

                    const proof = assignment.rhs;
                    /** @type {unknown} */
                    let proofOut;
                    /** When rhs is LeanCaret, proof statements live as siblings after the assignment. */
                    let proofNode = proof;
                    if (
                        assignIdx >= 0 &&
                        !(proof instanceof LeanBy || nameOf(proof) === 'LeanCalc') &&
                        (proof instanceof LeanCaret || !(proof?.args && proof.args.length))
                    ) {
                        let end = assignIdx + 1;
                        for (; end < args.length; ++end) {
                            const x = args[end];
                            if (x instanceof LeanLineComment && /^(created|updated)\s/i.test(String(/** @type {*} */ (x).text || '')))
                                break;
                        }
                        proofNode = { args: args.slice(assignIdx + 1, end) };
                    }
                    syntax.letBindings = buildLetBindings(imply?.length ? imply : flatImplyStmts);
                    if (by) {
                        proofOut = { [by]: leanModuleMergeProof(proofNode?.arg ?? proofNode, echo, syntax) };
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
                } else if (declspec && (typeof declspec.toLatex === 'function' || flatImplyStmts?.length > 0)) {
                    const proof0 = assignment.rhs;
                    const by =
                        proof0 instanceof LeanBy
                            ? 'by'
                            : nameOf(proof0) === 'LeanCalc'
                              ? 'calc'
                              : '';
                    /** When declspec is LeanColon, extract explicit (A:T)(V:T) from lhs and imply from rhs. */
                    let simpleExplicit = flatExplicit;
                    let implyNode = declspec;
                    if (declspec instanceof LeanColon && declspec.lhs && !flatExplicit) {
                        const inner = declspec.lhs;
                        /** Binders may be in inner (LeanColon), inner.lhs (LeanArgsIndented), or inner.lhs.lhs. */
                        const binderNode =
                            inner.lhs instanceof LeanColon
                                ? inner.lhs.lhs
                                : inner;
                        const collectParens = (/** @type {import('../../../static/js/parser/lean.js').Lean} */ n) => {
                            if (!n) return [];
                            if (nameOf(n) === 'LeanParenthesis') return [n];
                            const a = n.args ?? (n.lhs != null && n.rhs != null ? [n.lhs, n.rhs] : []);
                            return a.flatMap(collectParens);
                        };
                        const parens = collectParens(binderNode);
                        if (parens.length > 0) {
                            const lines = parens.map((p) => {
                                const arg = /** @type {*} */ (p).arg;
                                if (arg instanceof LeanColon && arg.lhs && arg.rhs)
                                    return `(${strStmt(arg.lhs).trim()} : ${normalizeTypeStr(strStmt(arg.rhs))})`;
                                return strStmt(p);
                            });
                            if (lines.length) {
                                lines[lines.length - 1] += ' :';
                                simpleExplicit = lines.join('\n');
                            }
                        }
                        /** Imply = LeanStatements from inner.rhs, or inner.lhs.rhs when triple-nested. */
                        const innerLhs = inner.lhs;
                        implyNode =
                            (innerLhs && innerLhs.rhs && (nameOf(innerLhs.rhs) === 'LeanStatements' || nameOf(innerLhs.rhs) === 'LeanArgsNewLineSeparated'))
                                ? innerLhs.rhs
                                : inner.rhs || declspec;
                    }
                    let implyOut;
                    if (flatImplyStmts && flatImplyStmts.length > 0) {
                        const imply = [...flatImplyStmts, assignment.lhs];
                        const implyLean = unindentTwo(imply.map((s) => strStmt(s)).join('\n'));
                        let implyLatex;
                        if (imply.length > 1 && (nameOf(imply[0]) === 'Lean_let' || nameOf(imply[0]) === 'Lean_have')) {
                            implyLatex =
                                '\\begin{align}\n' +
                                imply
                                    .map((st) => `&${st.toLatex ? st.toLatex(syntax) : strStmt(st)}&& `)
                                    .join('\\\\\n') +
                                '\n\\end{align}';
                        } else {
                            implyLatex = imply
                                .map((st) => (st.toLatex ? st.toLatex(syntax) : strStmt(st)))
                                .join('\n');
                        }
                        implyLatex += `\\tag*{ :=${by ? ` ${by}` : ''}}`;
                        implyOut = { lean: implyLean + ' :=' + (by ? ` ${by}` : ''), latex: implyLatex };
                    } else {
                        const implyLean = unindentTwo(strStmt(implyNode)) + ' :=' + (by ? ` ${by}` : '');
                        const implyLatex =
                            (implyNode.toLatex ? implyNode.toLatex(syntax) : strStmt(implyNode)) +
                            `\\tag*{ :=${by ? ` ${by}` : ''}}`;
                        implyOut = { lean: implyLean, latex: implyLatex };
                    }
                    syntax.letBindings = buildLetBindings(flatImplyStmts ?? []);
                    const proof = assignment.rhs;
                    let proofOut;
                    const proofArg = proof && typeof proof === 'object' && 'arg' in proof ? proof.arg : proof;
                    const hasProofArgs = proofArg && typeof proofArg === 'object' && Array.isArray(proofArg.args);
                    if (by) {
                        proofOut = { [by]: hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [] };
                    } else {
                        proofOut = hasProofArgs ? leanModuleMergeProof(proofArg, echo, syntax) : [{ lean: strStmt(proof || ''), latex: null }];
                    }
                    let attribute = extractAttribute(stmt.attribute);
                    const name = stmt.assignment;
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
            def.push(strStmt(stmt));
        } else if (nameOf(stmt) === 'Lean_open') {
            let o = /** @type {*} */ (stmt).arg;
            if (o instanceof LeanArgsSpaceSeparated) {
                if (o.args.length === 2 && o.args[1] instanceof LeanParenthesis) {
                    const defs = /** @type {*} */ (o.args[1]).arg;
                    open.push({
                        [strStmt(o.args[0])]:
                            defs instanceof LeanArgsSpaceSeparated
                                ? defs.args.map((a) => strStmt(a))
                                : [strStmt(/** @type {*} */ (defs).arg)],
                    });
                } else open.push(o.args.map((a) => strStmt(a)).filter((s) => s.trim()));
            } else open.push([strStmt(/** @type {*} */ (o).text)]);
        } else if (nameOf(stmt) === 'Lean_set_option') {
            const a = /** @type {*} */ (stmt).arg;
            if (a instanceof LeanArgsSpaceSeparated) set_option.push(a.args.map((x) => strStmt(x)));
        } else if (stmt instanceof LeanLineComment) {
            const m = /^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/.exec(stmt.text);
            if (m) date[m[1]] = m[2];
            else comment = stmt.text;
        } else if (nameOf(stmt) === 'LeanBlockComment') {
            comment = /** @type {*} */ (stmt).text;
        }
    }

    return {
        imports: import_,
        open,
        set_option,
        def,
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
        return parts.reduce((carry, tok) => {
            const t = new LeanToken(tok, 0, 0);
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
        const args = this.args;
        for (let i = 0; i < args.length; i++) args[i].echo?.();
    }

    echo2vue(_leanFile) {
        throw new Error(
            'LeanModule.echo2vue is not implemented in JavaScript (PHP uses filesystem and Lean CLI).',
        );
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
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
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
     * when the proof is tactic-shaped, pad the assign line with `assign.indent`, dedent term proofs before
     * re-indenting (so newline scanning does not over-read continuation indent), and when a `LeanColon`
     * (indented, module child) is immediately followed by such an echo assign, prefix the colon block’s
     * first line with `colon.indent` so re-parse keeps the assign at module scope.
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
                        // Rhs is still a caret: the lemma was parsed as `:=` then proof lines (no `by` token).
                        // Do not print ` by` or re-parse will build `LeanBy` and the AST drifts.
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
                    const ind = Math.max(a.indent ?? 0, next.indent ?? 0);
                    const as = String(a);
                    const ns = String(next);
                    const join = as.endsWith('\n') ? '' : '\n';
                    parts.push(indentText(`${as}${join}${ns}`, ind));
                    continue;
                }
            }
            if (a instanceof LeanColon && a.parent === this) {
                const ind = a.indent ?? 0;
                if (ind > 0) {
                    let k = i + 1;
                    while (k < args.length && args[k] instanceof LeanCaret) k++;
                    const next = args[k];
                    const echoTail =
                        next instanceof LeanAssign &&
                        next.rhs instanceof LeanCaret &&
                        consumeEchoAssignProofTail(args, k + 1, indentText);
                    if (echoTail) {
                        const lines = String(a).split('\n');
                        if (lines[0] !== '') lines[0] = ' '.repeat(ind) + lines[0];
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
                const ind = prev instanceof Lean_have ? prev.indent ?? 0 : 0;
                if (ind > 0) out = ' '.repeat(ind) + out;
            }
            parts.push(out);
        }
        return parts.join('\n');
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
            const $new = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
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

export class LeanRightarrow extends LeanBinary {
    static input_priority = 19;

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

export class Lean_mapsto extends LeanBinary {
    get stack_priority() {
        return 23;
    }

    get operator() {
        return '↦';
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

/** Unary `←`. */
class Lean_leftarrow extends LeanUnary {
    get operator() {
        return '←';
    }
    strFormat() {
        return `${this.operator} %s`;
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

    static echo_part(part, token) {
        const echo = new LeanTactic('echo', token.clone(), part.indent, part.level);
        if (part instanceof LeanStatements) part.unshift(echo);
        else if (part.parent)
            part.parent.replace(part, new LeanStatements([echo, part], part.indent, part.level));
    }
}

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
        if (this.cache.size != null) return /** @type {number} */ (this.cache.size);
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
        cur = /** @type {Record<string, unknown>} */ (cur)[k];
    }
    return cur;
}

export class LeanArgsSpaceSeparated extends LeanArgs {
    static input_priority = 80;

    constructor(args, indent, level, parent = null) {
        super(args, indent, level, parent);
        this.cache = null;
    }

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

    /**
     * @param {Record<string, unknown>} vars
     * @param {Lean} arg
     * @returns {unknown}
     */
    get_type(vars, arg) {
        if (arg instanceof LeanToken) return vars[arg.text] ?? '';
        if (arg instanceof LeanArgsSpaceSeparated) {
            const segs = arg.args.map((a) => this.get_type(vars, a)).map((x) => String(x ?? ''));
            return leanVarsGetitem(vars, segs);
        }
        return '';
    }

    insert(caret, func, type) {
        const last = this.args[this.args.length - 1];
        if (last === caret && !(caret instanceof LeanCaret) && type !== 'modifier') {
            const c = new LeanCaret(this.indent, caret.level);
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.push(new Ctor(c, c.indent, c.level));
            return c;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_unary(caret, func) {
        const last = this.args[this.args.length - 1];
        if (last !== caret) throw new Error(`insert_unary is unexpected for ${this.constructor.name}`);
        const indent = this.indent;
        const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
        if (caret instanceof LeanCaret) {
            this.replace(caret, new Ctor(caret, indent, caret.level));
            return caret;
        }
        const c = new LeanCaret(indent, caret.level);
        this.push(new Ctor(c, indent, this.level));
        return c;
    }

    insert_word(caret, word) {
        const newTok = new LeanToken(word, this.indent, caret.level);
        this.push(newTok);
        return newTok;
    }

    is_Abs() {
        const args = this.args;
        const func = args[0];
        return func instanceof LeanToken && args.length === 2 && func.text === 'abs';
    }

    is_Bool() {
        const args = this.args;
        const func = args[0];
        return (
            func instanceof LeanProperty &&
            func.rhs instanceof LeanToken &&
            func.rhs.text === 'toNat' &&
            func.lhs instanceof LeanToken &&
            func.lhs.text === 'Bool'
        );
    }

    is_indented() {
        const parent = this.parent;
        return (
            parent instanceof LeanStatements ||
            parent instanceof LeanArgsCommaNewLineSeparated ||
            parent instanceof LeanArgsNewLineSeparated ||
            (parent instanceof LeanIte && (this === parent.then || this === parent.else))
        );
    }

    isProp(vars) {
        const targs = this.args.map((a) => this.get_type(vars, a));
        const type0 = targs[0];
        if (type0 != null && typeof type0 === 'object') {
            const rest = targs.slice(1).map((x) => String(x ?? ''));
            if (leanVarsGetitem(/** @type {Record<string, unknown>} */ (type0), rest) === 'Prop') return true;
        }
        const func = this.args[0];
        if (func instanceof LeanToken) {
            switch (func.text) {
                case 'HEq':
                case 'Infinitesimal':
                case 'Infinite':
                case 'InfinitePos':
                case 'InfiniteNeg':
                    return true;
                default:
            }
        }
    }

    is_space_separated() {
        return true;
    }

    /**
     * @param {Record<string, unknown> | null} [syntax]
     * @returns {string[]}
     */
    latexArgs(syntax = null) {
        const syn = syntax ?? {};
        const args = this.args;
        const func = args[0];
        if (this.is_Abs()) {
            const stripped = this.strip_parenthesis();
            return [stripped[1].toLatex(syn)];
        }
        if (func instanceof LeanToken) {
            const fn = func.text;
            syn[fn] = true;
            switch (args.length) {
                case 2:
                    switch (fn) {
                        case 'exp':
                        case 'cexp': {
                            const s = this.strip_parenthesis();
                            return [s[1].toLatex(syn)];
                        }
                        case 'arcsin':
                        case 'arccos':
                        case 'arctan':
                        case 'sin':
                        case 'cos':
                        case 'tan':
                        case 'arg':
                        case 'arcsec':
                        case 'arccsc':
                        case 'arccot':
                        case 'arcsinh':
                        case 'arccosh':
                        case 'arctanh':
                        case 'arccoth': {
                            let arg = args[1];
                            if (arg instanceof LeanParenthesis && arg.arg instanceof LeanDiv) arg = arg.arg;
                            return [arg.toLatex(syn)];
                        }
                        case 'Ici':
                        case 'Iic':
                        case 'Ioi':
                        case 'Iio':
                        case 'Zeros':
                        case 'Ones': {
                            const s = this.strip_parenthesis();
                            return [s[1].toLatex(syn)];
                        }
                        default:
                    }
                    break;
                case 3:
                    switch (fn) {
                        case 'Ioc':
                        case 'Ioo':
                        case 'Icc':
                        case 'Ico': {
                            const s = this.strip_parenthesis();
                            return [s[1].toLatex(syn), s[2].toLatex(syn)];
                        }
                        case 'KroneckerDelta':
                            return [args[1].toLatex(syn), args[2].toLatex(syn)];
                        default:
                    }
                    break;
                default:
            }
        } else if (this.is_Bool()) {
            const stripped = this.strip_parenthesis();
            return [stripped[1].toLatex(syn)];
        }
        return super.latexArgs(syn);
    }

    latexFormat() {
        const args = this.args;
        const func = args[0];
        if (this.is_Abs()) return '\\left|{%s}\\right|';
        if (func instanceof LeanToken) {
            switch (args.length) {
                case 2:
                    switch (func.text) {
                        case 'exp':
                        case 'cexp':
                            return '{\\color{RoyalBlue} e} ^ {%s}';
                        case 'arcsin':
                        case 'arccos':
                        case 'arctan':
                        case 'sin':
                        case 'cos':
                        case 'tan':
                        case 'arg':
                            return `\\${func.text} {%s}`;
                        case 'arcsec':
                        case 'arccsc':
                        case 'arccot':
                        case 'arcsinh':
                        case 'arccosh':
                        case 'arctanh':
                        case 'arccoth':
                            return `${func.text}\\ {%s}`;
                        case 'Ici':
                            return '\\left[%s, \\infty\\right)';
                        case 'Iic':
                            return '\\left(-\\infty, %s\\right]';
                        case 'Ioi':
                            return '\\left(%s, \\infty\\right)';
                        case 'Iio':
                            return '\\left(-\\infty, %s\\right)';
                        case 'Zeros':
                            return '\\mathbf{0}_{%s}';
                        case 'Ones':
                            return '\\mathbf{1}_{%s}';
                        default:
                    }
                    break;
                case 3:
                    switch (func.text) {
                        case 'Ioc':
                            return '\\left(%s, %s\\right]';
                        case 'Ioo':
                            return '\\left(%s, %s\\right)';
                        case 'Icc':
                            return '\\left[%s, %s\\right]';
                        case 'Ico':
                            return '\\left[%s, %s\\right)';
                        case 'KroneckerDelta':
                            return '\\delta_{%s %s}';
                        default:
                    }
                    break;
                default:
            }
        } else if (this.is_Bool()) {
            return '\\left|{%s}\\right|';
        } else if (func instanceof LeanProperty && func.rhs instanceof LeanToken) {
            if (func.rhs.text === 'fmod' && args.length === 2) return '{%s}{%s}';
        }
        const n = args.length;
        return Array(n)
            .fill('{%s}')
            .join('\\ ');
    }

    operand_count() {
        return this.args[0].operand_count();
    }

    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        if (this.parent instanceof LeanTactic) {
            let out = '';
            for (let i = 0; i < n; i++) {
                if (i > 0) out += this.args[i] instanceof LeanTactic ? '\n' : ' ';
                out += '%s';
            }
            return out;
        }
        return Array(n).fill('%s').join(' ');
    }

    /**
     * Leading `LeanCaret` stringifies to '' but `strFormat` still inserts a space before the next arg,
     * yielding `import  Foo` / `open  A` and unstable re-parse vs sources that use a single space.
     */
    toString() {
        const format = this.strFormat();
        const args = this.strArgs();
        const inner =
            args.length === 0
                ? format
                : String(format).format(...args.map((a) => (a instanceof Lean ? String(a) : a)));
        const body = inner.replace(/^\s+/, '');
        return (this.is_indented() ? ' '.repeat(this.indent) : '') + body;
    }

    tactic_block_info() {
        if (!this.cache) this.cache = {};
        if (this.cache.tactic_block_info != null)
            return /** @type {Record<number, LeanToken[]>} */ (this.cache.tactic_block_info);
        const nodes = this.construct_prefix_tree();
        let physic_index = 0;
        let logic_index = 0;
        for (const node of nodes) {
            node.traverse((n) => {
                /** @type {ParserPrefixExpr[] | null} */
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

    unique_token(indent) {
        const tokens = this.tokens_space_separated();
        if (!tokens.length) return undefined;
        const texts = tokens.map((t) => t.text);
        if (new Set(texts).size !== 1) return undefined;
        const token = tokens[0].clone();
        token.indent = indent;
        return token;
    }
}

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

    set_line(line) {
        return leanMultipleLineSetLine(this, line);
    }
}



export class LeanArgsIndented extends LeanBinary {
    get stack_priority() {
        if (this.parent instanceof LeanCalc) return 17;
        if (this.parent instanceof LeanQuantifier) return LeanRelational.input_priority + 1;
        return 47;
    }

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

    strFormat() {
        const sep = this.sep();
        return `%s${sep}%s`;
    }
}

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
        return leanMultipleLineSetLine(this, line);
    }
}


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
        this.only = undefined;
    }

    get stack_priority() {
        if (this.parent instanceof LeanBy) return LeanColon.input_priority;
        if (this.tacticName === 'obtain') return LeanAssign.input_priority - 1;
        return LeanAssign.input_priority;
    }

    get modifiers() {
        return this.args.slice(1);
    }

    get at() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanAt) return this.args[i];
        }
    }

    get with() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanWith) return this.args[i];
        }
    }

    get by() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanBy) return this.args[i];
        }
    }

    get arrow() {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof LeanRightarrow) return this.args[i];
        }
    }

    get func() {
        return this.tacticName;
    }

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

    /**
     * Port of `LeanTactic::getEcho`.
     * @returns {LeanTactic | undefined}
     */
    getEcho() {
        if (this.tacticName === 'echo') return this;
        if (this.tacticName === 'try' && this.arg instanceof LeanTactic && this.arg.tacticName === 'echo') return this.arg;
    }

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

    insert_comma(caret) {
        if (caret === this.arg) {
            if (
                caret instanceof LeanToken ||
                caret instanceof LeanBinary ||
                caret instanceof LeanPairedGroup
            ) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            if (caret instanceof LeanArgsCommaSeparated) {
                const $new = new LeanCaret(this.indent, caret.level);
                caret.push($new);
                return $new;
            }
        }
        return super.insert_comma(caret);
    }

    insert_line_comment(_caret, comment) {
        return this.push_line_comment(comment);
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (caret === this.arg) {
            if (this.indent < indent && caret instanceof LeanArgsSpaceSeparated) {
                const $new = new LeanCaret(this.indent, caret.level);
                caret.push($new);
                return $new;
            }
            if (next === '<') {
                const c = new LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    insert_only(caret) {
        if (caret !== this.args[this.args.length - 1]) {
            throw new Error(`LeanTactic.insert_only: unexpected for ${this.constructor.name}`);
        }
        this.only = true;
        return caret;
    }

    insert_semicolon(caret) {
        if (caret === this.arg) {
            if (this.is_inline_tactic_block()) {
                const $new = new LeanCaret(this.indent, caret.level);
                if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                else this.replace(caret, new LeanArgsSemicolonSeparated([caret, $new], this.indent, caret.level));
                return $new;
            }
            if (this.parent instanceof LeanBy) {
                const $new = new LeanCaret(this.indent, caret.level);
                if (caret instanceof LeanArgsSemicolonSeparated) caret.push($new);
                else this.parent.replace(this, new LeanArgsSemicolonSeparated([this, $new], this.indent, caret.level));
                return $new;
            }
        }
        return super.insert_semicolon(caret);
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

    is_indented() {
        const p = this.parent;
        if (!p) return true;
        if (p instanceof LeanStatements || p instanceof LeanIte) return true;
        if (p instanceof LeanArgsNewLineSeparated) return true;
        if (p instanceof LeanArgsSpaceSeparated && p.parent instanceof LeanTactic) return true;
        if (p instanceof LeanSequentialTacticCombinator && p.arg === this) return true;
        if (p instanceof LeanSequentialTacticCombinator) {
            return this.indent >= p.indent && !p.newline;
        }
        return false;
    }

    is_inline_tactic_block() {
        return this.tacticName === 'repeat' || this.tacticName === 'try';
    }

    toJSON() {
        const name = this.tacticName;
        const arg = this.arg.toJSON();
        const modifiers = this.modifiers.map((m) => m.toJSON());
        /** Fixed key order so parse → print → parse matches JSON.stringify output. */
        return {
            modifiers,
            only: this.only,
            [name]: arg,
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

    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
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
}

export class LeanBy extends LeanUnary {
    get operator() {
        return 'by';
    }

    get command() {
        return 'by';
    }

    echo() {
        this.arg?.echo?.();
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent <= indent && caret instanceof LeanCaret && caret === this.arg) {
            // When the next line is already deeper than `by`, use that indent; when it matches the assign
            // line (common after a column-0 `-- proof`), keep that indent so tactics stay inside the
            // proof block instead of bubbling to `LeanModule` (AST → string → AST).
            const ind = indent >= this.indent ? indent : this.indent + 2;
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
            const ind = indent >= this.indent ? indent : this.indent + 2;
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
                const $new = this.push_args_indented(indent, newlineCount, false);
                if ($new) return $new;
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

export class LeanAt extends LeanUnary {
    get operator() {
        return 'at';
    }

    get command() {
        return 'at';
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

    is_indented() {
        return false;
    }

    latexFormat() {
        return `{\\color{#00f}${this.command}}\\ %s`;
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}

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

    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }

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

    tactic_block(args, span) {
        let count = 0;
        let j = 0;
        while (count < span && j < args.length) {
            if (args[j] instanceof LeanTacticBlock) count++;
            j++;
        }
        return j;
    }

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

    set_line(line) {
        this.line = line;
        if (this.arg instanceof LeanStatements) line++;
        return this.arg.set_line(line);
    }
}

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
            const $new = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanBitOr(caret, $new, this.indent, caret.level));
            return $new;
        }
        throw new Error(`LeanWith.insert_bar: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    insert_comma(caret) {
        if (caret === this.args[this.args.length - 1]) {
            const $new = new LeanCaret(this.indent, caret.level);
            this.replace(caret, new LeanArgsCommaSeparated([caret, $new], this.indent, caret.level));
            return $new;
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

class LeanAttribute extends LeanUnary {
    get operator() {
        return '@';
    }

    get command() {
        return '@';
    }

    append($new, _type) {
        return this.push_accessibility($new, 'public');
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

    push_accessibility($new, accessibility) {
        switch ($new) {
            case 'Lean_theorem':
            case 'Lean_lemma':
            case 'Lean_def': {
                const Ctor = getLeanClass($new);
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

    strArgs() {
        const [attr, assignment] = this.args;
        if (attr == null) return [assignment];
        return this.args;
    }

    strFormat() {
        const acc = this.accessibility === 'public' ? '' : `${this.accessibility} `;
        let def = `${acc}${this.func} %s`;
        if (this.attribute) def = `%s\n${def}`;
        return def;
    }

    latexFormat() {
        return this.strFormat();
    }

    toJSON() {
        const json = {
            [this.operator]: super.toJSON(),
            accessibility: this.accessibility,
        };
        if (this.attribute) json.attribute = this.attribute.toJSON();
        return json;
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    is_indented() {
        return false;
    }

    set_line(line) {
        this.line = line;
        let L = line;
        const attr = this.attribute;
        if (attr) L = attr.set_line(L) + 1;
        return this.assignment.set_line(L);
    }

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

    toJSON() {
        return {
            [this.operator]: this.args[0].toJSON(),
        };
    }

    latexFormat() {
        return `{\\color{#00f}${this.command}}\\ ` + Array(this.args.length).fill('%s').join('\\ ');
    }

    get operator() {
        return 'let';
    }

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

    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }
}

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

    toJSON() {
        return {
            [this.operator]: super.toJSON(),
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
    toJSON() {
        return { [this.operator]: this.arg.toJSON() };
    }
    latexFormat() {
        return `${this.command}\\ %s`;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

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

    toJSON() {
        return {
            [this.func]: super.toJSON(),
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

class LeanStack extends LeanBigOperator {
    static input_priority = 52;

    get operator() {
        return 'Stack';
    }

    get command() {
        return 'Stack';
    }

    get stack_priority() {
        return 28;
    }

    latexArgs(syntax) {
        const s = syntax ?? {};
        s[this.constructor.name] = true;
        return super.latexArgs(s);
    }

    latexFormat() {
        return '\\left[{%s}\\right]{%s}';
    }

    push_args_indented(_indent, _newlineCount, _functionCall = true) {}

    strFormat() {
        return '[%s] %s';
    }
}

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
        for (; this.start_idx < length; this.start_idx++) {
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

function getLeanClass(name) {
    const C = LEAN_CLASSES[name];
    if (C) return C;
    throw new Error(`getLeanClass: unknown class ${name} (add to LEAN_CLASSES)`);
}

/**
 * Port of global `compile`.
 * @param {string} code
 */
export function compile(code) {
    return LeanParser.instance.build(code);
}

LeanParser.instance = new LeanParser();
