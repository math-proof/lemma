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

export class Lean extends IndentedNode {
    /**
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(indent, level, parent = null) {
        super(indent, parent);
        this.level = level;
    }

    /**
     * Port of default `Lean::toString` / `strFormat` behavior (php/parser/lean.php).
     * Anonymous command/paired classes rely on this so `Node::toString` never throws.
     */
    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n).fill('%s').join(' ');
    }

    is_comment() {
        return false;
    }

    /** PHP `Lean::tokens_space_separated` (php/parser/lean.php ~94–97). */
    tokens_space_separated() {
        return [];
    }

    /** Port of `Lean::is_outsider` (php/parser/lean.php ~99–101). */
    is_outsider() {
        return false;
    }

    /** PHP `Lean::is_space_separated` (php/parser/lean.php ~469–472). */
    is_space_separated() {
        return false;
    }

    /** PHP `Lean::getEcho` (php/parser/lean.php ~104): base returns void. */
    getEcho() {}

    /** PHP `Lean::strArgs` (php/parser/lean.php ~106–109). */
    strArgs() {
        return this.args ?? [];
    }

    /** PHP `Lean::echo` (php/parser/lean.php ~152–154): no-op. */
    echo() {}

    /** Port of `Lean::relocate_last_comment` (php/parser/lean.php ~438). */
    relocateLastComment() {}

    /** Port of `Lean::split` (php/parser/lean.php ~440–442). */
    split(_syntax) {
        return [this];
    }

    /** Default: same as `strFormat` (php/parser/lean.php ~125–127). */
    latexFormat() {
        return this.strFormat();
    }

    /**
     * Port of `Lean::latexArgs` (php/parser/lean.php ~129–136).
     * @param {Record<string, unknown>} [syntax]
     */
    latexArgs(syntax) {
        return this.args.map((a) => a.toLatex(syntax));
    }

    /**
     * Port of `Lean::toLatex` (php/parser/lean.php ~139–145).
     * @param {Record<string, unknown>} [syntax]
     */
    toLatex(syntax) {
        const fmt = this.latexFormat();
        const args = this.latexArgs(syntax);
        if (args.length) return String(fmt).format(...args);
        return fmt;
    }

    /** Port of `Lean::isProp` (php/parser/lean.php ~148–150). */
    isProp(_vars) {
        return false;
    }

    /** PHP `Lean::traverse` (php/parser/lean.php ~156–159): generator yielding this. */
    *traverse() {
        yield this;
    }

    /** PHP `Lean::set_line` (php/parser/lean.php ~161–165). */
    set_line(line) {
        this.line = line;
        return line;
    }

    get stack_priority() {
        const c = /** @type {{ input_priority?: number }} */ (this.constructor);
        return typeof c.input_priority === 'number' ? c.input_priority : 100;
    }

    get root() {
        return this.parent ? this.parent.root : null;
    }

    insert_space(caret) {
        return caret;
    }

    /** Port of `Lean::insert_newline` (php/parser/lean.php ~179–182): delegate with `$this`, not the first param. */
    insert_newline(_caret, newlineCount, indent, next) {
        if (this.parent) return this.parent.insert_newline(this, newlineCount, indent, next);
        throw new Error('insert_newline: no parent');
    }

    insert_end(caret) {
        if (this.parent) return this.parent.insert_end(this);
    }

    append(_new, _type) {
        if (this.parent) return this.parent.append(this, _new, _type);
    }

    push_accessibility(_new, _accessibility) {
        if (this.parent) return this.parent.push_accessibility(this, _new, _accessibility);
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

    push_arithmetic(token) {
        const cls = token2classname[token];
        if (!cls) throw new Error(`push_arithmetic: unknown token ${JSON.stringify(token)}`);
        return this.push_binary(cls);
    }

    push_or() {
        const parent = this.parent;
        if (!parent) return undefined;
        const Ctor = LEAN_CLASSES.Lean_lor;
        return Ctor.input_priority > parent.stack_priority
            ? this.push_multiple('Lean_lor', new LeanCaret(this.indent, this.level))
            : parent.push_or();
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

    push_token(word) {
        return this.append(new LeanToken(word, this.indent, this.level), 'token');
    }

    insert_word(caret, word) {
        return caret.push_token(word);
    }

    insert_comma(caret) {
        if (this.parent) return this.parent.insert_comma(this);
    }

    insert_semicolon(caret) {
        if (this.parent) return this.parent.insert_semicolon(this);
    }

    insert_colon(caret) {
        return caret.push_binary('LeanColon');
    }

    /** Port of `Lean::insert_assign` (php/parser/lean.php ~270–272) — must not delegate; same pattern as `insert_colon`. */
    insert_assign(caret) {
        return caret.push_binary('LeanAssign');
    }

    /** Port of `Lean::insert_vconstruct` (php/parser/lean.php ~274–276). */
    insert_vconstruct(caret) {
        return caret.push_binary('LeanVConstruct');
    }

    /** Port of `Lean::insert_construct` (php/parser/lean.php ~278–280). */
    insert_construct(caret) {
        return caret.push_binary('LeanConstruct');
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

    insert_left(caret, func, prevToken = '') {
        return caret.push_left(func, prevToken);
    }

    push_right(funcName) {
        if (this.parent) return this.parent.push_right(funcName);
    }

    push_attr(_caret) {
        throw new Error('push_attr is unexpected for ' + this.constructor.name);
    }

    push_minus() {
        throw new Error('push_minus is unexpected for ' + this.constructor.name);
    }

    push_quote(_quote) {
        throw new Error('push_quote is unexpected for ' + this.constructor.name);
    }

    insert_sequential_tactic_combinator(caret, nextToken) {
        if (this.parent) return this.parent.insert_sequential_tactic_combinator(this, nextToken);
    }

    insert_line_comment(caret, comment) {
        return caret.push_line_comment(comment);
    }

    insert(caret, func, type) {
        if (this.parent) return this.parent.insert(this, func, type);
    }

    insert_if(caret) {
        if (this.parent) return this.parent.insert_if(this);
    }

    insert_then(caret) {
        if (this.parent) return this.parent.insert_then(this);
    }

    insert_else(caret) {
        if (this.parent) return this.parent.insert_else(this);
    }

    insert_calc(caret) {
        if (this.parent) return this.parent.insert_calc(this);
    }

    insert_only(caret) {
        if (this.parent) return this.parent.insert_only(this);
    }

    insert_tactic(caret, token) {
        if (this.parent) return this.parent.insert_tactic(this, token);
    }

    case_default() {
        return this;
    }

    /**
     * Port of `Lean::parse` (php/parser/lean.php ~484–942).
     * @param {string} token
     * @param {LeanParser} parser
     */
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
                // fallthrough: bare '/' uses same rule as '%' (php/parser/lean.php)
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

    push_line_comment(comment) {
        if (this.parent) return this.parent.push_line_comment(comment);
        throw new Error(`push_line_comment: no parent for ${this.constructor.name}`);
    }

    push_block_comment(comment, docstring) {
        throw new Error(`push_block_comment is unexpected for ${this.constructor.name}`);
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

    /**
     * Port of `LeanArgs::push_args_indented` (php/parser/lean.php ~1483–1492).
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

    // insert_comma, insert_semicolon, insert_assign, push_right, push_or, push_post_unary, etc.
    // inherit from `Lean` (php/parser/lean.php) — delegate to parent; do not override with throws.
}

/** Port of `LeanArgsCommaSeparated` (php/parser/lean.php ~6755–6765). */
export class LeanArgsCommaSeparated extends LeanArgs {
    /** PHP `LeanArgsCommaSeparated::strFormat` (php/parser/lean.php ~6738–6740). */
    strFormat() {
        return Array(this.args.length).fill('%s').join(', ');
    }

    /**
     * When this is the GetElem index (e.g. A[i, i+1-l:n⊓i+u]), use stack_priority 18 so the
     * slice `:` creates LeanColon inside the index instead of bubbling to the lemma colon.
     * Port of LeanGetElemBaseBinary::stack_priority (php/parser/lean.php ~4045–4046).
     */
    get stack_priority() {
        const p = this.parent?.constructor?.name;
        if (p === 'LeanGetElem' || p === 'LeanGetElemQue' || p === 'LeanGetElemQuote') return 18;
        return 100;
    }

    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        this.push(caret2);
        return caret2;
    }
}

/** Port of `LeanArgsNewLineSeparated` (php/parser/lean.php ~6520–6624). */
export class LeanArgsNewLineSeparated extends LeanArgs {
    push_newlines(newlineCount) {
        for (let i = 0; i < newlineCount; ++i) {
            this.push(new LeanCaret(this.indent, this.level));
        }
        return this.args[this.args.length - 1];
    }
}

/**
 * Port of `LeanArgsCommaNewLineSeparated` (php/parser/lean.php ~6856–6919).
 * Used by `LeanPairedGroup::insert_newline` when wrapping a caret (not `LeanArgsNewLineSeparated`).
 */
export class LeanArgsCommaNewLineSeparated extends LeanArgs {
    strFormat() {
        return Array(this.args.length).fill('%s').join(',\n');
    }

    insert_newline(caret, newlineCount, indent, next) {
        if (this.indent > indent) {
            return super.insert_newline(caret, newlineCount, indent, next);
        }
        // PHP `LeanArgsCommaNewLineSeparated::insert_newline` throws here; mirror
        // `LeanArgsNewLineSeparated` (~6544–6549) so indented multiline `⟨…⟩` / `[…]` lemmas parse.
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

    insert_comma(caret) {
        const c2 = new LeanCaret(this.indent, caret.level);
        this.push(c2);
        return c2;
    }
}

/** Port of `LeanArgsSemicolonSeparated` (php/parser/lean.php ~6798–6854). */
export class LeanArgsSemicolonSeparated extends LeanArgs {
    is_indented() {
        return false;
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join('; ');
    }

    latexFormat() {
        return Array(this.args.length).fill('{%s}').join('; ');
    }

    get stack_priority() {
        return LeanColon.input_priority - 1;
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
    get rhs() {
        return this.args[1];
    }

    /** PHP LeanBinary::__get('operator') — used by strFormat (php/parser/lean.php ~2433–2437). */
    get operator() {
        const name = this.constructor.name;
        switch (name) {
            case 'LeanAssign':
                return ':=';
            case 'LeanEq':
                return '=';
            case 'LeanRightarrow':
                return '=>';
            case 'Lean_is':
                return 'is';
            case 'Lean_is_not':
                return 'is not';
            default: {
                const pair = Object.entries(token2classname).find(([, cls]) => cls === name);
                return pair ? pair[0] : null;
            }
        }
    }

    /** PHP `LeanBinary::sep` (php/parser/lean.php ~2525–2527). */
    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    /** PHP `LeanBinary::strFormat` (php/parser/lean.php ~2433–2437): "%s $this->operator$sep%s". */
    strFormat() {
        const op = this.operator;
        if (op == null) return super.strFormat();
        const sep = this.sep();
        return `%s ${op}${sep}%s`;
    }

    /** PHP arithmetic/relational override: use literal LaTeX (+, -, \\cdot) not \\Add, \\Sub. */
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

    /** PHP `LeanBinary::latexFormat` (php/parser/lean.php ~2102–2104). */
    latexFormat() {
        return `{%s} ${this.command} {%s}`;
    }
}

/** PHP LeanProperty (php/parser/lean.php ~2126–2134); binary for property access e.g. Foo.bar. */
export class LeanProperty extends LeanBinary {
    static input_priority = 81;

    /** PHP `LeanProperty::is_space_separated` (php/parser/lean.php ~2152–2165): trig/log rhs. */
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

/** Port of `LeanColon` (php/parser/lean.php ~2355–2411). */
export class LeanColon extends LeanBinary {
    static input_priority = 19;

    /** PHP `LeanColon::strFormat` (php/parser/lean.php ~2368–2375): "%s : %s" so (l : ℕ) renders correctly. */
    strFormat() {
        const sep = this.rhs instanceof LeanStatements ? '\n' : (this.rhs instanceof LeanCaret || (this.parent && this.parent.constructor?.name === 'LeanGetElem') ? '' : ' ');
        const first = this.parent && this.parent.constructor?.name === 'LeanGetElem' ? '%s' : '%s ';
        return `${first}:${sep}%s`;
    }

    /** PHP `LeanColon::insert_newline` (php/parser/lean.php ~2399–2410). */
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

/** Port of `LeanAssign` (php/parser/lean.php ~2414+). */
export class LeanAssign extends LeanBinary {
    static input_priority = 18;
    relocateLastComment() {
        this.rhs.relocateLastComment();
    }
}

/** PHP LeanRelational group (php/parser/lean.php ~2596–2795): _gt, _ge, _lt, _le, Eq, BEq, _bne, _ne, _equiv, NotEquiv, _simeq, _approx, _asymp, Dvd. */
export class Lean_gt extends LeanBinary {
    static input_priority = 50;
}
export class Lean_ge extends LeanBinary {
    static input_priority = 50;
}
export class Lean_lt extends LeanBinary {
    static input_priority = 50;
}
export class Lean_le extends LeanBinary {
    static input_priority = 50;
}
export class LeanEq extends LeanBinary {
    static input_priority = 50;
}
export class LeanBEq extends LeanBinary {
    static input_priority = 50;
}
export class Lean_bne extends LeanBinary {
    static input_priority = 50;
}
export class Lean_ne extends LeanBinary {
    static input_priority = 50;
}
export class Lean_equiv extends LeanBinary {
    static input_priority = 40;
}
export class LeanNotEquiv extends LeanBinary {
    static input_priority = 40;
}
export class Lean_simeq extends LeanBinary {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≃'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_approx extends LeanBinary {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≈'] = true;
        return super.latexArgs(syntax);
    }
}
export class Lean_asymp extends LeanBinary {
    static input_priority = 50;
    latexArgs(syntax) {
        if (syntax) syntax['≍'] = true;
        return super.latexArgs(syntax);
    }
}
export class LeanDvd extends LeanBinary {
    static input_priority = 50;
}

/** PHP LeanBinaryBoolean (php/parser/lean.php ~2811–2863): _in, _notin, _leftrightarrow. */
export class Lean_in extends LeanBinary {
    static input_priority = 50;
    latexArgs(syntax) {
        let lhs = this.lhs;
        if (lhs instanceof LeanParenthesis && !(lhs.arg instanceof LeanColon)) lhs = lhs.arg;
        return [lhs.toLatex(syntax), this.rhs.toLatex(syntax)];
    }
}
export class Lean_notin extends LeanBinary {
    static input_priority = 50;
}
export class Lean_leftrightarrow extends LeanBinary {
    static input_priority = 50;
}

/** PHP LeanArithmetic group (php/parser/lean.php ~2901–3513): Add, Sub, Mul, _times, MatMul, _bullet, _odot, _otimes, _oplus, Div, FDiv, BitAnd, BitwiseAnd, BitwiseXor, BitOr, BitwiseOr, Pow, _ll, _lll, _gg, _ggg, Modular, Construct, VConstruct, Append, _sqcup, _sqcap, _cdotp, _circ, _blacktriangleright. */
/** PHP `LeanAdd` / `LeanSub` / `LeanMul` (php/parser/lean.php ~2901–2936): `input_priority` matches PHP statics. */
export class LeanAdd extends LeanBinary {
    static input_priority = 65;
}
export class LeanSub extends LeanBinary {
    static input_priority = 65;
}
export class LeanMul extends LeanBinary {
    static input_priority = 70;

    /** PHP `LeanMul::__get('command')` (php/parser/lean.php ~2937–2960): \\cdot vs implicit \\ . */
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

/** PHP `LeanMatMul` (php/parser/lean.php ~3013–3028): `@`; `operator` `@`, `command` `{\color{red}\times}` (see `LeanBinary::command`). */
export class LeanMatMul extends LeanBinary {
    static input_priority = 70;
}

/** PHP `Lean_sqcap` (php/parser/lean.php ~3469–3481): lattice meet `⊓`; extends `LeanArithmetic` (`input_priority` 69). */
export class Lean_sqcap extends LeanBinary {
    static input_priority = 69;
}

/** PHP `Lean_sqcup` (php/parser/lean.php ~3455–3467): lattice join `⊔`. */
export class Lean_sqcup extends LeanBinary {
    static input_priority = 68;
}

/** PHP `LeanDiv` (php/parser/lean.php ~3091–3128). */
export class LeanDiv extends LeanBinary {
    static input_priority = 70;
}

/** PHP `Lean_times` (php/parser/lean.php ~2998–3011): `×`. */
export class Lean_times extends LeanBinary {
    static input_priority = 72;
}

/** PHP `LeanPow` (php/parser/lean.php ~3308–3336): `^`. */
export class LeanPow extends LeanBinary {
    static input_priority = 80;
}

/** PHP `LeanConstruct` (php/parser/lean.php ~3408–3420): `::`. */
export class LeanConstruct extends LeanBinary {
    static input_priority = 67;
}

/** PHP `LeanVConstruct` (php/parser/lean.php ~3423–3436): `::ᵥ`. */
export class LeanVConstruct extends LeanBinary {
    static input_priority = 67;
}

/** PHP `LeanAppend` (php/parser/lean.php ~3439–3452): `++`. */
export class LeanAppend extends LeanBinary {
    static input_priority = 65;
}

/** PHP `Lean_bullet` (php/parser/lean.php ~3030–3043): `•`. */
export class Lean_bullet extends LeanBinary {
    static input_priority = 73;
}

/** PHP `Lean_odot` (php/parser/lean.php ~3045–3058): `⊙`. */
export class Lean_odot extends LeanBinary {
    static input_priority = 73;
}

/** PHP `Lean_otimes` (php/parser/lean.php ~3060–3074): `⊗`. */
export class Lean_otimes extends LeanBinary {
    static input_priority = 32;
}

/** PHP `Lean_oplus` (php/parser/lean.php ~3076–3089): `⊕`. */
export class Lean_oplus extends LeanBinary {
    static input_priority = 30;
}

/** PHP token2classname `⊖` => Lean_ominus. No explicit PHP class; extends LeanArithmetic. */
export class Lean_ominus extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊘` => Lean_oslash. No explicit PHP class. */
export class Lean_oslash extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊚` => Lean_circledcirc. No explicit PHP class. */
export class Lean_circledcirc extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊛` => Lean_circledast. No explicit PHP class. */
export class Lean_circledast extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊜` => Lean_circleeq. No explicit PHP class. */
export class Lean_circleeq extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊝` => Lean_circleddash. No explicit PHP class. */
export class Lean_circleddash extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊞` => Lean_boxplus. No explicit PHP class. */
export class Lean_boxplus extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊟` => Lean_boxminus. No explicit PHP class. */
export class Lean_boxminus extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊠` => Lean_boxtimes. No explicit PHP class. */
export class Lean_boxtimes extends LeanBinary {
    static input_priority = 67;
}

/** PHP token2classname `⊡` => Lean_dotsquare. No explicit PHP class. */
export class Lean_dotsquare extends LeanBinary {
    static input_priority = 67;
}

/** PHP `LeanEDiv` (php/parser/lean.php token2classname): euclidean division `÷`. No explicit PHP class; uses LeanArithmetic default. */
export class LeanEDiv extends LeanBinary {
    static input_priority = 70;
}

/** PHP `LeanFDiv` (php/parser/lean.php ~3131–3145): `//`. */
export class LeanFDiv extends LeanBinary {
    static input_priority = 70;
}

/** PHP `LeanModular` (php/parser/lean.php ~3392–3405): `%`. */
export class LeanModular extends LeanBinary {
    static input_priority = 70;
}

/** PHP `Lean_ll` (php/parser/lean.php ~3339–3350): `<<`. */
export class Lean_ll extends LeanBinary {
    static input_priority = 47;
}

/** PHP `Lean_lll` (php/parser/lean.php ~3352–3363): `<<<`. */
export class Lean_lll extends LeanBinary {
    static input_priority = 47;
}

/** PHP `Lean_gg` (php/parser/lean.php ~3365–3376): `>>`. */
export class Lean_gg extends LeanBinary {
    static input_priority = 47;
}

/** PHP `Lean_ggg` (php/parser/lean.php ~3378–3390): `>>>`. */
export class Lean_ggg extends LeanBinary {
    static input_priority = 75;
}

/** PHP `Lean_cdotp` (php/parser/lean.php ~3483–3496): `⬝`. */
export class Lean_cdotp extends LeanBinary {
    static input_priority = 71;
}

/** PHP `Lean_circ` (php/parser/lean.php ~3499–3510): `∘`. */
export class Lean_circ extends LeanBinary {
    static input_priority = 90;
}

/** PHP `Lean_blacktriangleright` (php/parser/lean.php ~3513–3528): `▸`. */
export class Lean_blacktriangleright extends LeanBinary {
    static input_priority = 47;
}

/** PHP `LeanBitAnd` (php/parser/lean.php ~3148–3163). */
export class LeanBitAnd extends LeanBinary {
    static input_priority = 68;
}

/** PHP `LeanBitwiseAnd` (php/parser/lean.php ~3165–3179). */
export class LeanBitwiseAnd extends LeanBinary {
    static input_priority = 60;
}

/** PHP `LeanBitwiseXor` (php/parser/lean.php ~3182–3196). */
export class LeanBitwiseXor extends LeanBinary {
    static input_priority = 60;
}

/** PHP `LeanBitOr` (php/parser/lean.php ~3199+). */
export class LeanBitOr extends LeanBinary {
    static input_priority = 47;
}

/** PHP `LeanBitwiseOr` (php/parser/lean.php ~3291+). */
export class LeanBitwiseOr extends LeanBinary {
    static input_priority = 55;
}

/** PHP `Lean_land` (php/parser/lean.php ~4380–4402): `∧`. */
export class Lean_land extends LeanBinary {
    static input_priority = 35;
}

/** PHP `LeanLogicAnd` (php/parser/lean.php ~4248–4281): `&&`. */
export class LeanLogicAnd extends LeanBinary {
    static input_priority = 37;
}

/** PHP `LeanLogicOr` (php/parser/lean.php ~4284–4315): `||`. */
export class LeanLogicOr extends LeanBinary {
    static input_priority = 37;
}

/** PHP `LeanLogicXor` (php/parser/lean.php ~4319–4338): `^^`. */
export class LeanLogicXor extends LeanBinary {
    static input_priority = 33;
}

/** PHP `Lean_cup` (php/parser/lean.php ~4197–4210): `∪`. */
export class Lean_cup extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_cap` (php/parser/lean.php ~4212–4245): `∩`. */
export class Lean_cap extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_setminus` (php/parser/lean.php ~4183–4194): `\`. */
export class Lean_setminus extends LeanBinary {
    static input_priority = 70;
}

/** PHP `Lean_subseteq` (php/parser/lean.php ~4404–4417): `⊆`. */
export class Lean_subseteq extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_subset` (php/parser/lean.php ~4419–4432): `⊂`. */
export class Lean_subset extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_supseteq` (php/parser/lean.php ~4434–4446): `⊇`. */
export class Lean_supseteq extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_supset` (php/parser/lean.php ~4448–4460): `⊃`. */
export class Lean_supset extends LeanBinary {
    static input_priority = 50;
}

/** PHP `Lean_is` (php/parser/lean.php ~4096–4133): `is`. */
export class Lean_is extends LeanBinary {
    static input_priority = 62;
}

/** PHP `Lean_is_not` (php/parser/lean.php ~4136–4168). */
export class Lean_is_not extends LeanBinary {
    static input_priority = 62;
}

/** PHP `LeanMethodChaining` (php/parser/lean.php ~3989–4015): `|>.`. */
export class LeanMethodChaining extends LeanBinary {
    static input_priority = 67;
}

/** PHP `Lean_lor` (e.g. `∨`): lower priority than typical relation binaries. */
export class Lean_lor extends LeanBinary {
    static input_priority = 30;
}

/** PHP `Lean_rightarrow` (php/parser/lean.php ~5591–5645): `→` (right associative, priority 25). */
export class Lean_rightarrow extends LeanBinary {
    static input_priority = 25;

    get stack_priority() {
        return 24;
    }

    get operator() {
        return '→';
    }

    /** PHP `Lean_rightarrow::is_indented` (php/parser/lean.php ~5599–5602). */
    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    /** PHP `Lean_rightarrow::sep` (php/parser/lean.php ~5594–5597). */
    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    /** PHP `Lean_rightarrow::strFormat` (php/parser/lean.php ~5604–5608). */
    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }

    /** PHP `Lean_rightarrow::insert_newline` (php/parser/lean.php ~5610–5625). */
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

    /**
     * PHP `Lean_rightarrow::isProp` (php/parser/lean.php ~5639–5644).
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
}

/** PHP `Lean_mapsto` (php/parser/lean.php ~5647–5692): `↦`; stack_priority 23, sep for Statements. */
export class Lean_mapsto extends LeanBinary {
    static input_priority = 47;

    get stack_priority() {
        return 23;
    }

    /** PHP `Lean_mapsto::sep` (php/parser/lean.php ~5650–5653). */
    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : ' ';
    }

    /** PHP `Lean_mapsto::strFormat` (php/parser/lean.php ~5658–5662). */
    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }

    /** PHP `Lean_mapsto::insert_newline` (php/parser/lean.php ~5664–5679). */
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
}

/**
 * Port of `LeanRightarrow` (php/parser/lean.php ~5448–5504): `=>` (tactic arrow / mapsto-style layout).
 * `input_priority` matches `LeanColon` (19).
 */
export class LeanRightarrow extends LeanBinary {
    static input_priority = 19;

    /** PHP `LeanRightarrow::sep` (php/parser/lean.php ~5451–5454). */
    sep() {
        return this.rhs instanceof LeanStatements ? '\n' : this.rhs instanceof LeanCaret ? '' : ' ';
    }

    /** PHP `LeanRightarrow::strFormat` (php/parser/lean.php ~5461–5467). */
    strFormat() {
        const sep = this.sep();
        let lhs = '%s';
        if (!(this.lhs instanceof LeanCaret)) lhs += ' ';
        return `${lhs}${this.operator}${sep}%s`;
    }

    /**
     * Port of `LeanRightarrow::insert_newline` (php/parser/lean.php ~5470–5488).
     */
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

    /** PHP `LeanRightarrow::relocate_last_comment` (php/parser/lean.php ~5501–5504). */
    relocateLastComment() {
        this.rhs.relocateLastComment();
    }
}

/**
 * Port of `LeanArgsIndented` (php/parser/lean.php ~6638+).
 * Wraps `lhs` with newline-separated `rhs` at a deeper indent.
 * PHP latexFormat returns "%s\n%s" (no command) — KaTeX has no \ArgsIndented.
 */
export class LeanArgsIndented extends LeanBinary {
    /**
     * @param {Lean} lhs
     * @param {Lean} rhs
     * @param {number} indent
     * @param {number} level
     */
    constructor(lhs, rhs, indent, level) {
        super(lhs, rhs, indent, level);
    }

    /** PHP LeanArgsIndented::sep (php/parser/lean.php ~6640). */
    sep() {
        return '\n';
    }

    /** PHP LeanArgsIndented::latexFormat (php/parser/lean.php ~6655–6658): %s + sep + %s, no command. */
    latexFormat() {
        return '{%s}' + this.sep() + '{%s}';
    }
}

export class LeanUnary extends LeanArgs {
    static input_priority = 47;
    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     */
    constructor(arg, indent, level) {
        super([], indent, level);
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
}

/** Port of `LeanBy` (php/parser/lean.php ~7469–7538). */
export class LeanBy extends LeanUnary {
    static input_priority = 47;

    sep() {
        return this.arg instanceof LeanStatements ? '\n' : ' ';
    }

    strFormat() {
        const s = this.sep();
        return `by${s}%s`;
    }

    /**
     * Port of `LeanBy::insert_newline` (php/parser/lean.php ~7495–7509).
     */
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

    /** PHP `LeanBy::insert_semicolon` (php/parser/lean.php ~7541–7549). */
    insert_semicolon(caret) {
        if (caret === this.arg) {
            const c = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanArgsSemicolonSeparated([this.arg, c], this.indent, c.level);
            return c;
        }
        if (this.parent) return this.parent.insert_semicolon(this);
    }
}

/** Port of PHP LeanAttribute (php/parser/lean.php ~8553–8614). Needed so @[main] becomes lemma.attribute. */
class LeanAttribute extends LeanUnary {
    /** Port of LeanAttribute::insert_newline (php/parser/lean.php ~8575–8579). Return caret to keep it inside so push_accessibility runs on next line. */
    insert_newline(caret, newlineCount, indent, next) {
        if (this.parent && this.parent.constructor?.name === 'LeanTactic')
            return super.insert_newline(caret, newlineCount, indent, next);
        return caret;
    }

    push_accessibility(_child, New, accessibility) {
        if (New !== 'Lean_theorem' && New !== 'Lean_lemma' && New !== 'Lean_def')
            return super.push_accessibility(_child, New, accessibility);
        const Ctor = getLeanClass(New);
        const caret = new LeanCaret(this.indent, this.level);
        const replacement = new Ctor(accessibility, caret, this.indent, this.level);
        this.parent.replace(this, replacement);
        replacement.args[0] = this;
        this.parent = replacement;
        return caret;
    }
}

/** Port of PHP Lean_leftarrow (php/parser/lean.php ~5694–5715): unary with operator ←. */
class Lean_leftarrow extends LeanUnary {
    get operator() {
        return '←';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP LeanNeg (php/parser/lean.php ~3560–3578): unary minus "-%s". */
class LeanNeg extends LeanUnary {
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

/** PHP LeanPlus (php/parser/lean.php ~3607–3627): unary plus "+%s". */
class LeanPlus extends LeanUnary {
    get operator() {
        return '+';
    }
    strFormat() {
        return `${this.operator}%s`;
    }
}

/** PHP Lean_sqrt (php/parser/lean.php ~3705–3736): √%s. */
class Lean_sqrt extends LeanUnary {
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

/** PHP LeanCubicRoot (php/parser/lean.php ~3776–3799): ∛%s. */
class LeanCubicRoot extends LeanUnary {
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

/** PHP Lean_uparrow (php/parser/lean.php ~3802–3833): ↑%s. */
class Lean_uparrow extends LeanUnary {
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

/** PHP LeanUparrow (php/parser/lean.php ~3836–3858): ⇑%s. */
class LeanUparrow extends LeanUnary {
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

/** PHP LeanQuarticRoot (php/parser/lean.php ~3887–3911): ∜%s. */
class LeanQuarticRoot extends LeanUnary {
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

/** PHP Lean_lnot (php/parser/lean.php ~5717+): ¬%s. */
class Lean_lnot extends LeanUnary {
    static input_priority = 40;
    get operator() {
        return '¬';
    }
    strFormat() {
        return `${this.operator}%s`;
    }
}

/** PHP `LeanNot` (php/parser/lean.php ~5748–5779): prefix `!` (distinct from `Lean_lnot` ¬). */
class LeanNot extends LeanUnary {
    static input_priority = 40;

    is_indented() {
        return this.parent instanceof LeanStatements;
    }

    strFormat() {
        return `${this.operator}%s`;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    isProp(_vars) {
        return true;
    }

    get operator() {
        return '!';
    }

    get command() {
        return '\\text{!}';
    }
}

/** Placeholder for `instanceof` checks in `Lean::push_left` (php/parser/lean.php). */
export class LeanUnaryArithmeticPost extends Lean {
    static input_priority = 72;
}

/** PHP LeanInv (php/parser/lean.php ~3630–3652): %s⁻¹ postfix. */
class LeanInv extends LeanUnary {
    static input_priority = 71;
    get operator() {
        return '⁻¹';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanPosPart (php/parser/lean.php ~3655–3677): %s⁺. */
class LeanPosPart extends LeanUnary {
    static input_priority = 71;
    get operator() {
        return '⁺';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanNegPart (php/parser/lean.php ~3680–3702): %s⁻. */
class LeanNegPart extends LeanUnary {
    static input_priority = 71;
    get operator() {
        return '⁻';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanSquare (php/parser/lean.php ~3739–3773): %s². */
class LeanSquare extends LeanUnary {
    static input_priority = 66;
    get operator() {
        return '²';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanCube (php/parser/lean.php ~3868–3890): %s³. */
class LeanCube extends LeanUnary {
    get operator() {
        return '³';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanTesseract (php/parser/lean.php ~3920–3943): %s⁴. */
class LeanTesseract extends LeanUnary {
    get operator() {
        return '⁴';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanTranspose (php/parser/lean.php ~3945–3968): %sᵀ. */
class LeanTranspose extends LeanUnary {
    get operator() {
        return 'ᵀ';
    }
    strFormat() {
        return `%s${this.operator}`;
    }
}

/** PHP LeanPipeForward (php/parser/lean.php ~3970–3986): %s|>. */
class LeanPipeForward extends LeanUnary {
    get operator() {
        return '|>';
    }
    strFormat() {
        return `%s ${this.operator}`;
    }
}

/** PHP LeanBar (php/parser/lean.php ~5379–5446): pattern separator | in match/with/induction. */
class LeanBar extends LeanUnary {
    is_indented() {
        return true;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
    latexFormat() {
        return `${this.command} %s`;
    }
    get operator() {
        return '|';
    }
    get command() {
        return '|';
    }
    get stack_priority() {
        return LeanAssign?.input_priority ?? 20;
    }
    echo() {
        this.arg?.echo?.();
    }
    split(_syntax) {
        const arrow = this.arg;
        if (arrow instanceof LeanRightarrow) {
            const stmts = arrow.rhs;
            if (stmts instanceof LeanStatements) {
                const self = Object.assign(Object.create(Object.getPrototypeOf(this)), this);
                const statements = [self];
                arrow.rhs = new LeanCaret(arrow.indent, stmts.level);
                stmts.swap_echo_star?.(_syntax, statements);
                return statements;
            }
        }
        return [this];
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
}

class LeanPairedGroup extends LeanUnary {
    static input_priority = 60;
    is_Expr() {
        return true;
    }

    /** Port of `LeanPairedGroup::__get('operator')` / paired delimiters (php/parser/lean.php). */
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

    /** Port of `LeanPairedGroup::strFormat` (php/parser/lean.php ~1647–1657). */
    strFormat() {
        let format = this.argFormat();
        const operator = this.operator;
        if (this.is_closed) {
            format = operator[0] + format + operator[1];
        } else if (this.is_closed === null) {
            format = operator[0] + format;
        } else {
            format += operator[1];
        }
        return format;
    }

    /**
     * Port of `LeanPairedGroup::insert` (php/parser/lean.php ~1629–1643).
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

    /**
     * When `'` continues a name after `[…]` etc., caret may be a paired group; delegate like `LeanCaret::push_quote` extension.
     */
    push_quote(token) {
        if (this.parent) return this.parent.insert_word(this, token);
        throw new Error('push_quote: no parent');
    }

    /**
     * Port of `LeanPairedGroup::insert_newline` (php/parser/lean.php ~1573–1588) and `LeanBrace` (~1920–1928).
     */
    insert_newline(caret, newlineCount, indent, next) {
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
            throw new Error(`LeanPairedGroup.insert_newline: unexpected for ${this.constructor.name}`);
        }
        return super.insert_newline(caret, newlineCount, indent, next);
    }

    /**
     * Port of `LeanPairedGroup::push_token` (php/parser/lean.php ~1839–1845).
     * When token follows closed paren/bracket (e.g. `Mul_Stack_Bool (fun...) A`), add as sibling.
     */
    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    /**
     * Port of `LeanPairedGroup::push_right` (php/parser/lean.php ~1620–1627).
     * @param {string} funcName e.g. 'LeanParenthesis'
     */
    push_right(funcName) {
        if (this.constructor.name === funcName) {
            this.is_closed = true;
            return this;
        }
        if (this.parent) return this.parent.push_right(funcName);
    }

    /**
     * Port of `LeanPairedGroup::insert_comma` (php/parser/lean.php ~1591–1598).
     * PHP checks `$this->arg instanceof LeanArgsCommaSeparated` (not `$caret`).
     */
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

    get is_closed() {
        return this.kwargs.is_closed;
    }

    set is_closed(v) {
        this.kwargs.is_closed = v;
    }
}

/**
 * Port of `LeanParenthesis` (php/parser/lean.php ~1665–1772).
 * Parentheses bump inner `level` and handle newlines/`by` differently from generic `LeanPairedGroup`.
 * Rainbow printing: nesting level (arg.level) selects one of 8 colors via toColor().
 */
export class LeanParenthesis extends LeanPairedGroup {
    /** PHP `LeanParenthesis::__get('stack_priority')` returns 10 (php/parser/lean.php ~1727–1728). Ensures `:` creates LeanColon inside parens, e.g. (1 : Tensor ℝ* [n,n]). */
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
     * PHP `LeanParenthesis::toColor` (php/parser/lean.php ~1686–1696).
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
     * PHP `LeanParenthesis::latexFormat` (php/parser/lean.php ~1699–1709).
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
     * PHP `LeanParenthesis::latexArgs` (php/parser/lean.php ~1711–1722).
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
     * Port of `LeanParenthesis::insert_newline` (php/parser/lean.php ~1754–1772).
     */
    insert_newline(caret, newlineCount, indent, next) {
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

export class LeanArgsSpaceSeparated extends LeanArgs {
    static input_priority = 80;

    constructor(args, indent, level, parent = null) {
        super(args, indent, level, parent);
        /** @type {Record<string, unknown> | null} PHP `LeanArgsSpaceSeparated::$cache` */
        this.cache = null;
    }

    /** PHP `LeanArgsSpaceSeparated::is_space_separated` (php/parser/lean.php ~6192–6195). */
    is_space_separated() {
        return true;
    }

    /** Omit LeanCaret; use no sep for subscript (e.g. h_Ξ_def = h_ + Ξ_def). */
    toString() {
        const active = this.args.filter((a) => !(a instanceof LeanCaret));
        if (active.length === 0) return '';
        if (active.length === 1) return String(active[0]);
        const parts = [];
        for (let i = 0; i < active.length; i++) {
            const a = active[i];
            const prev = active[i - 1];
            const prevText = prev instanceof LeanToken ? prev.text : '';
            const sep =
                prev && prevText.endsWith('_') && a instanceof LeanToken ? '' : ' ';
            if (i > 0) parts.push(sep);
            parts.push(String(a));
        }
        return parts.join('');
    }

    /**
     * When inside LeanBracket (e.g. [i < n]), use LeanBracket's stack_priority (17) so that
     * Lean_lt is created by replacing the token (LeanToken "i"), not the whole group.
     * That yields LeanBracket.arg = LeanArgsSpaceSeparated([LeanCaret, Lean_lt(i,n)]) and
     * LeanStack can fire on `]` (php/parser/lean.php ~1878–1889).
     * When inside LeanArgsCommaSeparated that is a GetElem index (e.g. A[i, i+1-l:n⊓i+u]),
     * or directly under LeanGetElem (e.g. V[i+1-l:n⊓i+u] single-index slice), use 18 so
     * +, :, ⊓ etc. parse inside the index (php/parser/lean.php ~4045–4046).
     */
    get stack_priority() {
        if (this.parent?.constructor?.name === 'LeanBracket') return 17;
        const pc = this.parent?.constructor?.name;
        if (pc === 'LeanArgsCommaSeparated' && this.parent?.parent?.constructor?.name === 'LeanGetElem')
            return 18;
        if (pc === 'LeanGetElem' || pc === 'LeanGetElemQue' || pc === 'LeanGetElemQuote') return 18;
        return 80;
    }

    latexFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        return Array(n)
            .fill('{%s}')
            .join('\\ ');
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
                // Keep subscript-like identifiers contiguous: h_ Ξ -> h\_Ξ
                const sep =
                    prev && prevText.endsWith('_') && cur instanceof LeanToken ? '' : '\\ ';
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

    /**
     * PHP LeanStatements::latexFormat (php/parser/lean.php ~4515–4524).
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
     * Port of `LeanStatements::relocate_last_comment` (php/parser/lean.php ~4536–4599).
     */
    relocateLastComment() {
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
                    parent.relocateLastComment();
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
                            if (proof instanceof LeanBy || proof.constructor.name === 'LeanCalc') {
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
                end.relocateLastComment();
                break;
            }
        }
    }

    /** Port of LeanStatements::push_line_comment (php/parser/lean.php ~6973–6977). Stops bubbling to root. */
    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
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

export class LeanModule extends LeanStatements {
    get root() {
        return this;
    }

    get stack_priority() {
        return -3;
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
     * Port of `LeanModule::insert` (php/parser/lean.php ~4728–4737).
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
 * Port of `Lean_def` (php/parser/lean.php ~8616–8728). Used by `LeanCaret::append` (3-arg) and
 * `LeanCaret::push_accessibility` (4-arg).
 */
export class Lean_def extends LeanArgs {
    get stack_priority() {
        return 7;
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

    get assignment() {
        return this.args[1];
    }

    /** PHP `Lean_def::relocate_last_comment` (php/parser/lean.php ~8732–8736). */
    relocateLastComment() {
        const assignment = this.assignment;
        if (assignment instanceof LeanAssign) assignment.relocateLastComment();
    }

    /**
     * Port of `Lean_def::insert_newline` (php/parser/lean.php ~8667–8692).
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

export class Lean_lemma extends Lean_def {}

export class LeanCaret extends Lean {
    static input_priority = 100;

    strFormat() {
        return '';
    }

    append(New, _func) {
        if (typeof New === 'string') {
            const Ctor = getLeanClass(New);
            this.parent.replace(this, new Ctor(this, this.indent, this.level));
            return this;
        }
        this.parent.replace(this, New);
        return New;
    }

    push_accessibility(New, accessibility) {
        this.parent.replace(this, new (getLeanClass(New))(accessibility, this, this.indent, this.level));
        return this;
    }

    push_line_comment(comment) {
        const parent = this.parent;
        const line = new LeanLineComment(comment, this.indent, this.level);
        parent.replace(this, line);
        return line;
    }

    push_block_comment(comment, docstring) {
        const parent = this.parent;
        const Cls = docstring ? LeanDocString : LeanBlockComment;
        parent.replace(this, new Cls(comment, this.indent, this.level));
        parent.push(this);
        return this;
    }

    /** PHP does not define this on LeanCaret; delegate so `case "'"` can finish (see LeanToken::push_quote). */
    push_quote(token) {
        if (this.parent) return this.parent.insert_word(this, token);
        throw new Error('push_quote: no parent');
    }

    /** Port of LeanCaret::push_left (php/parser/lean.php ~1007–1010) — simpler than Lean::push_left. */
    push_left(func, _prevToken) {
        const Ctor = getLeanClass(func);
        this.parent.replace(this, new Ctor(this, this.indent, this.level));
        return this;
    }

    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    jsonSerialize() {
        return '';
    }

    is_outsider() {
        return true;
    }
}

class LeanCommand extends LeanUnary {
    static input_priority = 27;
}

/** PHP `Lean_let::strFormat` (php/parser/lean.php ~8802–8814): "let" + sep + "%s" per arg. */
class Lean_let extends LeanCommand {
    static input_priority = 7;

    get operator() {
        return 'let';
    }

    strFormat() {
        const func = this.operator;
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof LeanCaret) continue;
            parts.push(arg?.constructor?.name === 'LeanSequentialTacticCombinator' &&
                /** @type {*} */ (arg).newline ? '\n' : ' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }

    latexFormat() {
        return `{\\color{#00f}let}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
    }

    latexArgs(syntax) {
        return this.args.map((a) => a.toLatex(syntax));
    }
}

/** PHP `Lean_have::strFormat` (php/parser/lean.php ~8922–8926): "have" + sep + "%s". */
class Lean_have extends Lean_let {
    get operator() {
        return 'have';
    }

    latexFormat() {
        return `{\\color{#00f}have}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
    }
}

/** PHP `Lean_show` (php/parser/lean.php ~8973–9017). */
class Lean_show extends LeanArgs {
    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
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

    strFormat() {
        return `${this.func} ${Array(this.args.length).fill('%s').join(' ')}`;
    }

    latexFormat() {
        const f = `{\\color{#00f}${this.func}}`;
        return `${f}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
    }

    jsonSerialize() {
        return {
            [this.operator]: this.args.map((a) =>
                a && typeof a.jsonSerialize === 'function' ? a.jsonSerialize() : a
            ),
        };
    }
}

/** PHP Lean_fun (php/parser/lean.php ~9019–9056): lambda "fun %s". */
class Lean_fun extends LeanCommand {
    static input_priority = 18;
    get operator() {
        return 'fun';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** Port of `LbigOperator` (php/parser/lean.php ~9058–9150). */
class LeanBigOperator extends LeanArgs {
    /**
     * @param {Lean} bound
     * @param {number} indent
     * @param {number} level
     */
    constructor(bound, indent, level) {
        super([bound], indent, level);
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

    jsonSerialize() {
        return {
            [this.func]: this.args.map((a) =>
                a && typeof a.jsonSerialize === 'function' ? a.jsonSerialize() : a
            ),
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

/** Port of `LeanQuantifier` (php/parser/lean.php ~9153–9163). */
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

/** PHP Lean_import (php/parser/lean.php ~5237–5274): "import %s". */
class Lean_import extends LeanCommand {
    get operator() {
        return 'import';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP Lean_open (php/parser/lean.php ~5275–5312): "open %s". */
class Lean_open extends LeanCommand {
    get operator() {
        return 'open';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP Lean_set_option (php/parser/lean.php ~5313+): "set_option %s". */
class Lean_set_option extends LeanCommand {
    get operator() {
        return 'set_option';
    }
    strFormat() {
        return `${this.operator} %s`;
    }

    /** PHP `Lean_set_option::echo` (php/parser/lean.php ~5350–5362): multiply maxHeartbeats by 5 for proof echo. */
    echo() {
        const arg = this.arg;
        if (arg instanceof LeanArgsSpaceSeparated && arg.args.length === 2) {
            const [a0, a1] = arg.args;
            if (a0 instanceof LeanToken && a1 instanceof LeanToken && a0.text === 'maxHeartbeats') {
                a1.text = String(parseInt(a1.text, 10) * 5);
            }
        }
    }
}

/** PHP Lean_namespace (php/parser/lean.php ~5364–5376): "namespace %s". */
class Lean_namespace extends LeanCommand {
    get operator() {
        return 'namespace';
    }
}

/**
 * PHP `escape_specials` (php/parser/lean.php ~9331–9341).
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
     */
    constructor(text, indent, level) {
        super(indent, level);
        this.text = text;
        /** @type {Record<string, unknown> | null} PHP `LeanToken::$cache` */
        this.cache = null;
    }

    strFormat() {
        return this.text;
    }

    /** PHP `LeanToken::tokens_space_separated` (php/parser/lean.php ~1173–1176). */
    tokens_space_separated() {
        return [this];
    }

    /** PHP `LeanToken::isProp` (php/parser/lean.php ~1178–1181). */
    isProp(vars) {
        return (vars?.[this.text] ?? null) === 'Prop';
    }

    jsonSerialize() {
        return this.text;
    }

    /** PHP `LeanToken::starts_with_2_letters` (php/parser/lean.php ~1129–1132). */
    starts_with_2_letters() {
        return /^[a-zA-Z]{2,}/.test(this.text);
    }

    /** PHP `LeanToken::ends_with_2_letters` (php/parser/lean.php ~1134–1137). */
    ends_with_2_letters() {
        return /[a-zA-Z]{2,}$/.test(this.text);
    }

    /** PHP `LeanToken::is_variable` (php/parser/lean.php ~1158–1161). */
    is_variable() {
        return /^[a-zA-Z_][a-zA-Z_0-9]*$/.test(this.text);
    }

    /** PHP `LeanToken::lower` (php/parser/lean.php ~1163–1167). */
    lower() {
        this.text = this.text.toLowerCase();
        return this;
    }

    /** PHP `LeanToken::regexp` (php/parser/lean.php ~1169–1172). */
    regexp() {
        return ['_'];
    }

    /** PHP `LeanToken::operand_count` (php/parser/lean.php ~1183–1186). */
    operand_count() {
        const m = /\?*$/.exec(this.text);
        return m ? m[0].length : 0;
    }

    /** PHP `LeanToken::is_parallel_operator` (php/parser/lean.php ~1187–1189). */
    is_parallel_operator() {
        return /_\?+$/.test(this.text);
    }

    /** PHP `LeanToken::tactic_block_info` (php/parser/lean.php ~1191–1196). */
    tactic_block_info() {
        if (!this.cache) this.cache = {};
        const map = { 0: [this] };
        this.cache.size = 1;
        return map;
    }

    /** PHP `LeanToken::equals` (php/parser/lean.php ~1208–1211). */
    equals(other) {
        return other instanceof LeanToken && this.text === other.text;
    }

    latexFormat() {
        return '%s';
    }

    latexArgs() {
        return [this.text];
    }

    /**
     * PHP `LeanToken::latexFormat` (php/parser/lean.php ~1108–1127).
     * Uses escape_specials so identifiers like band_part render as text, not bandₚₐᵣₜ.
     * @param {Record<string, unknown>} [_syntax]
     */
    toLatex(_syntax) {
        const backslashEscaped = this.text.replace(/\\/g, '\\textbackslash ');
        return escapeSpecialsForLatex(backslashEscaped);
    }

    is_TypeStar() {
        return this.text === 'Sort' || this.text === 'Type' || this.text === 'ℝ';
    }

    /**
     * Like `LeanCaret::push_line_comment` — `Lean` default would bubble to `LeanModule` and throw at root.
     * Port of PHP behavior when `--` is parsed while the active node is a token (php/parser/lean.php ~944–947 vs ~968–973).
     */
    push_line_comment(comment) {
        const parent = this.parent;
        if (!parent) throw new Error(`push_line_comment: no parent for LeanToken`);
        const line = new LeanLineComment(comment, this.indent, this.level);
        parent.replace(this, line);
        return line;
    }

    push_token(word) {
        const level = this.level;
        const newTok = new LeanToken(word, this.indent, level);
        this.parent.replace(this, new LeanArgsSpaceSeparated([this, newTok], this.indent, level));
        return newTok;
    }

    append(New, func) {
        if (this.parent) return this.parent.insert(this, New, func);
    }

    push_quote(quote) {
        this.text += quote;
        return this;
    }
}

export class LeanLineComment extends Lean {
    constructor(text, indent, level) {
        super(indent, level);
        this.text = text;
    }

    get operator() {
        return '--';
    }

    get command() {
        return '%';
    }

    sep() {
        return ' ';
    }

    strFormat() {
        return `${this.operator}${this.sep()}${this.text}`;
    }

    is_comment() {
        return true;
    }

    /**
     * PHP LeanLineComment::latexFormat outputs "% imply" etc., but LaTeX interprets % as comment start,
     * causing "Expected '}', got 'EOF'". Emit empty for structural markers so they don't break math.
     */
    latexFormat() {
        if (this.text === 'imply' || this.text === 'given' || this.text === 'proof') return '';
        return `\\%${this.sep()}${this.text}`;
    }
}

class LeanBlockComment extends Lean {
    constructor(text, indent, level) {
        super(indent, level);
        this.text = text;
    }

    is_comment() {
        return true;
    }
}

class LeanDocString extends Lean {
    constructor(text, indent, level) {
        super(indent, level);
        this.text = text;
    }

    is_comment() {
        return true;
    }
}

export class LeanGetElem extends LeanBinary {
    static input_priority = 88;

    /** PHP LeanGetElemBaseBinary::stack_priority 18 (php/parser/lean.php ~4045–4046). Keeps slice `:` and binary ops inside the index. */
    get stack_priority() {
        return 18;
    }

    /** PHP `LeanGetElemBase::push_right` (php/parser/lean.php ~4019–4024). Absorb `]` so it closes the index bracket, not an outer LeanBracket. */
    push_right(funcName) {
        if (funcName === 'LeanBracket') return this;
        return super.push_right(funcName);
    }

    /** PHP `LeanGetElemBase::insert_comma` (php/parser/lean.php ~4026–4031). Create comma-separated index e.g. A[i, j]. */
    insert_comma(caret) {
        const caret2 = new LeanCaret(this.indent, caret.level);
        const commaSep = new LeanArgsCommaSeparated([caret, caret2], this.indent, caret2.level);
        this.args[1] = commaSep;
        commaSep.parent = this;
        return caret2;
    }

    /** PHP `LeanGetElem::latexFormat` (php/parser/lean.php ~4062–4064): subscript. */
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

    /** PHP `LeanGetElemQue::latexFormat` (php/parser/lean.php ~4076–4078). */
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
}

/**
 * Port of LeanStack (php/parser/lean.php ~9251–9286). For [i < n] body — fin.pi/bounded notation.
 * Replaces LeanBracket when closing ] on pattern (Lean_lt with LeanToken lhs).
 */
class LeanStack extends LeanArgs {
    static input_priority = 52;

    get bound() {
        return this.args[0];
    }
    get scope() {
        return this.args[1];
    }
    set scope(v) {
        if (this.args.length < 2) this.args.push(v);
        else this.args[1] = v;
        if (v) v.parent = this;
    }

    latexFormat() {
        return '\\left[{%s}\\right]{%s}';
    }

    strFormat() {
        return '[%s] %s';
    }
}

/**
 * Port of LeanBracket::push_right (php/parser/lean.php ~1878–1889). When [i < n] pattern, replace with LeanStack.
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
                const stack = new LeanStack([bound, scope], this.indent, this.level);
                scope.parent = stack;
                this.parent.replace(this, stack);
                return scope;
            }
        }
        return super.push_right(funcName);
    }

    latexFormat() {
        return '\\left[ {%s} \\right]';
    }
}

/** PHP `LeanBrace` (php/parser/lean.php ~1892–1938). */
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

/** PHP `LeanAngleBracket` (php/parser/lean.php ~1802–1845). */
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
}

/** PHP `LeanAbs` (php/parser/lean.php ~1939–1962). */
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

/** PHP `LeanNorm` (php/parser/lean.php ~1964–1982). */
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

/** PHP `LeanCeil` (php/parser/lean.php ~1984–2002). */
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

/** PHP `LeanFloor` (php/parser/lean.php ~2004–2022). */
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

/** PHP `LeanDoubleAngleQuotation` (php/parser/lean.php ~2024–2044). */
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

/** PHP `LeanUsing` (php/parser/lean.php ~7766–7810): tactic modifier `using`. */
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

/** PHP `LeanFrom` (php/parser/lean.php ~7552–7618). */
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
    relocateLastComment() {
        this.arg.relocateLastComment();
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

/** PHP `LeanMOD` (php/parser/lean.php ~7728–7763). */
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

/** PHP `LeanGeneralizing` (php/parser/lean.php ~7906–7950). */
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

/** PHP `LeanIn` (php/parser/lean.php ~7858–7904): tactic modifier `in` (not `Lean_in` ∈). */
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

/** PHP LeanAt extends LeanUnary (php/parser/lean.php ~7812–7856): modifier "at %s". */
export class LeanAt extends LeanUnary {
    get operator() {
        return 'at';
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}

/** PHP `LeanTacticBlock` (php/parser/lean.php ~8071–8151): `<;>` tactic block (structure; `echo` not fully ported). */
class LeanTacticBlock extends LeanUnary {
    is_indented() {
        return true;
    }

    sep() {
        const a = this.arg;
        return a instanceof LeanStatements ? '\n' : a instanceof LeanCaret ? '' : ' ';
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

    insert_line_comment(caret, comment) {
        if (caret instanceof LeanCaret) {
            const ind = this.indent + 2;
            const line = new LeanLineComment(comment, ind, caret.level);
            this.arg = new LeanStatements([line], ind, caret.level);
            return line;
        }
        throw new Error('LeanTacticBlock.insert_line_comment: unexpected');
    }

    get operator() {
        return '·';
    }

    get command() {
        return '\\cdot';
    }
}

export class LeanTactic extends LeanUnary {
    /**
     * @param {string} name
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     */
    constructor(name, arg, indent, level) {
        super(arg, indent, level);
        this.tacticName = name;
    }

    /**
     * Port of PHP LeanTactic::insert for modifiers like "at", "with" (php/parser/lean.php).
     * When "at h_Ξ" follows "rw [← h_band_part]", the modifier is pushed as a new arg.
     */
    insert(caret, func, type) {
        if (type === 'modifier' && this.args[this.args.length - 1] === caret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            const newCaret = new LeanCaret(this.indent, caret.level);
            this.push(new Ctor(newCaret, this.indent, caret.level));
            return newCaret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    /** PHP `LeanTactic::is_inline_tactic_block` (php/parser/lean.php ~6980–6983). */
    is_inline_tactic_block() {
        return this.tacticName === 'repeat' || this.tacticName === 'try';
    }

    /** PHP `LeanTactic::__get('stack_priority')` (php/parser/lean.php ~6996–7001). */
    get stack_priority() {
        if (this.parent instanceof LeanBy) return LeanColon.input_priority;
        if (this.tacticName === 'obtain') return LeanAssign.input_priority - 1;
        return LeanAssign.input_priority;
    }

    /** PHP `LeanTactic::insert_newline` (php/parser/lean.php ~7408–7426). */
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

    /** PHP `LeanTactic::insert_comma` (php/parser/lean.php ~7428–7443). */
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

    /** PHP `LeanTactic::insert_semicolon` (php/parser/lean.php ~7445–7466). */
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

    /** PHP `LeanTactic::strFormat` (php/parser/lean.php ~7053–7066): "func" + sep + "%s" for each arg. */
    strFormat() {
        const func = this.tacticName;
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof LeanCaret) continue;
            parts.push(arg?.constructor?.name === 'LeanSequentialTacticCombinator' &&
                /** @type {*} */ (arg).newline ? '\n' : ' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }

    /** Pass only non-Caret args to format so "simp at h_zi" renders correctly (strFormat skips LeanCaret). */
    toString() {
        const format = this.strFormat();
        const active = this.args.filter((a) => !(a instanceof LeanCaret));
        if (active.length > 0) return format.format(...active);
        return format;
    }

    /** Port of `LeanTactic::insert_line_comment` / `push_line_comment` (php/parser/lean.php ~6968–6977). */
    insert_line_comment(_caret, comment) {
        return this.push_line_comment(comment);
    }

    push_line_comment(comment) {
        const line = new LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }

    /**
     * Port of `LeanTactic::getEcho` (php/parser/lean.php ~6985–6991).
     * @returns {LeanTactic | undefined}
     */
    getEcho() {
        if (this.tacticName === 'echo') return this;
        if (this.tacticName === 'try' && this.arg instanceof LeanTactic && this.arg.tacticName === 'echo') return this.arg;
    }
}

export class LeanSequentialTacticCombinator extends LeanArgs {}

/** Placeholders for instanceof checks in parse */
export class LeanIte extends LeanArgs {}

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
     * Port of `LeanParser::build` (php/parser/lean.php ~9311–9326).
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
 * Resolve an AST class by name. Mirrors PHP `new $ClassName(...)`; there is no separate PHP registry.
 * Looks up `LEAN_CLASSES` (concrete classes only).
 * @param {string} name
 */
function getLeanClass(name) {
    const C = LEAN_CLASSES[name];
    if (C) return C;
    throw new Error(`getLeanClass: unknown class ${name} (add to LEAN_CLASSES)`);
}

/**
 * Port of global `compile` (php/parser/lean.php ~9288–9290).
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
