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

    /** PHP `Lean::regexp` (php/parser/lean.php ~904–906). */
    regexp() {
        return [];
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

    /**
     * Shallow instance copy (same pattern as `static/js/parser/sql.js` `clone()`).
     * `LeanArgs` overrides to deep-clone `this.args` (PHP `LeanArgs::__clone`).
     * @returns {this}
     */
    clone() {
        const copy = Object.create(Object.getPrototypeOf(this));
        Object.assign(copy, this);
        copy.parent = null;
        return copy;
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

    /** PHP `Lean::push_accessibility` (php/parser/lean.php ~764–767): two-arg bubble, no `this` prefix. */
    push_accessibility(_new, _accessibility) {
        if (this.parent) return this.parent.push_accessibility(_new, _accessibility);
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

    /** PHP `LeanArgs::insert_calc` (php/parser/lean.php ~1472–1481). */
    insert_calc(caret) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof LeanCaret) {
            this.replace(caret, new LeanCalc(caret, caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_calc: unexpected for ${this.constructor.name}`);
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

    /**
     * PHP `LeanArgs::__clone` (php/parser/lean.php ~1405–1411): same shell as `Lean.prototype.clone`,
     * then replace `args` with recursive `clone()` and fix `parent` links.
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
     * PHP `LeanArgs::strip_parenthesis` (php/parser/lean.php ~1479–1482).
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

    /** PHP `LeanArgs::set_line` (php/parser/lean.php ~1470–1477). */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            if (arg != null) line = arg.set_line(line);
        }
        return line;
    }

    /** PHP `LeanArgs::jsonSerialize` (php/parser/lean.php ~1443–1446). */
    jsonSerialize() {
        return this.args.map((a) =>
            a == null ? a : typeof a.jsonSerialize === 'function' ? a.jsonSerialize() : a,
        );
    }

    /** PHP `LeanArgs::traverse` (php/parser/lean.php ~1484–1491). */
    *traverse() {
        yield this;
        for (const arg of this.args) {
            if (arg != null) yield* arg.traverse();
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

    /** PHP `LeanArgsCommaSeparated::tokens_comma_separated` (php/parser/lean.php ~6785–6794). */
    tokens_comma_separated() {
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanToken) tokens.push(arg);
            else if (arg instanceof LeanAngleBracket) tokens.push(...arg.tokens_comma_separated());
        }
        return tokens;
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

/** Port of `LeanArgsNewLineSeparated` (php/parser/lean.php ~6520–6636). */
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

    /**
     * PHP `LeanArgsNewLineSeparated::insert_if` (~6549–6558).
     * Non-last caret: return undefined (see `LeanStatements.insert_if`).
     */
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

    relocateLastComment() {
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
                    return parent.relocateLastComment();
                }
            } else {
                return end.relocateLastComment();
            }
        }
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join('\n');
    }

    /** PHP trait `LeanMultipleLine::set_line` (php/parser/lean.php ~1380–1387). */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }
}

/**
 * Port of `LeanArgsCommaNewLineSeparated` (php/parser/lean.php ~6856–6919).
 * Used by `LeanPairedGroup::insert_newline` when wrapping a caret (not `LeanArgsNewLineSeparated`).
 */
export class LeanArgsCommaNewLineSeparated extends LeanArgs {
    get stack_priority() {
        return 17;
    }

    /**
     * PHP `LeanArgsCommaNewLineSeparated::insert` (php/parser/lean.php ~6869–6878).
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

    /** PHP trait `LeanMultipleLine::set_line` (php/parser/lean.php ~1380–1387). */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
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

    /** PHP `LeanBinary::set_line` (php/parser/lean.php ~2114–2122). */
    set_line(line) {
        this.line = line;
        line = this.lhs.set_line(line);
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.rhs.set_line(line);
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

    /** PHP `LeanBinary::echo` (php/parser/lean.php ~2480–2483). */
    echo() {
        this.rhs?.echo?.();
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

    /**
     * PHP `LeanAssign::split` (php/parser/lean.php ~2494–2504).
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

/** PHP `LeanBitOr` (php/parser/lean.php ~3199–3288). */
export class LeanBitOr extends LeanBinary {
    static input_priority = 47;

    /** PHP `LeanBitOr::tokens_bar_separated` (php/parser/lean.php ~3236–3247). */
    tokens_bar_separated() {
        const tokens = [];
        for (const arg of this.args) {
            if (arg instanceof LeanBitOr) tokens.push(...arg.tokens_bar_separated());
            else if (arg instanceof LeanAngleBracket) tokens.push(arg.tokens_comma_separated());
            else tokens.push(arg);
        }
        return tokens;
    }

    /** PHP `LeanBitOr::unique_token` (php/parser/lean.php ~3250–3286). */
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

    /** PHP `LeanRightarrow::insert` (php/parser/lean.php ~5533–5543). */
    insert(caret, func, type) {
        if (this.rhs === caret && caret instanceof LeanCaret) {
            const Ctor = typeof func === 'string' ? getLeanClass(func) : func;
            this.replace(caret, new Ctor(caret, caret.indent, caret.level));
            return caret;
        }
        if (this.parent) return this.parent.insert(this, func, type);
    }

    /**
     * PHP `LeanRightarrow::echo` (php/parser/lean.php ~5506–5576): inject `echo` tactic for match/induction arms.
     */
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

    /** PHP `LeanBy::echo` (php/parser/lean.php ~7482–7485). */
    echo() {
        this.arg?.echo?.();
    }

    latexFormat() {
        const arg = this.arg;
        const command = '{\\color{#00f}by}';
        if (arg instanceof LeanStatements) return `\\begin{align*}\n${command} && \\\\\n%s\n\\end{align*}`;
        return `${command}\\ %s`;
    }

    relocateLastComment() {
        this.arg?.relocateLastComment?.();
    }

    /** PHP `LeanBy::set_line` (php/parser/lean.php ~7537–7543). */
    set_line(line) {
        this.line = line;
        let L = line;
        if (this.arg instanceof LeanStatements) L++;
        return this.arg.set_line(L);
    }
}

/** PHP `LeanAttribute` (php/parser/lean.php ~8553–8614). */
class LeanAttribute extends LeanUnary {
    get operator() {
        return '@';
    }

    get command() {
        return '@';
    }

    /** PHP `LeanAttribute::append` (php/parser/lean.php ~8565–8568). */
    append(new_, _type) {
        return this.push_accessibility(new_, 'public');
    }

    /** PHP `LeanAttribute::insert_newline` (php/parser/lean.php ~8570–8574). */
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

    sep() {
        return '';
    }

    strFormat() {
        return `${this.operator}${this.sep()}%s`;
    }

    /** PHP `LeanAttribute::push_accessibility` (php/parser/lean.php ~8587–8601). */
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
    /**
     * PHP `LeanBar::split` (php/parser/lean.php ~5424–5438): clone this bar, then detach rhs statements on the clone only.
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

    /** PHP `LeanPairedGroup::set_line` (php/parser/lean.php ~1638–1648). */
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

/**
 * PHP `std\Expr` used by `eval_prefix` (php/std.php ~3567–3605).
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

/** PHP `std\eval_prefix` (php/std.php ~3608–3619). */
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

    /** PHP `LeanArgsSpaceSeparated::is_space_separated` (php/parser/lean.php ~6192–6195). */
    is_space_separated() {
        return true;
    }

    /** PHP `LeanArgsSpaceSeparated::operand_count` (php/parser/lean.php ~6443–6445). */
    operand_count() {
        return this.args[0].operand_count();
    }

    /**
     * PHP `LeanArgsSpaceSeparated::tokens_space_separated` (php/parser/lean.php ~6490–6504).
     * Angle-bracket contents are flattened (spread) so `eval_prefix` / `tactic_block_info` only see `LeanToken`s.
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

    /** PHP `LeanArgsSpaceSeparated::construct_prefix_tree` (php/parser/lean.php ~6192–6195). */
    construct_prefix_tree() {
        const tokens = this.tokens_space_separated();
        return leanEvalPrefix(tokens, (arg) => arg.operand_count());
    }

    /** PHP `LeanArgsSpaceSeparated::tactic_block_info` (php/parser/lean.php ~6452–6487). */
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

    /**
     * PHP `LeanStatements::swap_echo_star` (php/parser/lean.php ~4654–4665).
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

    /** PHP trait `LeanMultipleLine::set_line` via `LeanStatements` (php/parser/lean.php ~1378–1387). */
    set_line(line) {
        this.line = line;
        for (const arg of this.args) {
            line = arg.set_line(line) + 1;
        }
        return line - 1;
    }

    /**
     * PHP `LeanStatements::echo` (php/parser/lean.php ~4474–4519).
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
     * PHP `LeanStatements::insert_if` (php/parser/lean.php ~4521–4530).
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

    /** PHP `LeanStatements::isProp` (php/parser/lean.php ~4554–4559). */
    isProp(vars) {
        const args = this.args;
        if (args.length === 1) return args[0].isProp?.(vars);
    }

    /** PHP `LeanStatements::jsonSerialize` (php/parser/lean.php ~4560–4568). */
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

    /** PHP `Lean_def::strArgs` (php/parser/lean.php ~8735–8740). */
    strArgs() {
        const [attr, assignment] = this.args;
        if (attr == null) return [assignment];
        return this.args;
    }

    /** PHP `Lean_def::strFormat` (php/parser/lean.php ~8743–8749): uses `func` (def / theorem / lemma). */
    strFormat() {
        const acc = this.accessibility === 'public' ? '' : `${this.accessibility} `;
        let def = `${acc}${this.func} %s`;
        if (this.attribute) def = `%s\n${def}`;
        return def;
    }

    /** PHP `Lean_def::latexFormat` (php/parser/lean.php ~8714–8716). */
    latexFormat() {
        return this.strFormat();
    }

    /** PHP `Lean_def::jsonSerialize` (php/parser/lean.php ~8703–8711): key is `operator` (`'def'`), not `func`. */
    jsonSerialize() {
        const json = {
            [this.operator]: super.jsonSerialize(),
            accessibility: this.accessibility,
        };
        if (this.attribute) json.attribute = this.attribute.jsonSerialize?.() ?? this.attribute;
        return json;
    }

    /** PHP `Lean_def::insert_tactic` (php/parser/lean.php ~8694–8696). */
    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    /** PHP `Lean_def::is_indented` (php/parser/lean.php ~8698–8700). */
    is_indented() {
        return false;
    }

    /** PHP `Lean_def::set_line` (php/parser/lean.php ~8726–8732). */
    set_line(line) {
        this.line = line;
        let L = line;
        const attr = this.attribute;
        if (attr) L = attr.set_line(L) + 1;
        return this.assignment.set_line(L);
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

export class Lean_lemma extends Lean_def {
    /** PHP `Lean_lemma::echo` (php/parser/lean.php ~8758–8787). */
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

/** PHP `abstract class LeanCommand extends LeanUnary` (php/parser/lean.php ~5213–5234). No `static $input_priority` on `LeanCommand` — only `Lean_import` / `Lean_open` / `Lean_set_option` use 27; `Lean_namespace` keeps `LeanUnary`’s 47. */
class LeanCommand extends LeanUnary {
    is_indented() {
        return false;
    }

    /** PHP `__get('command')` matches `operator` for import/open/set_option/namespace. */
    get command() {
        return this.operator;
    }

    strFormat() {
        return `${this.operator} %s`;
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    /** PHP `LeanCommand::jsonSerialize` (php/parser/lean.php ~5220–5224). */
    jsonSerialize() {
        const inner = this.arg?.jsonSerialize?.() ?? this.arg;
        return { [this.func]: inner };
    }
}

/** PHP `Lean_fun` extends `LeanUnary` (php/parser/lean.php ~9019–9056). */
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

/** PHP `Lean_match` (php/parser/lean.php ~5781–5915). */
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
     * PHP `Lean_match::latexArgs` (php/parser/lean.php ~5820–5833).
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

    relocateLastComment() {
        const w = this.with;
        if (w instanceof LeanWith) w.relocateLastComment();
    }

    insert_tactic(caret, token) {
        if (caret instanceof LeanCaret) return this.insert_word(caret, token);
        return super.insert_tactic(caret, token);
    }

    /**
     * PHP `Lean_match::split` (php/parser/lean.php ~5892–5903); clone via `this.clone()` / `LeanArgs::__clone`.
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

/** PHP `LeanWith` (php/parser/lean.php ~8413–8551). */
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

    relocateLastComment() {
        const a = this.args[this.args.length - 1];
        a?.relocateLastComment?.();
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

/** Port of `LeanBigOperator` (php/parser/lean.php ~9058–9150). */
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

    /** PHP `LeanBigOperator::jsonSerialize` (php/parser/lean.php ~9131–9135): `{ [func]: parent::jsonSerialize() }`. */
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
    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'import';
    }

    /** PHP `Lean_import::append` (php/parser/lean.php ~5253–5261): `$this->arg` (PHP sources use `$this->sql`; same slot). */
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

    /** PHP `Lean_import::push_attr` (php/parser/lean.php ~5263–5270). */
    push_attr(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, new_, this.indent, caret.level);
            return new_;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** PHP Lean_open (php/parser/lean.php ~5275–5312): "open %s". */
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

/** PHP Lean_set_option (php/parser/lean.php ~5313+): "set_option %s". */
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

    push_attr(caret) {
        if (caret === this.arg) {
            const new_ = new LeanCaret(this.indent, caret.level);
            this.arg = new LeanProperty(this.arg, new_, this.indent, caret.level);
            return new_;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
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

    clone() {
        const copy = super.clone();
        copy.cache = null;
        return copy;
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
 * PHP `LeanStack` extends `LeanBigOperator` (php/parser/lean.php ~9251–9286). `[i < n] body` notation.
 */
class LeanStack extends LeanBigOperator {
    static input_priority = 52;

    get operator() {
        return 'Stack';
    }

    get command() {
        return 'Stack';
    }

    /** PHP `LeanStack::__get('stack_priority')` (php/parser/lean.php ~9261–9262). */
    get stack_priority() {
        return 28;
    }

    /** PHP `LeanStack::latexArgs` (php/parser/lean.php ~9268–9272). */
    latexArgs(syntax) {
        const s = syntax ?? {};
        s[this.constructor.name] = true;
        return super.latexArgs(s);
    }

    latexFormat() {
        return '\\left[{%s}\\right]{%s}';
    }

    /** PHP `LeanStack::push_args_indented` (php/parser/lean.php ~9279–9280): no-op. */
    push_args_indented(_indent, _newlineCount, _functionCall = true) {}

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

    /** PHP `LeanAngleBracket::tokens_comma_separated` (php/parser/lean.php ~1835–1843). */
    tokens_comma_separated() {
        const a = this.arg;
        if (a instanceof LeanArgsCommaSeparated) return a.tokens_comma_separated();
        return [a];
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

/** PHP `LeanCalc` (php/parser/lean.php ~7620–7725). */
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

    relocateLastComment() {
        this.arg.relocateLastComment();
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
     * PHP `LeanCalc::split` (php/parser/lean.php ~7693–7717): `clone $this` then detach body;
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

    /**
     * PHP `LeanTacticBlock::echo` (php/parser/lean.php ~8085–8310).
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

    /** PHP `LeanTacticBlock::tactic_block` (php/parser/lean.php ~8401–8407). */
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
     * PHP `LeanTacticBlock::split` (php/parser/lean.php ~8383–8394).
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

    /** PHP `LeanTacticBlock::set_line` (php/parser/lean.php ~8375–8380). */
    set_line(line) {
        this.line = line;
        if (this.arg instanceof LeanStatements) line++;
        return this.arg.set_line(line);
    }

    get operator() {
        return '·';
    }

    get command() {
        return '\\cdot';
    }
}

/**
 * PHP `LeanSequentialTacticCombinator` (php/parser/lean.php ~7952–8068): unary `·` / `<;>` combinator.
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
        return this.arg instanceof LeanTacticBlock || (this.arg.indent > 0 && !this.newline) ? '\n' : ' ';
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
 * PHP `abstract class LeanSyntax extends LeanArgs` (php/parser/lean.php ~6922–6955).
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

/** PHP `Lean_let` extends `LeanSyntax` (php/parser/lean.php ~8790–8917). */
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

    get stack_priority() {
        return 7;
    }

    get operator() {
        return 'let';
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

    /** PHP `Lean_let::latexFormat` (php/parser/lean.php ~8886–8890). */
    latexFormat() {
        return `{\\color{#00f}${this.command}}\\ ` + Array(this.args.length).fill('%s').join('\\ ');
    }

    /**
     * PHP `Lean_let::split` (php/parser/lean.php ~8892–8900).
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

    latexArgs(syntax) {
        return this.args.map((a) => a.toLatex(syntax));
    }
}

/** PHP `Lean_have` (php/parser/lean.php ~8920–8969). */
class Lean_have extends Lean_let {
    get operator() {
        return 'have';
    }

    get command() {
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

/** PHP `Lean_show` extends `LeanSyntax` (php/parser/lean.php ~8973–9017). */
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

    /** PHP `$this->func` */
    get func() {
        return this.tacticName;
    }

    get modifiers() {
        return this.args.slice(1);
    }

    _lastOf(Cls) {
        for (let i = this.args.length - 1; i >= 0; i--) {
            if (this.args[i] instanceof Cls) return this.args[i];
        }
    }

    get at() {
        return this._lastOf(LeanAt);
    }

    get with() {
        return this._lastOf(LeanWith);
    }

    get by() {
        return this._lastOf(LeanBy);
    }

    get arrow() {
        return this._lastOf(LeanRightarrow);
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

    /** PHP `LeanTactic::strFormat` (php/parser/lean.php ~7450–7464). */
    strFormat() {
        let func = this.tacticName;
        if (this.only) func += ' only';
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof LeanCaret) continue;
            parts.push(
                arg?.constructor?.name === 'LeanSequentialTacticCombinator' && /** @type {*} */ (arg).newline
                    ? '\n'
                    : ' ',
            );
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

    /** PHP `LeanTactic::has_tactic_block_followed` (php/parser/lean.php ~7217–7231). */
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
     * PHP `LeanTactic::get_echo_token` (php/parser/lean.php ~7054–7215).
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

    /** PHP `LeanTactic::echo` (php/parser/lean.php ~7021–7043). */
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

    /** PHP `LeanTactic::is_indented` (php/parser/lean.php ~7333–7336). */
    is_indented() {
        const p = this.parent;
        if (!p) return true;
        if (p instanceof LeanStatements || p instanceof LeanIte) return true;
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

    relocateLastComment() {
        const a = this.args[this.args.length - 1];
        if (a instanceof LeanRightarrow || a instanceof LeanWith) a.relocateLastComment?.();
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
     * PHP `LeanTactic::split` (php/parser/lean.php ~7388–7447).
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

    /**
     * Port of `LeanTactic::getEcho` (php/parser/lean.php ~7046–7052).
     * @returns {LeanTactic | undefined}
     */
    getEcho() {
        if (this.tacticName === 'echo') return this;
        if (this.tacticName === 'try' && this.arg instanceof LeanTactic && this.arg.tacticName === 'echo') return this.arg;
    }
}

/**
 * PHP `LeanIte` (php/parser/lean.php ~5917–6186): `if … then … else …`.
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
     * PHP `LeanIte::latexArgs` (php/parser/lean.php ~6078–6094).
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

    relocateLastComment() {
        const els = this.else;
        if (els instanceof LeanStatements || els instanceof LeanIte) els.relocateLastComment();
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
     * PHP `LeanIte::split` (php/parser/lean.php ~6133–6158).
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
     * PHP `LeanIte::echo_part` (php/parser/lean.php ~6179–6185).
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
