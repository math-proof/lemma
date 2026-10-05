/**
 * Abstract Lean AST node (`Lean`).
 *
 * `IndentedNode` and the helpers already declared above this factory stay in
 * `lean.js` and are passed in. Later classes are filled on `baseLate` after
 * the paired and arithmetic factories return. `LEAN_CLASSES` is the shared
 * registry (`classRegistry.map`). This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.IndentedNode
 * @param {object} deps.token2classname
 * @param {object} deps.tactics
 * @param {Function} deps.findInnermostOpenLeanAbsAncestor
 * @param {Function} deps.isIdentContinueToken
 * @param {Function} deps.leanInsertComma
 * @param {Function} deps.strStmt
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.baseLate
 */
export function createBaseFamily(deps) {
    const {
        IndentedNode,
        token2classname,
        tactics,
        findInnermostOpenLeanAbsAncestor,
        isIdentContinueToken,
        leanInsertComma,
        strStmt,
        classRegistry,
        baseLate,
    } = deps;

    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = baseLate[name];
                if (real == null) throw new Error(`${name} used before base registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = baseLate[name];
                if (real == null) throw new Error(`${name} used before base registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsCommaNewLineSeparated = lateCtor('LeanArgsCommaNewLineSeparated');
    const LeanArgsNewLineSeparated = lateCtor('LeanArgsNewLineSeparated');
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LeanAssign = lateCtor('LeanAssign');
    const LeanAt = lateCtor('LeanAt');
    const LeanAttribute = lateCtor('LeanAttribute');
    const LeanBEq = lateCtor('LeanBEq');
    const LeanBigOperator = lateCtor('LeanBigOperator');
    const LeanBitwiseOr = lateCtor('LeanBitwiseOr');
    const LeanBracket = lateCtor('LeanBracket');
    const LeanCalc = lateCtor('LeanCalc');
    const LeanCaret = lateCtor('LeanCaret');
    const LeanCeil = lateCtor('LeanCeil');
    const LeanColon = lateCtor('LeanColon');
    const LeanCondBar = lateCtor('LeanCondBar');
    const LeanConstruct = lateCtor('LeanConstruct');
    const LeanDoubleAngleQuotation = lateCtor('LeanDoubleAngleQuotation');
    const LeanEq = lateCtor('LeanEq');
    const LeanFloor = lateCtor('LeanFloor');
    const LeanGetElem = lateCtor('LeanGetElem');
    const LeanGetElemQue = lateCtor('LeanGetElemQue');
    const LeanGetElemQuote = lateCtor('LeanGetElemQuote');
    const LeanGetWhiteSquareBracket = lateCtor('LeanGetWhiteSquareBracket');
    const LeanInner = lateCtor('LeanInner');
    const LeanIte = lateCtor('LeanIte');
    const LeanLogicOr = lateCtor('LeanLogicOr');
    const LeanMatMul = lateCtor('LeanMatMul');
    const LeanMul = lateCtor('LeanMul');
    const LeanNotEquiv = lateCtor('LeanNotEquiv');
    const LeanPairedGroup = lateCtor('LeanPairedGroup');
    const LeanParenthesis = lateCtor('LeanParenthesis');
    const LeanPreimage = lateCtor('LeanPreimage');
    const LeanProperty = lateCtor('LeanProperty');
    const LeanQuantifier = lateCtor('LeanQuantifier');
    const LeanRightarrow = lateCtor('LeanRightarrow');
    const LeanSequentialTacticCombinator = lateCtor('LeanSequentialTacticCombinator');
    const LeanStatements = lateCtor('LeanStatements');
    const LeanTactic = lateCtor('LeanTactic');
    const LeanToken = lateCtor('LeanToken');
    const LeanUnaryArithmeticPost = lateCtor('LeanUnaryArithmeticPost');
    const LeanUpto = lateCtor('LeanUpto');
    const LeanWhiteSquareBracket = lateCtor('LeanWhiteSquareBracket');
    const LeanWith = lateCtor('LeanWith');
    const Lean_cdotp = lateCtor('Lean_cdotp');
    const Lean_circ = lateCtor('Lean_circ');
    const Lean_def = lateCtor('Lean_def');
    const Lean_equiv = lateCtor('Lean_equiv');
    const Lean_ge = lateCtor('Lean_ge');
    const Lean_gg = lateCtor('Lean_gg');
    const Lean_import = lateCtor('Lean_import');
    const Lean_int = lateCtor('Lean_int');
    const Lean_le = lateCtor('Lean_le');
    const Lean_lemma = lateCtor('Lean_lemma');
    const Lean_let = lateCtor('Lean_let');
    const Lean_ll = lateCtor('Lean_ll');
    const Lean_mapsto = lateCtor('Lean_mapsto');
    const Lean_namespace = lateCtor('Lean_namespace');
    const Lean_ne = lateCtor('Lean_ne');
    const Lean_open = lateCtor('Lean_open');
    const Lean_otimes = lateCtor('Lean_otimes');
    const Lean_otimesSub = lateCtor('Lean_otimesSub');
    const Lean_perp = lateCtor('Lean_perp');
    const Lean_rightarrow = lateCtor('Lean_rightarrow');
    const Lean_set_option = lateCtor('Lean_set_option');
    const Lean_simeq = lateCtor('Lean_simeq');
    const Lean_sum = lateCtor('Lean_sum');
    const Lean_theorem = lateCtor('Lean_theorem');
    const Lean_times = lateCtor('Lean_times');
    const Lean_where = lateCtor('Lean_where');
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before base registration');
            return map[key];
        },
    });

    /** Abstract Lean AST node; method order follows `scripts/reorder_lean_class.py` preset `lean`. */
    class Lean extends IndentedNode {
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

        append($new, type) {
            if (this.parent) return this.parent.append(this, $new, type);
        }

        /** `hstack` rows stacked with `++` → rectangular block cells. */
        blockMatrixRows() {
            const rows = this.flattenAppend().map((n) => n.hstackBlocks());
            if (!rows.length || rows.some((r) => !r)) return null;
            const cols = rows[0].length;
            if (cols < 1 || rows.some((r) => r.length !== cols)) return null;
            return rows;
        }

        case_default() {
            return this;
        }

        echo() {}

        /** Flatten a `++` chain, peeling grouping parentheses. */
        flattenAppend() {
            const inner = this.peelParen();
            if (inner !== this) return inner.flattenAppend();
            return [this];
        }

        getEcho() {}

        /**
         * `A.hstack B` or `Tensor.hstack A B` → `[A, B]`.
         * Grouping parentheses dispatch to the inner node.
         * @returns {Lean[] | null}
         */
        hstackBlocks() {
            const inner = this.peelParen();
            if (inner !== this) return inner.hstackBlocks();
            return null;
        }

        insert(caret, func, type) {
            if (this.parent) return this.parent.insert(this, func, type);
        }

        insert_assign(caret) {
            return caret.push_binary(LeanAssign);
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
                    {
                        const openAbs = findInnermostOpenLeanAbsAncestor(this, caret);
                        if (openAbs) return openAbs.insert_bar(caret, prevToken, next);
                    }
                    return this.insert_unary(caret, 'LeanAbs');
            }
        }

        insert_colon(caret) {
            return caret.push_binary(LeanColon);
        }

        insert_comma(caret) {
            if (this.parent) return this.parent.insert_comma(this);
        }

        insert_construct(caret) {
            return caret.push_binary(LeanConstruct);
        }

        insert_else(caret) {
            if (this.parent) return this.parent.insert_else(this);
        }

        insert_end(caret) {
            if (this.parent) return this.parent.insert_end(this);
        }

        insert_ite(caret) {
            if (caret instanceof LeanCaret) {
                this.replace(caret, new LeanIte([caret], caret.indent, caret.level));
                return caret;
            }
            const c = new LeanCaret(caret.indent, caret.level);
            const ite = new LeanIte([c], caret.indent, caret.level);
            if (this instanceof LeanArgsSpaceSeparated && this.args[this.args.length - 1] === caret) {
                this.push(ite);
                return c;
            }
            this.replace(caret, new LeanArgsSpaceSeparated([caret, ite], caret.indent, caret.level));
            return c;
        }

        insert_left(caret, func, prevToken = '') {
            return caret.push_left(func, prevToken);
        }

        insert_line_comment(caret, comment) {
            return caret.push_line_comment(comment);
        }

        insert_newline(_caret, newline_count, indent, next) {
            if (this.parent) return this.parent.insert_newline(this, newline_count, indent, next);
            throw new Error('insert_newline: no parent');
        }

        insert_only(caret) {
            if (this.parent) return this.parent.insert_only(caret);
        }

        insert_semicolon(caret) {
            if (this.parent) return this.parent.insert_semicolon(this);
        }

        insert_sequential_tactic_combinator(caret, prevToken, nextToken) {
            if (this.parent) return this.parent.insert_sequential_tactic_combinator(this, prevToken, nextToken);
        }

        insert_space(caret) {
            return caret;
        }

        insert_then(caret) {
            if (this.parent) return this.parent.insert_then(this);
        }

        insert_unary(self, funcName) {
            const parent = self.parent;
            const Ctor = LEAN_CLASSES[funcName];
            let caret;
            let replacement;
            if (self instanceof LeanCaret) {
                caret = self;
                replacement = new Ctor(caret, self.indent, self.level);
            } else if (self instanceof LeanArgsSpaceSeparated) {
                caret = new LeanCaret(self.indent, self.level);
                replacement = new Ctor(caret, self.indent, self.level);
                self.push(replacement);
                return caret;
            } else {
                caret = new LeanCaret(self.indent, self.level);
                replacement = new Ctor(caret, self.indent, self.level);
                replacement = new LeanArgsSpaceSeparated([self, replacement], self.indent, self.level);
            }
            parent.replace(self, replacement);
            return caret;
        }

        insert_word(caret, word) {
            return caret.push_token(word);
        }

        is_comment() {
            return false;
        }

        is_indented() {
            const p = this.parent;
            return p instanceof LeanArgsCommaNewLineSeparated ||
                p instanceof LeanArgsNewLineSeparated ||
                p instanceof LeanStatements ||
                (p instanceof LeanIte && !p.inline && (this === p.then || this === p.else));
        }

        isMatMulContext() {
            return false;
        }

        isMatMulOperand() {
            return this.parent != null && this.parent.isMatMulContext();
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

        matrixLatexArgs(syntax) {
            const rows = this.matrixLatexSpec();
            if (!rows) return null;
            return rows.flat().map((cell) => cell.peelParen().toLatex(syntax));
        }

        /**
         * Block matrix (`hstack` / `hstack ++ hstack`) or a stacked vector next to `@`.
         * @returns {Lean[][] | null}
         */
        matrixLatexSpec() {
            const rows = this.blockMatrixRows();
            if (rows) return rows;
            if (this.isMatMulOperand()) {
                const parts = this.flattenAppend();
                if (parts.length >= 2) return parts.map((p) => [p]);
            }
            return null;
        }

        parse(token, self) {
            const tokens = self.tokens;
            const count = tokens.length;

            // `ℝ≥0` / `ℝ≥0∞` / `ℚ≥0` — Mathlib type notations glued into one identifier
            if ((token === 'ℝ' || token === 'ℚ') && tokens[self.start_idx + 1] === '≥' && tokens[self.start_idx + 2] === '0') {
                token += '≥0';
                self.start_idx += 2;
                if (tokens[self.start_idx + 1] === '∞') {
                    token += '∞';
                    self.start_idx++;
                }
            }

            // `𝓝[>] x` / `𝓝[≠] x` — a lone relation symbol as the whole bracket content is a word.
            if (this instanceof LeanCaret && tokens[self.start_idx - 1] === '[' && tokens[self.start_idx + 1] === ']' &&
                (token === '>' || token === '<' || token === '≠' || token === '≥' || token === '≤'))
                return this.parent.insert_word(this, token);

            switch (token) {
                case 'import':
                case 'namespace':
                case 'def':
                case 'abbrev':
                case 'theorem':
                case 'lemma':
                case 'set_option':
                case 'class':
                case 'instance':
                case 'macro':
                case 'syntax':
                    return this.append(`Lean_${token}`, 'delspec');
                case 'open': {
                    let i = self.start_idx + 1;
                    while (tokens[i] === ' ') i++;
                    if (tokens[i] === 'scoped') {
                        self.start_idx = i; // loop ++ skips `scoped`
                        const caret = this.append('Lean_open', 'delspec');
                        let p = caret;
                        while (p && !(p instanceof Lean_open)) p = p.parent;
                        if (p instanceof Lean_open) p.scoped = true;
                        return caret;
                    }
                    return this.append('Lean_open', 'delspec');
                }
                case 'fun':
                case 'match': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    return this.append(`Lean_${token}`, 'expr');
                }
                case 'haveI':
                case 'letI':
                    token = token.slice(0, -1);
                case 'set':
                    // `lemma set` — keyword is the declaration name, not a tactic.
                    if (this instanceof LeanCaret && this.parent instanceof Lean_def)
                        return this.parent.insert_word(this, token);
                case 'have':
                case 'replace':
                case 'let':
                case 'show': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    return this.append(`Lean_${token}`, 'tactic');
                }
                case 'lim': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    return this.append(`Lean_${token}`, 'operator');
                }
                case 'public':
                case 'private':
                case 'protected':
                    while (tokens[++self.start_idx] === ' ');
                    switch (tokens[self.start_idx]) {
                        case 'noncomputable':
                        case 'nonrec':
                            token += ` ${tokens[self.start_idx]}`;
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
                    let newline_count = 1;
                    let indent = 0;
                    while (true) {
                        indent = 0;
                        while (tokens[self.start_idx + ++j] === ' ') ++indent;
                        if (tokens[self.start_idx + j] !== '\n') break;
                        ++newline_count;
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
                    if (indent === 0 && tokens[self.start_idx + k] === 'end') newline_count -= 1;
                    let caret = null;
                    if (
                        tokens[self.start_idx + k] === '|' &&
                        tokens[self.start_idx + k + 1] !== '|' &&
                        tokens[self.start_idx + k + 1] !== '>'
                    ) {
                        caret = LeanWith.findAlternativeCaret(this.parent, indent);
                    }
                    if (!caret && tokens[self.start_idx + k] === '∂' && indent > 0)
                        caret = Lean_int.continueMeasure(this, indent);
                    if (!caret && tokens[self.start_idx + k] === '_' && indent > 0)
                        caret = LeanCalc.continueStep(this, newline_count, indent);
                    if (
                        !caret &&
                        indent > 0 &&
                        tokens[self.start_idx + k] === '<' &&
                        tokens[self.start_idx + k + 1] === ';' &&
                        tokens[self.start_idx + k + 2] === '>'
                    )
                        caret = LeanTactic.continueSequentialTacticCombinator(this, indent);
                    if (!caret)
                        caret = this.parent.insert_newline(this, newline_count, indent, tokens[self.start_idx + k]);
                    self.start_idx += j - 1;
                    console.assert(caret != null);
                    return caret;
                }
                case '.':
                    if (tokens[self.start_idx + 1] === '.') {
                        self.start_idx++;
                        return this.push_binary(LeanUpto);
                    }
                    if (
                        this instanceof LeanCaret &&
                        (this.parent instanceof LeanStatements || this.parent instanceof LeanSequentialTacticCombinator)
                    )
                        return this.parent.insert_unary(this, 'LeanTacticBlock');
                    // `integral_fintype .of_finite` / `(.inl x)` — leading-dot identifier (dot notation on the
                    // expected type) is a separate argument, never a field access on the previous term.
                    if (
                        /^[\s(\[⟨,]$/u.test(tokens[self.start_idx - 1] ?? '') &&
                        /^[A-Za-z]/.test(tokens[self.start_idx + 1] ?? '')
                    ) {
                        let word = '.';
                        while (isIdentContinueToken(tokens[self.start_idx + 1] ?? '')) word += tokens[++self.start_idx];
                        return this.parent.insert_word(this, word);
                    }
                    // `X⁻¹.data` / `Aᵀ.det` — the caret sits on the postfix operand; the field
                    // access applies to the whole postfix term.
                    if (
                        this.parent instanceof LeanUnaryArithmeticPost &&
                        this.parent.arg === this &&
                        tokens[self.start_idx - 1] === [...this.parent.operator].pop()
                    )
                        return this.parent.push_binary(LeanProperty);
                    return this.push_binary(LeanProperty);
                case 'is': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    let p = this;
                    while (p && p.parent) {
                        const par = p.parent;
                        if (
                            par instanceof Lean_import ||
                            par instanceof Lean_open ||
                            par instanceof Lean_set_option ||
                            par instanceof Lean_namespace ||
                            par instanceof Lean_def ||
                            par instanceof Lean_theorem ||
                            par instanceof Lean_lemma ||
                            par instanceof LeanAttribute
                        )
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
                    return this.push_binary(LEAN_CLASSES[func]);
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
                case '⌉': {
                    const node = this.parent.push_right('LeanCeil');
                    // `⌈x⌉₊` — `Nat.ceil`
                    if (tokens[self.start_idx + 1] === '₊' && node instanceof LeanCeil) {
                        self.start_idx++;
                        node.nat = true;
                    }
                    return node;
                }
                case '⌊':
                    return this.parent.insert_left(this, 'LeanFloor');
                case '⌋': {
                    const node = this.parent.push_right('LeanFloor');
                    // `⌊x⌋₊` — `Nat.floor`
                    if (tokens[self.start_idx + 1] === '₊' && node instanceof LeanFloor) {
                        self.start_idx++;
                        node.nat = true;
                    }
                    return node;
                }
                case '⟦':
                    return this.parent.insert_left(this, 'LeanWhiteSquareBracket', self.start_idx ? tokens[self.start_idx - 1] : '');
                case '⟧':
                    return this.parent.push_right('LeanWhiteSquareBracket');
                case '«':
                    return this.parent.insert_left(this, 'LeanDoubleAngleQuotation');
                case '»':
                    return this.parent.push_right('LeanDoubleAngleQuotation');
                case '⟪':
                    return this.parent.insert_left(this, 'LeanInner');
                case '⟫': {
                    const node = this.parent.push_right('LeanInner');
                    // `⟪x, y⟫_ℝ` — Mathlib inner-product notation with its scalar field
                    if (node instanceof LeanInner) {
                        if (tokens[self.start_idx + 1] === '_' && /^[ℝℂ𝕜]$/u.test(tokens[self.start_idx + 2] ?? '')) {
                            node.field = '_' + tokens[self.start_idx + 2];
                            self.start_idx += 2;
                        } else if (/^_[ℝℂ𝕜]$/u.test(tokens[self.start_idx + 1] ?? '')) {
                            node.field = tokens[++self.start_idx];
                        }
                    }
                    return node;
                }
                case '‹':
                    return this.parent.insert_left(this, 'LeanSingleAngleQuotation');
                case '›':
                    return this.parent.push_right('LeanSingleAngleQuotation');
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
                    } else if (/^[A-Za-z]/.test(tokens[self.start_idx + 1] ?? '')) {
                        // named metavariable `?N` / `?hN` is one identifier
                        while (isIdentContinueToken(tokens[self.start_idx + 1] ?? '')) token += tokens[++self.start_idx];
                    }
                    return this.parent.insert_word(this, token);
                case '<':
                    if (tokens[self.start_idx + 1] === '=') {
                        self.start_idx++;
                        return this.push_binary(Lean_le);
                    }
                    if (tokens[self.start_idx + 1] === '|') {
                        self.start_idx++;
                        return this.push_arithmetic('<|');
                    }
                    if (self.start_idx + 2 < count && tokens[self.start_idx + 1] === ';' && tokens[self.start_idx + 2] === '>') {
                        let p = self.start_idx - 1;
                        while (p >= 0 && tokens[p] === ' ') --p;
                        const prevToken = tokens[p];
                        p = self.start_idx + 3;
                        while (p < tokens.length && tokens[p] === ' ') ++p;
                        const nextToken = tokens[p];
                        self.start_idx += 2;
                        return this.parent.insert_sequential_tactic_combinator(this, prevToken, nextToken);
                    }
                    if (tokens[self.start_idx + 1] === '<' && tokens[self.start_idx + 2] === '<') {
                        self.start_idx += 2;
                        token = '<<<';
                    }
                    return this.push_arithmetic(token);
                case '>':
                    if (tokens[self.start_idx + 1] === '=') {
                        self.start_idx++;
                        token += '=';
                    } else if (tokens[self.start_idx + 1] === '>' && tokens[self.start_idx + 2] === '>') {
                        self.start_idx += 2;
                        token = '>>>';
                    }
                    return this.push_arithmetic(token);
                case '≤':
                case '≥': {
                    // `≤ᵐ[μ]` / `≥ᶠ[l]` — optional unicode superscript + optional [modifier], like `=ᵐ[μ]`.
                    const Ctor = token === '≤' ? Lean_le : Lean_ge;
                    let superscript = '';
                    let modifier = '';
                    const sup = tokens[self.start_idx + 1];
                    if (sup === 'ᵐ' || sup === 'ᶠ') {
                        superscript = sup;
                        self.start_idx++;
                        if (tokens[self.start_idx + 1] === '[') {
                            self.start_idx += 2;
                            const startIdx = self.start_idx;
                            let depth = 0;
                            while (self.start_idx < tokens.length && (tokens[self.start_idx] !== ']' || depth > 0)) {
                                if (tokens[self.start_idx] === '[') depth++;
                                else if (tokens[self.start_idx] === ']') depth--;
                                self.start_idx++;
                            }
                            modifier = tokens.slice(startIdx, self.start_idx).join('');
                            if (self.start_idx < tokens.length) self.start_idx++;
                            self.start_idx--;
                        }
                    }
                    const caret = this.push_binary(Ctor);
                    if (superscript) {
                        let p = caret;
                        while (p && !(p instanceof Ctor)) p = p.parent;
                        if (p) {
                            p.superscript = superscript;
                            p.modifier = modifier;
                        }
                    }
                    return caret;
                }
                case '≪':
                    return this.push_binary(Lean_ll);
                case '≫':
                    return this.push_binary(Lean_gg);
                case '⟂': {
                    // `⟂ᵢ[π]` / `⟂ᵢ[𝕡]` — independence; optional unicode subscript + optional
                    // bracketed measure (echo only; elided in LaTeX), same shape as `→ₗ[ℝ]`.
                    let subscript = '';
                    let modifier = '';
                    const sub = tokens[self.start_idx + 1];
                    if (sub && LeanToken.subscript[sub] !== undefined) {
                        subscript = sub;
                        self.start_idx++; // consume subscript
                        if (tokens[self.start_idx + 1] === '[') {
                            self.start_idx += 2; // skip `[`, point inside
                            const startIdx = self.start_idx;
                            while (self.start_idx < tokens.length && tokens[self.start_idx] !== ']')
                                self.start_idx++;
                            modifier = tokens.slice(startIdx, self.start_idx).join('');
                            if (self.start_idx < tokens.length) self.start_idx++; // skip `]`
                            self.start_idx--; // loop will increment
                        }
                    }
                    const caret = this.push_binary(Lean_perp);
                    let p = caret;
                    while (p && !(p instanceof Lean_perp)) p = p.parent;
                    if (p) {
                        p.subscript = subscript;
                        p.modifier = modifier;
                    }
                    return caret;
                }
                case '=':
                    if (tokens[self.start_idx + 1] === '>') {
                        self.start_idx++;
                        if (this.parent instanceof LeanAt && this.parent.parent instanceof LeanTactic) {
                            const newCaret = new LeanCaret(this.indent, this.level);
                            this.parent.parent.push(newCaret);
                            return newCaret.push_binary(LeanRightarrow);
                        }
                        return this.push_binary(LeanRightarrow);
                    }
                    if (tokens[self.start_idx + 1] === '=') {
                        self.start_idx++;
                        return this.push_binary(LeanBEq);
                    }
                    {
                        // Polymorphic `=` / `=ᵐ` / `=ᵐ[ν]` — optional unicode superscript + optional [modifier].
                        let superscript = '';
                        let modifier = '';
                        const sup = tokens[self.start_idx + 1];
                        if (sup && LeanToken.supscript[sup] !== undefined) {
                            superscript = sup;
                            self.start_idx++; // consume superscript
                            if (tokens[self.start_idx + 1] === '[') {
                                self.start_idx += 2; // skip `[`, point inside
                                const startIdx = self.start_idx;
                                while (self.start_idx < tokens.length && tokens[self.start_idx] !== ']')
                                    self.start_idx++;
                                modifier = tokens.slice(startIdx, self.start_idx).join('');
                                if (self.start_idx < tokens.length) self.start_idx++; // skip `]`
                                self.start_idx--; // loop will increment
                            }
                        }
                        const caret = this.push_binary(LeanEq);
                        let p = caret;
                        while (p && !(p instanceof LeanEq)) p = p.parent;
                        if (p) {
                            p.superscript = superscript;
                            p.modifier = modifier;
                        }
                        return caret;
                    }
                case '!':
                    if (tokens[self.start_idx + 1] === '=') {
                        self.start_idx++;
                        return this.push_binary(Lean_ne);
                    }
                    if (this instanceof LeanCaret) return this.parent.insert_unary(this, 'LeanNot');
                    return this.push_post_unary('LeanFactorial');
                case ',':
                    return leanInsertComma(this);
                case ':':
                    if (tokens[self.start_idx + 1] === '=') {
                        self.start_idx++;
                        return this.parent.insert_assign(this);
                    }
                    if (tokens[self.start_idx + 1] === ':') {
                        self.start_idx++;
                        const caret = this.parent.insert_construct(this);
                        if (tokens[self.start_idx + 1] === 'ᵥ') {
                            self.start_idx++;
                            const node = caret && caret.parent;
                            if (node instanceof LeanConstruct) node.subscript = 'ᵥ';
                        }
                        return caret;
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
                    {
                        const caret = this.push_arithmetic(token);
                        if (tokens[self.start_idx + 1] === 'ᵥ') {
                            self.start_idx++;
                            const node = caret && caret.parent;
                            if (node instanceof LeanMul) node.subscript = 'ᵥ';
                        }
                        return caret;
                    }
                case '|': {
                    const next = tokens[self.start_idx + 1];
                    if (next === '|') {
                        self.start_idx++;
                        if (tokens[self.start_idx + 1] === '|') {
                            self.start_idx++;
                            return this.push_binary(LeanBitwiseOr);
                        }
                        return this.push_binary(LeanLogicOr);
                    }
                    if (next === '>') {
                        self.start_idx++;
                        if (tokens[self.start_idx + 1] === '.') {
                            self.start_idx++;
                            return this.push_arithmetic('|>.');
                        }
                        return this.push_post_unary('LeanPipeForward');
                    }
                    if (
                        tokens[self.start_idx - 1] === '[' &&
                        this instanceof LeanCaret &&
                        (this.parent instanceof LeanGetElem || this.parent instanceof LeanBracket)
                    ) {
                        // `μ[|s]` — ProbabilityTheory `cond μ s`: the bar belongs to the bracket, never to `|x|`.
                        const parent = this.parent;
                        const bar = new LeanCondBar(this, this.indent, this.level);
                        parent.replace(this, bar);
                        bar.parent = parent;
                        return this;
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
                    const prevToken = tokens[self.start_idx - 1];
                    while (isIdentContinueToken(tokens[self.start_idx + 1])) {
                        self.start_idx++;
                        token += tokens[self.start_idx];
                    }
                    if (this instanceof LeanCaret) return this.parent.insert_word(this, token);
                    if (prevToken !== undefined && isIdentContinueToken(prevToken))
                        return this.push_quote(token);
                    return this.push_token(token);
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
                case '→': {
                    // `→ₗ[ℝ]` / `→L[ℝ]` — (continuous) linear-map arrow with a subscript
                    // letter and an optional bracketed scalar-ring modifier.
                    const sub = tokens[self.start_idx + 1];
                    let subscript = '';
                    let modifier = '';
                    if (sub === 'ₗ' || sub === 'L') {
                        subscript = sub;
                        self.start_idx++; // consume subscript
                        if (tokens[self.start_idx + 1] === '[') {
                            self.start_idx += 2; // skip `[`, point inside
                            const startIdx = self.start_idx;
                            while (self.start_idx < tokens.length && tokens[self.start_idx] !== ']')
                                self.start_idx++;
                            modifier = tokens.slice(startIdx, self.start_idx).join('');
                            if (self.start_idx < tokens.length) self.start_idx++; // skip `]`
                            self.start_idx--; // loop will increment
                        }
                    } else if (sub === '+' || sub === '*') {
                        // bundled hom arrows `→+`, `→*`, `→+*`
                        subscript = sub;
                        self.start_idx++;
                        if (sub === '+' && tokens[self.start_idx + 1] === '*') {
                            subscript = '+*';
                            self.start_idx++;
                        }
                    }
                    const caret = this.push_arithmetic(token);
                    if (subscript) {
                        let p = caret;
                        while (p && !(p instanceof Lean_rightarrow)) p = p.parent;
                        if (p) {
                            p.subscript = subscript;
                            p.modifier = modifier;
                        }
                    }
                    return caret;
                }
                case '⬝': {
                    const caret = this.push_arithmetic(token);
                    if (tokens[self.start_idx + 1] === 'ᵥ') {
                        self.start_idx++;
                        const node = caret && caret.parent;
                        if (node instanceof Lean_cdotp) node.subscript = 'ᵥ';
                    }
                    return caret;
                }
                case 'ᵥ':
                    if (tokens[self.start_idx + 1] === '*') {
                        self.start_idx++; // consume `*`
                        const caret = this.push_arithmetic('*');
                        const node = caret && caret.parent;
                        if (node instanceof LeanMul) {
                            node.subscript = 'ᵥ';
                            node.isLeftSubscript = true;
                        }
                        return caret;
                    }
                    return this.parent.insert_word(this, token);
                case '×': {
                    const nextTok = tokens[self.start_idx + 1];
                    const sprod = nextTok === 'ˢ';
                    const hasSub = nextTok === 'ₖ';
                    if (sprod || hasSub) self.start_idx++;
                    const caret = this.push_arithmetic('×');
                    if (sprod) {
                        let p = caret;
                        while (p && !(p instanceof Lean_times)) p = p.parent;
                        if (p) p.superscript = 'ˢ';
                    }
                    if (hasSub) {
                        let p = caret;
                        while (p && !(p instanceof Lean_times)) p = p.parent;
                        if (p) p.subscript = 'ₖ';
                    }
                    return caret;
                }
                case '⊗': {
                    // `μ ⊗ₘ κ` / `κ ⊗ₖ η` — (measure / kernel) composition-product with a subscript letter.
                    const sub = tokens[self.start_idx + 1];
                    const hasSub = sub === 'ₘ' || sub === 'ₖ';
                    if (hasSub) self.start_idx++; // consume subscript
                    const caret = hasSub ? this.push_binary(Lean_otimesSub) : this.push_arithmetic(token);
                    if (hasSub) {
                        let p = caret;
                        while (p && !(p instanceof Lean_otimes)) p = p.parent;
                        if (p) p.subscript = sub;
                    }
                    return caret;
                }
                case '∘': {
                    // `∘ₘ` — composition with a subscript letter.
                    const hasSub = tokens[self.start_idx + 1] === 'ₘ';
                    if (hasSub) self.start_idx++;
                    const caret = this.push_arithmetic(token);
                    if (hasSub) {
                        let p = caret;
                        while (p && !(p instanceof Lean_circ)) p = p.parent;
                        if (p) p.subscript = 'ₘ';
                    }
                    return caret;
                }
                // fallthrough: bare '/' uses same rule as '%'
                case '⊗': {
                    // `⊗ₘ` — tensor product of kernels with a subscript letter.
                    const hasSub = tokens[self.start_idx + 1] === 'ₘ';
                    if (hasSub) self.start_idx++; // consume subscript
                    const caret = this.push_arithmetic(token);
                    if (hasSub) {
                        let p = caret;
                        while (p && !(p instanceof Lean_otimes)) p = p.parent;
                        if (p) p.subscript = 'ₘ';
                    }
                    return caret;
                }
                case '%':
                case '•':
                case '⊙':
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
                case '↦':
                case '↔':
                case '∧':
                case '∨':
                case '≠':
                case '≡':
                case '≢':
                case '≍':
                case '≈':
                case '∣':
                    return this.push_arithmetic(token);
                case '≃': {
                    const ae = tokens[self.start_idx + 1] === 'ᵐ';
                    if (ae) self.start_idx++;
                    let subscript = '';
                    let modifier = '';
                    if (!ae && tokens[self.start_idx + 1] === 'L' &&
                            tokens[self.start_idx + 2] === '[') {
                        subscript = 'L';
                        self.start_idx += 3; // skip `L[`, point inside
                        const startIdx = self.start_idx;
                        while (self.start_idx < tokens.length && tokens[self.start_idx] !== ']')
                            self.start_idx++;
                        modifier = tokens.slice(startIdx, self.start_idx).join('');
                        if (self.start_idx < tokens.length) self.start_idx++; // skip `]`
                        self.start_idx--; // loop will increment
                    }
                    const caret = this.push_arithmetic('≃');
                    if (ae) {
                        let p = caret;
                        while (p && !(p instanceof Lean_simeq)) p = p.parent;
                        if (p) p.superscript = 'ᵐ';
                    }
                    if (subscript) {
                        let p = caret;
                        while (p && !(p instanceof Lean_simeq)) p = p.parent;
                        if (p) {
                            p.subscript = subscript;
                            p.modifier = modifier;
                        }
                    }
                    return caret;
                }
                case '←':
                    return this.parent.insert_unary(this, 'Lean_leftarrow');
                case '∀':
                case '∃': {
                    // `∀ᵐ` / `∃ᵐ` — almost-everywhere quantifier; the modifier letter U+1D50
                    // would otherwise be swallowed as an ordinary identifier inside the bound.
                    // `∀ᶠ x in l, p` / `∃ᶠ x in l, p` — eventually / frequently along a filter.
                    const sup = tokens[self.start_idx + 1];
                    const ae = sup === 'ᵐ' || sup === 'ᶠ';
                    if (ae) self.start_idx++;
                    // `∃!` — unique existence; the `!` would otherwise parse as `‹! x›` (negation) in the bound.
                    const uq = token === '∃' && tokens[self.start_idx + 1] === '!';
                    if (uq) self.start_idx++;
                    const caret = this.append(token === '∀' ? 'Lean_forall' : 'Lean_exists', 'operator');
                    if (ae) {
                        let p = caret;
                        while (p && !(p instanceof LeanQuantifier)) p = p.parent;
                        if (p) p.superscript = sup;
                    }
                    if (uq) {
                        let p = caret;
                        while (p && !(p instanceof LeanQuantifier)) p = p.parent;
                        if (p) p.unique = true;
                    }
                    return caret;
                }
                case '∑': {
                    const caret = this.append('Lean_sum', 'operator');
                    if (tokens[self.start_idx + 1] === "'") {
                        self.start_idx++;
                        let p = this;
                        while (p && !(p instanceof Lean_sum)) p = p.parent;
                        if (p) p.superscript = "'";
                    }
                    return caret;
                }
                case '∏':
                    return this.append('Lean_prod', 'operator');
                case '⋃':
                    return this.append('Lean_bigcup', 'operator');
                case '⋂':
                    return this.append('Lean_bigcap', 'operator');
                case '⨅':
                    return this.append('LeanInf', 'operator');
                case '⨆':
                    return this.append('LeanSup', 'operator');
                case '∫': {
                    const neg = tokens[self.start_idx + 1] === '⁻';
                    if (neg) self.start_idx++;
                    const caret = this.append('Lean_int', 'operator');
                    if (neg) {
                        let p = caret;
                        while (p && !(p instanceof Lean_int)) p = p.parent;
                        if (p) p.superscript = '⁻';
                    }
                    return caret;
                }
                case '¬':
                    return this.parent.insert_unary(this, 'Lean_lnot');
                case '∂':
                    return this.parent.insert_unary(this, 'Lean_partial');
                case '~':
                    return this.parent.insert_unary(this, 'LeanConj');
                case '√':
                    return this.parent.insert_unary(this, 'Lean_sqrt');
                case '∛':
                    return this.parent.insert_unary(this, 'LeanCubicRoot');
                case '∜':
                    return this.parent.insert_unary(this, 'LeanQuarticRoot');
                case '↑':
                    return this.parent.insert_unary(this, 'Lean_uparrow');
                case '⇑':
                    return this.parent.insert_unary(this, 'LeanUparrow');
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
                        if (tokens[self.start_idx + 1] === "'") {
                            self.start_idx++;
                            // Mathlib `infixl:80 " ⁻¹' "`: application binds tighter, so `s t ⁻¹' A` is `(s t) ⁻¹' A`.
                            const spaced = tokens[self.start_idx - 3] === ' ';
                            const app = this.parent;
                            const node = app instanceof LeanArgsSpaceSeparated && app.args[app.args.length - 1] === this &&
                                app.args.filter((a) => !(a instanceof LeanCaret)).length >= 2
                                ? Lean.prototype.push_post_unary.call(app, 'LeanPreimage')
                                : this.push_post_unary('LeanPreimage');
                            if (node instanceof LeanPreimage) node.spaced = spaced;
                            return node;
                        }
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
                case 'from': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    return this.parent.insert(this, `Lean${token[0].toUpperCase() + token.slice(1)}`, 'modifier');
                }
                case 'where': {
                    // `class … where <body>` / `instance … where <body>`: split header from body.
                    return this.push_binary(Lean_where);
                }
                case 'calc': {
                    const asPropertyField = self.parseKeywordAsPropertyField(this, token);
                    if (asPropertyField) return asPropertyField;
                    return this.parent.insert_calc(this);
                }
                case '·':
                    if (this.parent instanceof LeanStatements || this.parent instanceof LeanSequentialTacticCombinator)
                        return this.parent.insert_unary(this, 'LeanTacticBlock');
                    return this.parent.insert_word(this, token);
                case '@':
                    if (this instanceof LeanCaret) {
                        // `@[` is an attribute; `@expr` is explicit argument application
                        let next = self.start_idx + 1;
                        while (tokens[next] === ' ') next++;
                        if (tokens[next] === '[') {
                            return this.parent.insert_unary(this, 'LeanAttribute');
                        }
                        // `@f` — explicit-argument marker glued to the identifier
                        if (/^[A-Za-z]/.test(tokens[self.start_idx + 1] ?? '')) {
                            let word = '@';
                            while (isIdentContinueToken(tokens[self.start_idx + 1] ?? '')) word += tokens[++self.start_idx];
                            return this.parent.insert_word(this, word);
                        }
                        return this.parent.insert_word(this, '@');
                    }
                    return this.push_binary(LeanMatMul);
                case 'end':
                    return this.parent.insert_end(this);
                case 'only':
                    // `<;> (simp only [h]; rfl)` — tactics inside `( … )` are plain words; `only` too.
                    for (let p = this.parent; p; p = p.parent) {
                        if (p instanceof LeanTactic) break;
                        if (p instanceof LeanParenthesis) return this.parent.insert_word(this, token);
                    }
                    return this.parent.insert_only(this);
                case 'if': {
                    let n = this.parent;
                    while (n) {
                        if (typeof n.insert_if === 'function') {
                            const next = n.insert_if(this);
                            if (next !== undefined) return next;
                        }
                        n = n.parent;
                    }
                    throw new Error('insert_if is unexpected');
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
                    if (index < tactics.length && tactics[index] === tokenOrig && this instanceof LeanCaret)
                        return this.parent.insert_tactic(this, token);
                    return this.parent.insert_word(this, token);
                }
            }
        }

        /** Default: leave the node as-is. Colon / `↑` / `(e : T)` override this. */
        peelLatexCoe() {
            return this;
        }

        /** Strip grouping parentheses (not `(e : T)` ascriptions). */
        peelParen() {
            return this;
        }

        /**
         * Peel pure grouping wrappers: parentheses and singleton space-separated
         * groups. Default leaves the node as-is; `LeanParenthesis` and singleton
         * `LeanArgsSpaceSeparated` override to recurse into their single child.
         */
        peelGroup() {
            return this;
        }

        /**
         * Head text of an application chain `Measure Ω` / `M.Measure Ω` -> its head
         * identifier (e.g. `Measure`, `M.Measure`); `null` if none can be extracted.
         */
        appHead() {
            const g = this.peelGroup();
            if (g instanceof LeanToken) return g.text;
            if (g instanceof LeanArgsSpaceSeparated && g.args.length >= 1) {
                const h = g.args[0];
                if (h instanceof LeanToken || h instanceof LeanProperty) return strStmt(h).trim();
            }
            return null;
        }

        /** True if this node's `appHead()` equals `name` or ends with `.<name>`. */
        headIs(name) {
            const h = this.appHead();
            return h === name || (h != null && h.endsWith('.' + name));
        }

        /**
         * Binder names introduced by the lhs of `↦` / `x : T` / `x in s`.
         * @param {unknown} node
         * @returns {string[]}
         * @protected
         */
        static _binderNames(node) {
            /** @type {string[]} */
            const names = [];
            const go = (x) => {
                const y = x.peelGroup();
                if (y instanceof LeanToken) names.push(y.text);
                else if (y instanceof LeanColon) go(y.lhs);
                else if (y instanceof LeanArgsSpaceSeparated) y.args.forEach(go);
                else if (y instanceof LeanDoubleAngleQuotation && y.boundValueLhs())
                    names.push(strStmt(y.arg).trim());
            };
            go(node);
            return names;
        }

        markRandomVarNames(rvNames, letBound = []) {
            /** @type {string[][]} */
            const localFrames = [];
            const isHidden = (name) =>
                letBound.includes(name) || localFrames.some((f) => f.includes(name));

            const walk = (n) => {
                if (!n || typeof n !== 'object') return;
                if (n instanceof LeanDoubleAngleQuotation && n.boundValueLhs())
                    return;
                if (n instanceof LeanToken) {
                    if (rvNames.has(n.text) && !isHidden(n.text))
                        n.kwargs.isRandomVariable = true;
                    return;
                }
                // `Measure.map X` (e.g. `𝕡.map a`) — the argument is a random variable
                if (n instanceof LeanArgsSpaceSeparated) {
                    const head = n.args[0];
                    if (head instanceof LeanProperty && head.rhs instanceof LeanToken
                        && head.rhs.text === 'map') {
                        const rv = n.args[1];
                        if (rv instanceof LeanToken) rv.kwargs.isRandomVariable = true;
                    }
                }
                if (n instanceof Lean_mapsto) {
                    localFrames.push(Lean._binderNames(n.lhs));
                    walk(n.rhs);
                    localFrames.pop();
                    return;
                }
                if (n instanceof LeanBigOperator) {
                    localFrames.push(n.bound ? Lean._binderNames(n.bound) : []);
                    // domain/type of the bound variable is outside its own scope
                    if (n.bound instanceof LeanColon) walk(n.bound.rhs);
                    if (n.scope) walk(n.scope);
                    localFrames.pop();
                    return;
                }
                if (n instanceof Lean_let) {
                    // RHS is evaluated first; the name binds only the continuation
                    const a = n.arg;
                    if (a instanceof LeanAssign) {
                        if (a.lhs instanceof LeanColon) {
                            walk(a.lhs.rhs);
                            walk(a.rhs);
                            letBound.push(...Lean._binderNames(a.lhs.lhs));
                        } else {
                            walk(a.rhs);
                            letBound.push(...Lean._binderNames(a.lhs));
                        }
                    } else if (a instanceof LeanColon && a.rhs instanceof LeanAssign) {
                        walk(a.rhs.rhs);
                        letBound.push(...Lean._binderNames(a.rhs.lhs));
                    }
                    return;
                }
                if (Array.isArray(n.args)) for (const k of n.args) walk(k);
            };
            walk(this);
        }

        push_accessibility($new, accessibility) {
            if (this.parent) return this.parent.push_accessibility($new, accessibility);
        }

        push_arithmetic(token) {
            const cls = token2classname[token];
            if (!cls) throw new Error(`push_arithmetic: unknown token ${JSON.stringify(token)}`);
            return this.push_binary(LEAN_CLASSES[cls]);
        }

        push_attr(_caret) {
            throw new Error('push_attr is unexpected for ' + this.constructor.name);
        }

        push_binary(Ctor) {
            const parent = this.parent;
            if (!parent) return undefined;
            if (parent instanceof LeanStatements) return parent.push_binary(Ctor);
            if (Ctor.input_priority > parent.stack_priority) {
                const level = this.level;
                const caret = new LeanCaret(this.indent, level);
                parent.replace(this, new Ctor(this, caret, this.indent, level));
                return caret;
            }
            return parent.push_binary(Ctor);
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
                case 'LeanWhiteSquareBracket':
                case 'LeanDoubleAngleQuotation':
                case 'LeanInner':
                case 'LeanSingleAngleQuotation': {
                    const {indent, level} = this;
                    const caret = new LeanCaret(indent, level);
                    if (func === 'LeanBracket') {
                        if (prevToken === ' ') {
                            let self = this;
                            let par = self.parent;
                            while (par) {
                                if (par instanceof Lean_equiv || par instanceof LeanNotEquiv) {
                                    const newNode = new (LEAN_CLASSES[func])(caret, indent, level);
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
                            this instanceof LeanBracket ||
                            this instanceof LeanDoubleAngleQuotation ||
                            (this instanceof LeanPairedGroup && this.is_Expr())
                        ) {
                            this.parent.replace(this, new LeanGetElem(this, caret, indent, level));
                            return caret;
                        }
                    }
                    if (
                        func === 'LeanWhiteSquareBracket' &&
                        prevToken !== ' ' &&
                        (this instanceof LeanToken ||
                            this instanceof LeanProperty ||
                            this instanceof LeanGetElem ||
                            this instanceof LeanGetElemQue ||
                            this instanceof LeanGetElemQuote ||
                            this instanceof LeanGetWhiteSquareBracket ||
                            this instanceof LeanUnaryArithmeticPost ||
                            this instanceof LeanBracket ||
                            this instanceof LeanWhiteSquareBracket ||
                            (this instanceof LeanPairedGroup && this.is_Expr()))
                    ) {
                        this.parent.replace(this, new LeanGetWhiteSquareBracket(this, caret, indent, level));
                        return caret;
                    }
                    const paired = new (LEAN_CLASSES[func])(caret, indent, level);
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
            const Ctor = LEAN_CLASSES[funcName];
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
            // `a.b⁻¹` / `Prod.snd⁻¹' s` — the postfix applies to the whole dotted name
            if (parent instanceof LeanProperty && parent.rhs === this && this instanceof LeanToken)
                return parent.push_post_unary(funcName);
            const Ctor = LEAN_CLASSES[funcName];
            if (Ctor.input_priority > parent.stack_priority) {
                const created = new Ctor(this, this.indent, this.level);
                parent.replace(this, created);
                // The caret is the postfix node itself, so a following binary operator
                // (`x⁻¹ * b`, `x² + 1`) takes `x⁻¹` as its lhs instead of splitting `x`
                // out of the postfix (which printed `x * b⁻¹`).
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

    return {
        Lean,
    };
}
