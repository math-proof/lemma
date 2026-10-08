/**
 * Abstract argument bases: `LeanArgs`, `LeanUnary`, `LeanBinary`.
 *
 * PHP `LeanUnary` / `LeanBinary` are `abstract`; these JS classes are concrete.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { leanSubtreeContains, token2classname } from './utility.js';
import { Lean } from './base.js';

const L = Lean.classes;

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
    static { this.register(); }

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
        if (last === caret && caret instanceof L.LeanCaret) {
            this.replace(caret, new L.LeanCalc(caret, caret.indent, caret.level));
            return caret;
        }
        throw new Error(`insert_calc: unexpected for ${this.constructor.name}`);
    }

    insert_tactic(caret, func) {
        if (caret instanceof L.LeanCaret) {
            this.replace(caret, new L.LeanTactic(func, caret, caret.indent, caret.level));
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
            end instanceof L.LeanToken ||
            end instanceof L.LeanProperty ||
            end instanceof L.LeanParenthesis
        ) {
            const caret = new L.LeanCaret(indent, end.level);
            const nl = new L.LeanArgsNewLineSeparated([caret], indent, caret.level);
            const c = nl.push_newlines(newline_count - 1);
            this.replace(end, new L.LeanArgsIndented(end, nl, this.indent, c.level));
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
            if (!(arg instanceof L.LeanParenthesis)) return arg;
            // a tuple `(a, b)` / a `·` section `(· t)`: the parentheses are part of the term
            if (arg.latexParenRequired()) return arg;
            const inner = arg.arg;
            if (
                inner instanceof L.LeanMethodChaining ||
                inner instanceof L.Lean_rightarrow ||
                inner instanceof L.LeanColon
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
    static { this.register(); }

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
        if (this.arg === caret && caret instanceof L.LeanCaret) {
            this.arg = new L.LeanIte([caret], caret.indent, caret.level);
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

// Paired delimiters live in ./lean/paired.js and register themselves in `Lean.classes`.

export class LeanBinary extends LeanArgs {
    static { this.register(); }

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
        if (this instanceof L.LeanArgsIndented && caret instanceof L.LeanCaret) {
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
        return this.rhs instanceof L.LeanStatements ? '\n' : ' ';
    }

    set_line(line) {
        this.line = line;
        line = this.lhs.set_line(line);
        const s = this.sep();
        if (s && s[0] === '\n') line++;
        return this.rhs.set_line(line);
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.parent instanceof L.LeanTactic && indent > this.indent) {
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
