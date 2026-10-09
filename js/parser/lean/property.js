/**
 * Field access `a.b` (`LeanProperty`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class LeanProperty extends LeanBinary {
    static { this.register(); }

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
            if (caret instanceof L.LeanCaret) {
                if (func.startsWith('Lean_')) {
                    return this.insert_word(caret, func.slice(5));
                }
            } else if (type === 'modifier') {
                return this.parent.insert(this, func, type);
            } else {
                const newCaret = new L.LeanCaret(this.indent, caret.level);
                this.parent.replace(
                    this,
                    new L.LeanArgsSpaceSeparated(
                        [this, new (L[func])(newCaret, newCaret.indent, newCaret.level)],
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
        if (this.parent instanceof L.LeanTactic && indent > this.indent) {
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
        if (caret instanceof L.LeanCaret) {
            return super.insert_word(caret, word);
        }
        if (this.parent) {
            return this.parent.insert_word(this, word);
        }
    }

    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanArgsCommaNewLineSeparated ||
            parent instanceof L.LeanArgsNewLineSeparated ||
            parent instanceof L.LeanStatements ||
            (parent instanceof L.LeanArgsIndented && parent.rhs === this) ||
            (parent instanceof L.LeanIte && !parent.inline && parent.else === this);
    }

    isProp(vars) {
        const rhs = this.rhs;
        if (rhs instanceof L.LeanToken) {
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
        if (rhs instanceof L.LeanToken) {
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
        if (rhs instanceof L.LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    arg = '%s';
                    if (lhs instanceof L.LeanToken) {
                        switch (lhs.text) {
                            case 'Real':
                            case 'Complex':
                            case 'Exp':
                                arg = null;
                        }
                    }
                    if (arg) {
                        const exponent = L.LeanParenthesis.peelLatex(this.lhs);
                        return [exponent.toLatex(syntax)];
                    }
                    break;
                case 'cos':
                case 'sin':
                case 'tan':
                case 'log':
                    arg = '%s';
                    if (lhs instanceof L.LeanToken) {
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
                    if (!(lhs instanceof L.LeanToken && this.parent instanceof L.LeanArgsSpaceSeparated && this.parent.args[0] === this)) {
                        let arg = this.lhs;
                        if (arg instanceof L.LeanParenthesis && !(arg.arg instanceof L.LeanColon))
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
                    if (arg instanceof L.LeanParenthesis && !(arg.arg instanceof L.LeanColon))
                        arg = arg.arg;
                    return [arg.toLatex(syntax)];
                }
                case 'natAbs': {
                    let arg = this.lhs;
                    if (arg instanceof L.LeanParenthesis) arg = arg.arg;
                    if (arg instanceof L.LeanColon) arg = arg.lhs;
                    return [arg.toLatex(syntax)];
                }
                case 'toReal':
                    // ENNReal→ℝ: `ℙ[…](…).toReal` — keep the paren so Prob short-form / `\middle|` still run
                    return [this.lhs.toLatex(syntax)];
            }
        }
        return super.latexArgs(syntax);
    }

    latexFormat() {
        const [lhs, rhs] = this.args;
        var arg;
        if (rhs instanceof L.LeanToken) {
            switch (rhs.text) {
                case 'exp':
                    arg = '%s';
                    if (lhs instanceof L.LeanToken) {
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
                    if (lhs instanceof L.LeanToken) {
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
                    if (!(lhs instanceof L.LeanToken && this.parent instanceof L.LeanArgsSpaceSeparated && this.parent.args[0] === this)) {
                        return '\\left|{%s}\\right|';
                    }
                    break;
                case 'epsilon':
                    if (lhs instanceof L.LeanToken && lhs.text === 'Hyperreal') {
                        return '0^+';
                    }
                    break;
                case 'omega':
                    if (lhs instanceof L.LeanToken && lhs.text === 'Hyperreal') {
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
                case 'toReal':
                    return '%s';
            }
        }
        return `{%s}${this.command}{%s}`;
    }

    push_attr(caret) {
        return super.push_attr(caret);
    }

    push_token(word) {
        const level = this.level;
        const newToken = new L.LeanToken(word, this.indent, level);
        this.parent.replace(this, new L.LeanArgsSpaceSeparated([this, newToken], this.indent, level));
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
        if (rhs instanceof L.LeanArgsSpaceSeparated && rhs.args.length === 2 && rhs.args[0] instanceof L.LeanCaret) {
            rhs = rhs.args[1];
        }
        return [this.lhs, rhs];
    }
}
