import { AbstractParser, Node, IndentedNode, Closable, MatchTrait } from "./node.js";
import XMLParser from "./xml.js";
import NewLineParser from "./newline.js";

class Markdown extends MatchTrait(IndentedNode) {
    get kwargs_list() {
        return [];
    }

    clone() {
        return new this.constructor(this.indent, ...this.kwargs_list);
    }

    get indent() {
        return this.kwargs.indent;
    }

    set indent(indent) {
        this.kwargs.indent = indent;
    }

    get html() {
        const html = this.htmlFormat();
        if (this.args && this.args.length)
            return html.format(...this.args.map(arg => arg.html));
        return html;
    }

    htmlFormat() {
        return this.strFormat();
    }

    toString() {
        var s = super.toString();
        if (this.is_indented())
            s = ' '.repeat(this.indent) + s;
        return s;
    }

    get plainText() {
        const strFormat = this.strFormat();
        let text = this.args && this.args.length > 0? strFormat.format(...this.args.map(arg => arg.plainText)) : strFormat;
        if (this.is_indented())
            text = ' '.repeat(this.indent) + text;
        return text;
    }

    has_newline() {
        return this.is_Paragraph;
    }

    push_token(word, ...kwargs) {
        return this.append(new MarkdownText(word, this.indent, ...kwargs));
    }

    push_left_bracket(...kwargs) {
        var indent = this.indent;
        var caret = new MarkdownCaret(indent, ...kwargs);
        caret.start_idx++;
        var $new = new MarkdownBracket(caret, indent);
        if (isinstance(this.parent, MarkdownSPAN) || isinstance(this.parent, MarkdownDocument) && !isinstance(this, MarkdownText))
            this.parent.push($new);
        else 
            this.parent.replace(this, new MarkdownSPAN([this, $new], indent));
        return caret;
    }
    push_left_parenthesis(...kwargs) {
        return this.push_token('(', ...kwargs);
    }
    push_tilde(...kwargs) {
        return this.push_token('~', ...kwargs);
    }

    case_space(...kwargs) {
        return this.parent.insert_space(this, ...kwargs);
    }
    case_newline(...kwargs) {
        return new NewLineParser(this, true, ...kwargs);
    }
    case_asterisk(...kwargs) {
        return this.parent.insert_asterisk(this, ...kwargs);
    }
    case_underscore(...kwargs) {
        return this.parent.insert_underscore(this, ...kwargs);
    }
    case_left_bracket(...kwargs) {
        return this.parent.insert_left_bracket(this, ...kwargs);
    }
    case_right_bracket(...kwargs) {
        return this.parent.insert_right_bracket(this, ...kwargs);
    }
    case_left_parenthesis(...kwargs) {
        return this.parent.insert_left_parenthesis(this, ...kwargs);
    }
    case_right_parenthesis(...kwargs) {
        return this.parent.insert_right_parenthesis(this, ...kwargs);
    }
    case_lt(...kwargs) {
        return this.parent.insert_lt(this, ...kwargs);
    }
    case_ampersand(...kwargs) {
        return this.parent.insert_ampersand(this, ...kwargs);
    }
    case_bar(...kwargs) {
        return this.parent.insert_bar(this, ...kwargs);
    }
    case_tilde(...kwargs) {
        return this.parent.insert_tilde(this, ...kwargs);
    }
    case_quotation(...kwargs) {
        return this.parent.insert_quotation(this, ...kwargs);
    }
    case_apostrophe(...kwargs) {
        return this.parent.insert_apostrophe(this, ...kwargs);
    }
    case_backtick(...kwargs) {
        return this.parent.insert_backtick(this, ...kwargs);
    }
    case_dollar(...kwargs) {
        return this.parent.insert_dollar(this, ...kwargs);
    }
    case_tab(...kwargs) {
        return this.case_default('    ', ...kwargs);
    }
    case_default(token, ...kwargs) {
        return this.parent.insert_token(this, token, ...kwargs);
    }
    isspace() {
        return false;
    }
}
Markdown.case = {
    ' ': Markdown.prototype.case_space,
    "\n": Markdown.prototype.case_newline,
    '*': Markdown.prototype.case_asterisk,
    '_': Markdown.prototype.case_underscore,
    '[': Markdown.prototype.case_left_bracket,
    ']': Markdown.prototype.case_right_bracket,
    '(': Markdown.prototype.case_left_parenthesis,
    ')': Markdown.prototype.case_right_parenthesis,
    '<': Markdown.prototype.case_lt,
    '&': Markdown.prototype.case_ampersand,
    '|': Markdown.prototype.case_bar,
    '~': Markdown.prototype.case_tilde,
    '"': Markdown.prototype.case_quotation,
    "'": Markdown.prototype.case_apostrophe,
    '`': Markdown.prototype.case_backtick,
    '$': Markdown.prototype.case_dollar,
    "\t": Markdown.prototype.case_tab
}
class MarkdownCaret extends Markdown {
    constructor(indent = 0, start_idx=null, parent = null, ...kwargs) {
        console.assert (Number.isInteger(indent) && Number.isInteger(start_idx));
        super(indent, parent, ...kwargs);
        this.start_idx = start_idx;
    }
    get text() {
        return '';
    }
    is_indented() {
        return false;
    }
    strFormat() {
        return '';
    }
    append($new) {
        this.parent.replace(this, $new);
        return $new;
    }
    push_token(word, ...kwargs) {
        var $new = new MarkdownText(word, this.indent, ...kwargs);
        this.parent.replace(this, $new);
        return $new;
    }
    push_left_bracket(...kwargs) {
        var caret = this;
        caret.start_idx++;
        this.parent.replace(this, new MarkdownBracket(caret, this.indent));
        return caret;
    }
    isspace() {
        return true;
    }
}

class MarkdownText extends Markdown {
    get is_MarkdownText() {
        return true;
    }
    get is_token() {
        return true;
    }
    constructor(text, indent=0, start_idx=null, parent=null) {
        console.assert (typeof text === 'string' && Number.isInteger(indent) && Number.isInteger(start_idx));
        super(indent, parent);
        this.text = text;
        this.start_idx = start_idx;
    }

    has_newline() {
        return this.text.includes('\n');
    }

    append($new) {
        if (this.parent)
            return this.parent.insert(this, $new);
        throw new Error('append is not defined for', get_class(this), $new);
    }

    push_token(word, ...kwargs) {
        this.text += word;
        return this;
    }

    is_indented() {
        return false;
    }

    htmlFormat() {
        let html = this.text.replace(/</g, '&lt;').replace(/>/g, '&gt;');
        return html.replace(/\\_/g, '&#95;');
    }

    strFormat() {
        return this.text;
    }

    strArgs() {
        return [this.text];
    }

    push_patten(cls, stop) {
        var m;
        // First condition: check for pattern at end of text
        if (!this.text.match(cls.regex_skip)) {
            if ((m = this.text.match(cls.regex_text)) && m[1]) {
                this.text = this.text.slice(0, -m[0].length);
                var $new = new MarkdownText(m[1], this.indent, this.start_idx + m.indices[1][0]);
                var new_pattern = new cls($new, this.indent);
                if (this.text) {
                    if (this.parent instanceof MarkdownSPAN)
                        this.parent.push(new_pattern);
                    else
                        this.parent.replace(this, new MarkdownSPAN([this, new_pattern], this.indent));
                }
                else
                    this.parent.replace(this, new_pattern);
                return new_pattern;
            }
            // Second condition: handle parent spans
            if (this.parent instanceof MarkdownSPAN || this.parent instanceof MarkdownLI) {
                var $new = cls.try_pattern(this, stop);
                if ($new)
                    return $new;
            }
        }
        // Default case: add char to text
        this.text += cls.char;
        return this;
    }
    push_asterisk(...kwargs) {
        return this.push_patten(MarkdownI);
    }
    push_underscore(...kwargs) {
        return this.push_patten(MarkdownIUnderscore);
    }
    push_tilde(...kwargs) {
        return this.push_patten(MarkdownS, -1);
    }
    push_backtick(...kwargs) {
        return this.push_patten(MarkdownCODE);
    }
    push_dollar(...kwargs) {
        return this.push_patten(MarkdownLatex);
    }

    try_insert_latex(block, ...kwargs) {
        if (this.text.match(/(?<!\\)(\\\\)*\\$/))
            return this.parent.insert_latex(this, block, ...kwargs);
    }
    push_left_bracket(...kwargs) {
        return this.try_insert_latex(["\\[", "\\]"], ...kwargs) || super.push_left_bracket(...kwargs);
    }

    push_left_parenthesis(...kwargs) {
        return this.try_insert_latex(["\\(", "\\)"], ...kwargs) || super.push_left_parenthesis(...kwargs);
    }

    get kwargs_list() {
        return [this.text, this.start_idx];
    }

    colgroup_css() {
        if (/: *$/.test(this.text))
            return /^ *:/.test(this.text) ? 'center' : 'right';
        else
            return /^ *:/.test(this.text) ? 'left' : null;
    }

    isspace() {
        return this.text.isspace();
    }
}

class MarkdownArgs extends Markdown {
    constructor(args, indent, parent) {
        super(indent, parent);
        this.args = args;
        for (var arg of args)
            arg.parent = this;
    }

    get start_idx() {
        return this.args[0].start_idx;
    }
    get end_idx() {
        return this.args.back().end_idx;
    }
    clone() {
        return new this.constructor(this.args.clone(), this.indent, ...this.kwargs_list);
    }

    toJSON() {
        return { [this.func]: this.args.map(arg => arg.toJSON()) };
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (this.indent > indent)
            return this.parent.insert_newline(this, newline_count, indent, next, ...kwargs);
    
        if (this.indent < indent)
            throw new Error(`${get_class(this)}::insert_newline is unexpected for ${get_class(this)}`);

        const {start_idx} = kwargs;
        for (let i of range(newline_count)) {
            caret = new MarkdownCaret(indent, start_idx + i);
            this.push(caret);
        }
        return caret;
    }
    insert_space(caret, ...kwargs) {
        return this.parent.insert_space(this, ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return caret.push_token('*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return caret.push_token('_', ...kwargs);
    }
    insert_right_bracket(caret, ...kwargs) {
        let parent = this.parent;
        while (parent) {
            if (parent instanceof MarkdownBracket) {
                parent.is_closed = true;
                return parent;
            }
            parent = parent.parent;
        }
        return this.insert_token(caret, ']', ...kwargs);
    }

    insert_right_parenthesis(caret, ...kwargs) {
        return this.insert_token(caret, ')', ...kwargs);
    }

    insert_token(caret, word, ...kwargs) {
        return caret.push_token(word, ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        return caret.push_token('|', ...kwargs);
    }

    insert_latex(caret, block, ...kwargs) {
        var $new = new MarkdownCaret(this.indent, ...kwargs);
        var latex = new MarkdownLatex($new, this.indent, block);
        if (caret instanceof MarkdownText) {
            caret.text = caret.text.slice(0, -1);
            if (caret.text) {
                latex = [caret, latex];
                if (!(this instanceof MarkdownSPAN))
                    latex = new MarkdownSPAN(latex, this.indent);
            }
            this.replace(caret, latex);
        }
        else
            throw new Error('undefined insert_latex for', get_class(this), caret);
        return $new;
    }
    insert_h(caret, h_level, ...kwargs) {
        if (this.parent)
            return this.parent.insert_h(this, h_level, ...kwargs);
        throw new Error('insert_h is not defined for', get_class(this), caret);
    }
    insert_blockquote(caret, ...kwargs) {
        caret = new MarkdownCaret(this.indent, ...kwargs);
        this.push(new MarkdownBLOCKQUOTE([caret], this.indent));
        return caret;
    }
    insert_list(cls, caret, m, ...kwargs) {
        var indent = m[1].length;
        var warning = null;
        if (indent == this.indent + 1 && this.indent) {
            warning = `indent adjusted from ${indent} to ${this.indent}`;
            indent = this.indent;
        }
        caret.text = caret.text.slice(0, -m[0].length);
        var $new = new MarkdownCaret(m[0].length + 1, ...kwargs);
        var new_li = new MarkdownLI([$new], indent, m[2]);
        var new_list = new cls([new_li], indent);
        if (caret.text)
            this.push(new_list);
        else
            this.replace(caret, new_list);
        $new.warning = warning;
        return $new;
    }

    insert_ul(caret, m, ...kwargs) {
        return this.insert_list(MarkdownUL, caret, m, ...kwargs);
    }
    
    insert_ol(caret, m, ...kwargs) {
        return this.insert_list(MarkdownOL, caret, m, ...kwargs);
    }

    insert_code(caret, m, indent, ...kwargs) {
        caret.text = caret.text.slice(0, -m[0].length);
        var lang = m[1];
        var $new = indent ? new MarkdownText(' '.repeat(indent), this.indent, ...kwargs) : new MarkdownCaret(this.indent, ...kwargs);
        var new_code = new MarkdownPreCode($new, this.indent, lang);
        if (this instanceof MarkdownSPAN && isinstance(this.parent, [MarkdownLI, MarkdownP, MarkdownDocument]))
            this.parent.push(new_code);
        else
            this.push(new_code);
        if (!caret.text)
            caret.remove();
        return $new;
    }

    insert_hr(caret, m, ...kwargs) {
        caret.text = caret.text.slice(0, -m[0].length);
        var $new = new MarkdownHR(this.indent, caret.end_idx + 1);
        if (caret.text)
            this.push($new);
        else
            this.replace(caret, $new);
        return $new;
    }

    insert_left_bracket(caret, ...kwargs) {
        return caret.push_left_bracket(...kwargs);
    }

    insert_left_parenthesis(caret, ...kwargs) {
        return caret.push_left_parenthesis(...kwargs);
    }

    insert_lt(caret, ...kwargs) {
        const parser = new XMLParser(...kwargs);
        if (caret instanceof MarkdownCaret)
            this.replace(caret, parser);
        else if (this.is_MarkdownSPAN)
            this.push(parser);
        else
            this.replace(caret, new MarkdownSPAN([caret, parser], this.indent));
        parser.parse('<');
        return parser;
    }

    insert_ampersand(caret, ...kwargs) {
        const parser = new XMLParser(...kwargs);
        if (caret instanceof MarkdownCaret)
            this.replace(caret, parser);
        else if (this.is_MarkdownSPAN)
            this.push(parser);
        else
            this.replace(caret, new MarkdownSPAN([caret, parser], this.indent));
        parser.parse('&');
        return parser;
    }

    insert_tilde(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_tilde(...kwargs);
        return this.insert_token(caret, '~', ...kwargs);
    }
    insert_apostrophe(caret, ...kwargs) {
        return this.insert_token(caret, "'", ...kwargs);
    }
    insert_quotation(caret, ...kwargs) {
        return this.insert_token(caret, '"', ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        return this.insert_token(caret, '`', ...kwargs);
    }
    insert_dollar(caret, ...kwargs) {
        return this.insert_token(caret, '$', ...kwargs);
    }
    span(indices) {
        let index = this.args.binary_search(indices, Node.prototype.compareTo.call);
        if (index < this.args.length) {
            const node = this.args[index];
            if (node instanceof MarkdownArgs && node.start_idx < indices.end_idx)
                return node.span(indices);
            return node;
        }
    }

    process_inner_loop(i, ...kwargs) {
        var {args} = this;
        if (args[i].has_newline()) {
            if (args[i] instanceof MarkdownText) {
                var {text} = args[i];
                var index = text.lastIndexOf("\n");
                var former = text.slice(0, index);
                var latter = text.slice(index + 1);
                if (latter.includes('`'))
                    return args.back().push_token('|', ...kwargs);
                args[i].text = former;
            }
            else if (i + 1 < args.length)
                var latter = ' '.repeat(args[i + 1].indent);
            else 
                var latter = '';
            var rest = args.slice(i + 1);
            args.splice(i + 1);
            const m = latter.match(/^( *)(.*)/);
            var indent = m[1].length;
            if (latter = m[2])
                rest.unshift(new MarkdownText(latter, indent, ...kwargs));
            if (rest && rest.length) {
                if (rest.length === 1)
                    rest = rest[0];
                else
                    rest = new MarkdownSPAN(rest, indent);
            } else
                rest = new MarkdownCaret(indent, ...kwargs);
            var caret = new MarkdownCaret(indent, ...kwargs);
            let self = this;
            while (!(
                self instanceof MarkdownP || 
                self instanceof MarkdownLI || 
                self instanceof MarkdownListBase || 
                self instanceof MarkdownTABLE || 
                self instanceof MarkdownDocument || 
                self instanceof MarkdownH
            ))
                self = self.parent;
            self.push(new MarkdownArgsBarSeparated([rest, caret], indent));
            return caret;
        }
    }
}

class MarkdownSPAN extends MarkdownArgs {
    get is_MarkdownSPAN() {
        return true;
    }

    is_indented() {
        return false;
    }

    htmlFormat() {
        return `<span>${this.strFormat()}</span>`;
    }
    strFormat() {
        return '%s'.repeat(this.args.length);
    }

    insert_space(caret, ...kwargs) {
        console.assert(!(caret instanceof MarkdownCaret));
        console.assert(caret === this.args.back());
        if (caret instanceof MarkdownText) {
            const previousElementSibling = caret.previousElementSibling;
            const newline = previousElementSibling?.is_Paragraph ? '^' : '(?<=\\n)';
            var m;
            // Handle headings
            if (m = caret.text.match(new RegExp(newline + MarkdownH.regex_text))) {
                var level = m[1].length;
                caret.text = caret.text.slice(0, -m[0].length);
                if (!caret.text)
                    caret.remove();
                return this.parent.insert_h(this, level, ...kwargs);
            }
            // Handle unordered lists
            if (m = caret.text.match(new RegExp(newline + `( *)([-*])$`)))
                return this.insert_ul(caret, m, ...kwargs);
            // Handle ordered lists
            if (m = caret.text.match(new RegExp(newline + `( *)(\\d+\\.)$`)))
                return this.insert_ol(caret, m, ...kwargs);
            caret.text += ' ';
        }
        else {
            var caret = new MarkdownText(' ', this.indent, ...kwargs);
            this.push(caret);
        }
        return caret;
    }
    insert_asterisk(caret, ...kwargs) {
        if (caret instanceof MarkdownB) {
            var new_i = caret.toMarkdownI();
            if (new_i)
                return new_i;
        }
        else if (caret instanceof MarkdownText) {
            if (this.parent instanceof MarkdownLI) {
                var $new = this.parent.try_indent_li(caret, '*', ...kwargs);
                if ($new)
                    return $new;
            }
            return caret.push_asterisk(...kwargs);
        }
        else if (caret.is_token) {
            if (caret instanceof MarkdownI) {
                var new_b = caret.toMarkdownB();
                if (new_b)
                    return new_b;
            }
            var $new = MarkdownI.try_pattern(caret);
            if ($new)
                return $new
        }
        return this.insert_token(caret, '*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        if (caret instanceof MarkdownB) {
            var new_i = caret.toMarkdownI();
            if (new_i)
                return new_i;
        }
        else if (caret instanceof MarkdownText)
            return caret.push_underscore(...kwargs);
        else if (caret.is_token) {
            if (caret instanceof MarkdownI) {
                var new_b = caret.toMarkdownB();
                if (new_b)
                    return new_b;
            }
            var $new = MarkdownIUnderscore.try_pattern(caret);
            if ($new)
                return $new
        }
        return this.insert_token(caret, '_', ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            const $new = caret.push_backtick(...kwargs);
            if ($new instanceof MarkdownCODE)
                $new.arg = new MarkdownText($new.arg.plainText, $new.indent, $new.arg.start_idx);
            return $new;
        }
        if (caret.is_token) {
            const $new = MarkdownCODE.try_pattern(caret);
            if ($new) {
                $new.arg = new MarkdownText($new.arg.plainText, $new.indent, $new.arg.start_idx);
                return $new;
            }
        }
        return this.insert_token(caret, '`', ...kwargs);
    }
    insert_dollar(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            const $new = caret.push_dollar(...kwargs);
            if ($new instanceof MarkdownLatex)
                $new.arg = new MarkdownText($new.arg.plainText, $new.indent, $new.arg.start_idx);
            return $new;
        }
        if (caret.is_token) {
            const $new = MarkdownLatex.try_pattern(caret);
            if ($new) {
                $new.arg = new MarkdownText($new.arg.plainText, $new.indent, $new.arg.start_idx);
                return $new;
            }
        }
        return this.insert_token(caret, '$', ...kwargs);
    }
    try_pattern(cls, stop) {
        var m;
        var nested_pattern = [];
        for (var i of range(this.args.length - 2, -1, -1)) {
            var node = this.args[i];
            if (node instanceof MarkdownText && (m = node.text.match(cls.regex_span))) {
                node.text = node.text.slice(0, -m[0].length);
                var new_pattern = new cls(
                    new MarkdownSPAN(
                        [
                            new MarkdownText(
                                m[1], 
                                node.indent, 
                                node.start_idx + m.indices[1][0]
                            ), 
                            ...this.args.slice(i + 1, stop? stop : this.args.length)
                        ],
                        node.indent
                    ), 
                    node.indent
                );
                new_pattern.parent = this;
                this.args.splice(i + 1);
                if (node.text)
                    ++i;
                this.args[i] = new_pattern;
                new_pattern.warning = nested_pattern.length ? `nested tag ${cls.name} detected: ${nested_pattern.map(arg => String(arg))}` : null;
                return new_pattern;
            }
            else if (node instanceof cls.base)
                nested_pattern.push(node);
        }
    }

    try_strike() {
        var $new;
        if ($new = this.try_pattern(MarkdownS, -1))
            return $new;
    }

    try_backtick() {
        var $new;
        if ($new = this.try_pattern(MarkdownCODE))
            return $new;
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (this.parent instanceof MarkdownArgsBarSeparated || this.parent instanceof MarkdownH)
            return this.parent.insert_newline(this, newline_count, indent, next, ...kwargs);
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(MarkdownPreCode.code_start_regex))
                return this.insert_code(caret, m, indent, ...kwargs);
            if (m = caret.text.match(MarkdownHR.regex))
                return this.insert_hr(caret, m, ...kwargs);
        }
        if (newline_count == 1)
            return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
        if (this.parent instanceof MarkdownLI) {
            if ("-*".includes(next))
                return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
            const li = this.parent;
            var $new = indent? new MarkdownText(' '.repeat(indent), 0, ...kwargs) : new MarkdownCaret(indent, ...kwargs);
            $new.start_idx += newline_count;
            li.parent.parent.push($new);
            return $new;
        }
        if (this.parent instanceof MarkdownBracket) {
            const bracket = this.parent;
            let self = this;
            const container = bracket.parent;
            self.unshift(new MarkdownText('[', bracket.indent, bracket.start_idx));
            if (self.constructor === container.constructor)
                self = self.args;
            container.replace(bracket, self);
            if (container.parent)
                return container.parent.insert_newline(container, newline_count, indent, next, ...kwargs);
            return container.insert_newline(container.args.back(), newline_count, indent, next, ...kwargs);
        }
        if (newline_count > 1 && indent >= 4 && this.parent instanceof MarkdownDocument && caret.is_token) {
            var $new = new MarkdownText(' '.repeat(indent), this.indent, ...kwargs);
            $new.start_idx += newline_count;
            this.parent.push(new MarkdownPreCode($new, this.indent, null));
        }
        else {
            var $new = new MarkdownP(this.args, this.indent);
            var {parent} = this;
            parent.replace(this, $new);
            indent -= this.indent;
            if (indent > 0) {
                $new = new MarkdownText(' '.repeat(indent), this.indent, ...kwargs);
                $new.start_idx += newline_count;
                parent.push($new);
            }
        }
        return $new;
    }

    insert(caret, $new) {
        console.assert(caret === this.args.back());
        console.assert ($new instanceof MarkdownText);
        console.assert (!(caret instanceof MarkdownText));
        this.push($new);
        return $new;
    }

    append($new) {
        if ($new instanceof MarkdownText) {
            this.push($new);
            return $new;
        }
        return this.parent.append($new);
    }

    insert_list(cls, caret, m, ...kwargs) {
        var indent = m[1].length;
        var warning = null;
        if (indent == this.indent + 1 && this.indent) {
            warning = `indent adjusted from ${indent} to ${this.indent}`;
            indent = this.indent;
        }
        caret.text = caret.text.slice(0, -m[0].length);
        var node = this.parent;
        if (node instanceof MarkdownLI)
            return node.insert_li(indent, m[2], m[0].length + 1, ...kwargs);

        var $new = new MarkdownCaret(indent, ...kwargs);
        var new_li = new MarkdownLI([$new], indent, m[2]);
        var new_list = new cls([new_li], indent);
        if (caret.text)
            this.push(new_list);
        else if (caret.parent === this)
            this.replace(caret, new_list);
        else {
            caret.remove();
            this.push(new_list);
        }
        $new.warning = warning;
        return $new;
    }

    insert_token(caret, word, ...kwargs) {
        if (caret instanceof MarkdownText && this.parent instanceof MarkdownLI) {
            var $new = this.parent.try_indent_li(caret, word, ...kwargs);
            if ($new)
                return $new;
        }
        else if (caret instanceof XMLParser)
            return MarkdownI.push_token(caret, word, ...kwargs);
        return super.insert_token(caret, word, ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        for (var i of range(this.args.length - 1, -1, -1)) {
            var $new = this.process_inner_loop(i, ...kwargs);
            if ($new)
                return $new;
        }
        if (this.parent instanceof MarkdownArgsBarSeparated)
            return this.parent.insert_bar(this, ...kwargs);
        else
            return caret.push_token('|', ...kwargs);
    }

    removeChild(child) {
        super.removeChild(child);
        if (!this.args.length)
            this.remove();
    }
}

class MarkdownUnary extends MarkdownArgs {
    constructor(arg, indent, parent) {
        super([], indent, parent);
        this.arg = arg;
    }

    clone() {
        return new this.constructor(this.arg.clone(), this.indent, ...this.kwargs_list);
    }

    get arg() {
        return this.args[0];
    }

    set arg(arg) {
        this.args[0] = arg;
        arg.parent = this;
    }

    toJSON() {
        return this.arg.toJSON();
    }

    push(arg) {
        throw new Error(`push operation not allowed for ${get_class(this)}`);
    }

    unshift(arg) {
        throw new Error(`unshift operation not allowed for ${get_class(this)}`);
    }

    replace(old, $new) {
        if (Array.isArray($new))
            $new = new MarkdownSPAN($new, this.indent);
        super.replace(old, $new);
    }
}

class MarkdownI extends MarkdownUnary {
    static char = '*';
    static regex_skip = /[ \n\t~\\]$|`/;
    static regex_text = /\*(?![ \n\t])([^*]*)$/d;
    static get regex_span() {
        return this.regex_text;
    }
    get is_token() {
        return true;
    }
    constructor(arg, indent, char='*', parent=null) {
        super(arg, indent, parent);
        this.kwargs.char = char;
    }
    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<i>%s</i>';
    }

    strFormat() {
        var char = this.kwargs.char;
        return `${char}%s${char}`;
    }

    append($new) {
        if (this.parent)
            return this.parent.insert(this, $new);
        throw new Error('append is not defined for', get_class(this), $new);
    }

    push_token(word, ...kwargs) {
        var $new = new MarkdownText(word, this.indent, ...kwargs);
        if (this.parent instanceof MarkdownSPAN || this.parent instanceof MarkdownLI)
            this.parent.push($new);
        else
            this.parent.replace(this, new MarkdownSPAN([this, $new], this.indent));
        return $new;
    }

    toMarkdownB() {
        var caret = this;
        var parent = this.parent;
        var {previousElementSibling} = caret;
        if (previousElementSibling instanceof MarkdownText && previousElementSibling.text.endsWith('*')) {
            previousElementSibling.text = previousElementSibling.text.slice(0, -1);
            var new_b = new MarkdownB(caret.arg instanceof MarkdownB? caret.arg.arg: caret.arg, caret.indent);
            parent.replace(caret, new_b);
            if (!previousElementSibling.text)
                previousElementSibling.remove();
            return new_b;
        }
    }

    insert_asterisk(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_asterisk(...kwargs);
        return this.insert_token(caret, '*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_underscore(...kwargs);
        return this.insert_token(caret, '_', ...kwargs);
    }
    static try_pattern(self, stop) {
        self = self.parent;
        let $new;
        if ($new = self.try_pattern(this, stop))
            return $new;
        // Handle span parent inside italic
        if (self.parent instanceof this) {
            if ($new = self.parent.toMarkdownB())
                return $new;
        }
    }
}

function MarkdownIUnderscore(...args) {
    return new MarkdownI(...args, '_');
}
MarkdownIUnderscore.base = MarkdownI;
MarkdownIUnderscore.char = '_';
MarkdownIUnderscore.regex_skip = MarkdownI.regex_skip;
MarkdownIUnderscore.regex_text = MarkdownIUnderscore.regex_span = /_(?![ \n\t])([^_]*)$/d;
MarkdownIUnderscore.try_pattern = MarkdownI.try_pattern;

class MarkdownB extends MarkdownUnary {
    get is_token() {
        return true;
    }

    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<b>%s</b>';
    }

    strFormat() {
        return '**%s**';
    }

    append($new) {
        if (this.parent)
            return this.parent.insert(this, $new);
        throw new Error('append is not defined for', get_class(this), $new);
    }

    toMarkdownI() {
        var caret = this;
        var parent = this.parent;
        var {previousElementSibling} = caret;
        if (previousElementSibling instanceof MarkdownText && previousElementSibling.text.endsWith('*')) {
            previousElementSibling.text = previousElementSibling.text.slice(0, -1);
            // text both italic and bold
            var new_i = new MarkdownI(caret, caret.indent);
            parent.replace(caret, new_i);
            if (!previousElementSibling.text)
                previousElementSibling.remove();
            return new_i;
        }
    }
}
MarkdownB.prototype.push_token = MarkdownI.prototype.push_token;
MarkdownB.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownB.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;

class MarkdownS extends MarkdownUnary {
    static char = '~';
    static regex_skip = /[^~]$|[ \n\t\\]~$/;
    static regex_text = /~~(?![ \n\t~])([^~]*)~$/d;
    static regex_span = /~~(?![ \n\t~])([^~]*)$/d;
    get is_token() {
        return true;
    }
    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<s>%s</s>';
    }

    strFormat() {
        return '~~%s~~';
    }

    append($new) {
        if (this.parent)
            return this.parent.insert(this, $new);
        throw new Error('append is not defined for', get_class(this), $new);
    }

    static try_pattern(self, stop) {
        if (self.text == '~')
            return self.parent.try_pattern(this, stop);
    }
}
MarkdownS.prototype.push_token = MarkdownI.prototype.push_token;
MarkdownS.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownS.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;

class MarkdownLink extends Closable(MarkdownArgs) {
    get is_token() {
        return true;
    }
    get href() {
        return this.args[1];
    }

    get title() {
        return this.args[2];
    }

    get title_quote() {
        return this.kwargs.title_quote;
    }

    set title_quote(title_quote) {
        this.kwargs.title_quote = title_quote;
    }

    is_indented() {
        return false;
    }

    get html() {
        const [text, href, ...title] = this.args;
        const args = [href, ...title, text];
        return this.htmlFormat().format(...args.map(arg => arg.html));
    }

    strFormat() {
        if (this.args.length === 2)
            return '[%s](%s)';
        const title_quote = this.title_quote[0];
        return `[%s](%s ${title_quote}%s${title_quote})`;
    }

    insert_right_parenthesis(caret, ...kwargs) {
        let paren_count = 0;
        const {href} = this;
        if (href instanceof MarkdownText && caret === href) {
            for (const ch of href.text) {
                if (ch === '(')
                    ++paren_count;
                else if (ch === ')')
                    --paren_count;
            }
        }
        if (paren_count > 0) {
            caret.text += ')';
            return caret;
        }
        this.is_closed = true;
        return this;
    }

    insert_space(caret, ...kwargs) {
        if (caret === this.href)
            return caret.push_token(' ', ...kwargs);
        return super.insert_space(caret, ...kwargs);
    }

    insert_apostrophe(caret, ...kwargs) {
        if (caret === this.href) {
            caret = new MarkdownCaret(this.indent, ...kwargs);
            caret.start_idx++;
            this.title_quote = "'";
            this.push(caret);
            return caret;
        }
        if (caret === this.title) {
            if (this.title_quote === "'") {
                this.title_quote += "'";
                return caret;
            }
        }
        return super.insert_apostrophe(caret, ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        if (caret === this.href) {
            caret = new MarkdownCaret(this.indent, ...kwargs);
            caret.start_idx++;
            this.title_quote = '"';
            this.push(caret);
            return caret;
        }
        if (caret === this.title) {
            if (this.title_quote === '"') {
                this.title_quote += '"';
                return caret;
            }
        }
        return super.insert_quotation(caret, ...kwargs);
    }

    insert_ampersand(caret, ...kwargs) {
        return this.insert_token(caret, '&', ...kwargs);
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        const href = this.href;
        const args = [
            this.args[0],
            new MarkdownText("(", href.start_idx - 1),
            href
        ];
        if (caret === this.title) {
            args.push(
                new MarkdownText(")", href.end_idx),
                caret
            );
        }
        $new = new MarkdownText("\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
        args.push($new);
        this.parent.replace(this, args);
        return $new;
    }
}
MarkdownLink.prototype.push_token = MarkdownI.prototype.push_token;

class MarkdownA extends MarkdownLink {
    get start_idx() {
        return this.args[0].start_idx - 1;
    }
    htmlFormat() {
        if (this.args.length == 2)
            return '<a href="%s">%s</a>';
        var title_quote = this.title_quote[0];
        return `<a href="%s" title=${title_quote}%s${title_quote}>%s</a>`;
    }
}

class MarkdownIMG extends MarkdownLink {
    get start_idx() {
        return this.args[0].start_idx - 2;
    }
    htmlFormat() {
        if (this.args.length == 2)
            return '<img src="%s" alt="%s" />';
        var title_quote = this.title_quote[0];
        return `<img src="%s" alt="%s" title=${title_quote}%s${title_quote} />`;
    }
    strFormat() {
        return '!' + super.strFormat();
    }
    insert_left_bracket(caret, ...kwargs) {
        if (caret === this.href)
            return this.insert_token(caret, '[', ...kwargs);
        return super.insert_left_bracket(caret, ...kwargs);
    }
}

class MarkdownArgsBarSeparated extends MarkdownArgs {
    get is_Paragraph() {
        return true;
    }
    strip_head_tail() {
        let {args} = this;
        if (!args.length)
            return;
        if (args[0].isspace()) {
            args = args.slice(1);
            if (!args)
                return;
        }
        if (args.back().isspace()) {
            args = args.slice(0, -1);
            if (!args.length) 
                return;
        }
        return args;
    }

    is_colgroup_setting() {
        var args = this.strip_head_tail();
        if (args && args.every(cell => cell instanceof MarkdownText && cell.text.fullmatch(/ *:?-+:? */)))
            return args;
    }

    has_newline() {
        return true;
    }
    
    strFormat() {
        var args_placeholders = Array(this.args.length).fill('%s').join('|');
        return `\n${args_placeholders}`;
    }

    insert_space(caret, ...kwargs) {
        if (caret instanceof MarkdownCaret || caret instanceof MarkdownText || caret instanceof XMLParser)
            return caret.push_token(' ', ...kwargs);
        return this.parent.insert_space(caret, ...kwargs);
    }
    
    insert_bar(caret, ...kwargs) {
        caret = new MarkdownCaret(this.indent, ...kwargs);
        this.push(caret);
        return caret;
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        const table_continued = newline_count === 1 && indent >= this.indent && indent < this.indent + 4;
        var caret = indent? new MarkdownText(' '.repeat(indent), indent, ...kwargs) : new MarkdownCaret(indent, ...kwargs);
        caret.start_idx += newline_count;
        var {indent} = this;
        if (this.parent instanceof MarkdownTABLE) {
            const table = this.parent;
            var args = this.strip_head_tail();
            if (args) {
                const new_td = args.map(arg => new MarkdownTD(arg, indent));
                for (var [td, th] of zip(new_td, table.args[0].args))
                    td.textAlign = th.textAlign
                table.replace(this, new MarkdownTR(new_td, indent));
            }
            let parent = table;
            if (!table_continued) {
                while (parent = parent.parent) {
                    if (parent.is_Paragraph || parent instanceof MarkdownLI)
                        break;
                }
            }
            parent.push(caret);
        } else {
            const P = this.parent;
            var previousElementSibling;
            var colgroup;
            var args;
            if (P instanceof MarkdownP && (previousElementSibling = this.previousElementSibling) instanceof MarkdownArgsBarSeparated && (colgroup = this.is_colgroup_setting()) && (args = previousElementSibling.strip_head_tail())) {
                let escape_li = false;
                let li = P.parent;
                if (li instanceof MarkdownLI && li.parent instanceof MarkdownListBase) {
                    const indent_pivot = li.args[0].indent;
                    if (indent < indent_pivot) {
                        if (indent > li.indent)
                            indent = li.indent;
                        P.remove();
                        parent = li.parent.parent;
                        escape_li = true;
                    }
                }
                const new_th = args.map(arg => new MarkdownTH(arg, indent));
                const new_table = new MarkdownTABLE(
                    [
                        new MarkdownTR(new_th, indent),
                        caret
                    ],
                    indent
                );
                if (escape_li)
                    parent.push(new_table);
                else
                    P.parent.replace(P, new_table);
                for ([align, th] in zip(colgroup, new_th))
                    th.textAlign = align.colgroup_css();
            }
            else if (this.parent instanceof MarkdownP)
                this.parent.push(caret);
            else 
                this.parent.replace(this, new MarkdownP([this, caret], indent));
        }
        return caret;
    }
}
MarkdownArgsBarSeparated.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownArgsBarSeparated.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;
MarkdownArgsBarSeparated.prototype.insert_backtick = MarkdownSPAN.prototype.insert_backtick;

class MarkdownPreCode extends Closable(MarkdownUnary) {
    static code_start_regex = /(?<=(?:^|\n) *)```([a-zA-Z:]*\+*\d*)( *)$/;
    get is_Paragraph() {
        return true;
    }
    constructor(caret, indent, lang, parent) {
        super(caret, indent, parent);
        this.lang = lang;
    }

    get kwargs_list() {
        return [this.lang];
    }

    get lang() {
        return this.kwargs.lang;
    }

    set lang(lang) {
        this.kwargs.lang = lang;
    }

    is_indented() {
        return false;
    }

    get html() {
        const args = this.args.map(arg => arg.html.replace(/</g, '&lt;').replace(/>/g, '&gt;'));
        return this.htmlFormat().format(...args);
    }

    htmlFormat() {
        const {lang} = this;
        if (lang == null)
            return `<pre><code>%s</code></pre>`;
        else
            return `<pre class="language-${lang}"><code class="language-${lang}">%s</code></pre>`;
    }
    strFormat() {
        const {lang} = this;
        if (lang == null)
            return `\n%s\n`;
        else
            return `\`\`\`${lang}\n%s\n\`\`\``;
    }
    insert_space(caret, ...kwargs) {
        return caret.push_token(' ', ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return caret.push_token('*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return caret.push_token('_', ...kwargs);
    }
    insert_left_bracket(caret, ...kwargs) {
        return caret.push_token('[', ...kwargs);
    }

    insert_left_parenthesis(caret, ...kwargs) {
        return caret.push_token('(', ...kwargs);
    }

    insert_right_bracket(caret, ...kwargs) {
        return caret.push_token(']', ...kwargs);
    }

    insert_right_parenthesis(caret, ...kwargs) {
        return caret.push_token(')', ...kwargs);
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (this.lang == null) {
                if (indent < 4)
                    this.is_closed = true;
            }
            else if (m = caret.text.match(/\n* *``` *$/)) {
                caret.text = caret.text.slice(0, -m[0].length);
                this.is_closed = true;
            }
        }
        var self = this;
        if (self.is_closed) {
            kwargs.start_idx += newline_count;
            if (!indent) {
                if (self.parent instanceof MarkdownLI) {
                    var li = self.parent;
                    li.replace(self, new MarkdownP([self], self.indent));
                    const caret = new MarkdownCaret(indent, ...kwargs);
                    let hit = false;
                    if (newline_count > 1) {
                        while (li instanceof MarkdownLI && indent <= li.indent) {
                            li = li.parent.parent;
                            hit = true;
                        }
                    }
                    if (hit)
                        li.push(caret);
                    else
                        li.push(new MarkdownP([caret], indent));
                    return caret;
                }
                return self;
            }
            newline_count = 0;
            caret = self;
            self = caret.parent;
        }
        return self.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }

    insert_lt(caret, ...kwargs) {
        return caret.push_token('<', ...kwargs);
    }
    
    insert_ampersand(caret, ...kwargs) {
        return caret.push_token('&', ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        return caret.push_token('|', ...kwargs);
    }

    insert_tilde(caret, ...kwargs) {
        return caret.push_token('~', ...kwargs);
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.insert_token(caret, "'", ...kwargs);
    }
    insert_quotation(caret, ...kwargs) {
        return this.insert_token(caret, '"', ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        return this.insert_token(caret, '`', ...kwargs);
    }
    insert_dollar(caret, ...kwargs) {
        return this.insert_token(caret, '$', ...kwargs);
    }
    push_token(word, ...kwargs) {
        const $new = new MarkdownText(word, this.indent, ...kwargs);
        if (this.parent instanceof MarkdownP || 
            this.parent instanceof MarkdownLI || 
            this.parent instanceof MarkdownH || 
            this.parent instanceof MarkdownDocument) {
            this.parent.push($new);
        } else
            this.parent.replace(this, new MarkdownP([this, $new], this.indent));
        return $new;
    }
}

class MarkdownCODE extends MarkdownUnary {
    static char = '`';
    static regex_skip = /(?<![`\\])`[^`]*\n\n/;
    static regex_text = /(?<![`\\])`([^`]*)$/d;
    static get regex_span() { 
        return this.regex_text; 
    }
    get is_token() { 
        return true;
    }
    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<code>%s</code>';
    }
    
    strFormat() {
        return '`%s`';
    }

    insert_space(caret, ...kwargs) {
        return caret.push_token(' ', ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return caret.push_token('*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return caret.push_token('_', ...kwargs);
    }
    insert_left_bracket(caret, ...kwargs) {
        return caret.push_token('[', ...kwargs);
    }
    insert_left_parenthesis(caret, ...kwargs) {
        return caret.push_token('(', ...kwargs);
    }

    insert_right_bracket(caret, ...kwargs) {
        return caret.push_token(']', ...kwargs);
    }

    insert_right_parenthesis(caret, ...kwargs) {
        return caret.push_token(')', ...kwargs);
    }

    insert_newline(caret, newlineCount, indent, next, ...kwargs) {
        return this.insert_token(caret, '\n'.repeat(newlineCount) + ' '.repeat(indent), ...kwargs);
    }

    insert_lt(caret, ...kwargs) {
        return caret.push_token('<', ...kwargs);
    }

    insert_ampersand(caret, ...kwargs) {
        return caret.push_token('&', ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        return caret.push_token('|', ...kwargs);
    }

    insert_tilde(caret, ...kwargs) {
        return caret.push_token('~', ...kwargs);
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.insert_token(caret, "'", ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        return this.insert_token(caret, '"', ...kwargs);
    }

    insert_backtick(...kwargs) {
        return this;
    }

    static try_pattern(self, stop) {
        return self.parent.try_pattern(this, stop);
    }
}
MarkdownCODE.prototype.push_token = MarkdownI.prototype.push_token;
Object.defineProperty(MarkdownCODE.prototype, 'html', Object.getOwnPropertyDescriptor(MarkdownPreCode.prototype, 'html'));

class MarkdownH extends MarkdownArgs {
    static regex_text = ' {0,3}(#+)$';
    constructor(caret, indent, level, parent) {
        super([caret], indent, parent);
        this.kwargs.level = level;
    }

    get kwargs_list() {
        return [this.level];
    }

    get level() {
        return this.kwargs.level;
    }

    is_indented() {
        return false;
    }

    htmlFormat() {
        var {level} = this;
        var hanging = Array(this.args.length - 1).fill('%s').join("\n");
        return `<h${level}>%s</h${level}>\n` + hanging;
    }

    strFormat() {
        const {level} = this;
        const hanging = Array(this.args.length - 1).fill('%s').join('\n');
        const hash = '#'.repeat(level);
        return `${hash} %s\n${hanging}`;
    }

    get header() {  
        return this.args[0];
    }

    get hanging() {
        return this.args.slice(1);
    }

    insert_right(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(/\(([^)]+)/))
                caret.text = caret.text.slice(0, -m[0].length);
        }
        if (this.parent)
            return this.parent.insert_right(this, caret, ...kwargs);
        throw new Error('insert_right is not defined for', get_class(this), caret);
    }

    insert_space(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (caret !== this.header) {
                if (m = caret.text.match(new RegExp('(?<=^|\\n)' + MarkdownH.regex_text))) {
                    var level = m[1].length;
                    caret.text = caret.text.slice(0, -m[0].length);
                    var $new = this.insert_h(caret, level, ...kwargs);
                    if (!caret.text)
                        caret.remove();
                    return $new;
                }
                if (m = caret.text.match(/(?<=^|\n)( *)([-*])$/))
                    return this.insert_ul(caret, m, ...kwargs);
                if (m = caret.text.match(/(?<=^|\n)( *)(\d+\.)$/))
                    return this.insert_ol(caret, m, ...kwargs);
            }
            caret.text += ' ';
        }
        return caret;
    }
    insert_backtick(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_backtick(...kwargs);
        return this.insert_token(caret, '`', ...kwargs);
    }
    insert_dollar(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_dollar(...kwargs);
        return this.insert_token(caret, '$', ...kwargs);
    }
    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (this.indent > indent)
            return super.insert_newline(caret, newline_count, indent, next, ...kwargs);
        // now that indent ≥ this.indent
        if (caret === this.header) {
            caret = indent ? new MarkdownText(' '.repeat(indent), this.indent, ...kwargs) : new MarkdownCaret(indent, ...kwargs);
            caret.start_idx += newline_count;
            this.push(caret);
            return caret;
        }
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(MarkdownPreCode.code_start_regex))
                return this.insert_code(caret, m, indent, ...kwargs);
            if (m = caret.text.match(MarkdownHR.regex))
                return this.insert_hr(caret, m, ...kwargs);
            if (newline_count == 1)
                return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
        }
        if (caret.is_Paragraph)
            return caret;
        var $new = new MarkdownP(caret instanceof MarkdownSPAN? caret.args : [caret], this.indent);
        this.replace(caret, $new);
        indent -= this.indent;
        if (indent) {
            $new = new MarkdownText(' '.repeat(indent), this.indent, ...kwargs);
            $new.start_idx += newline_count;
            this.push($new);
        }
        return $new;
    }

    insert_token(caret, char, ...kwargs) {
        if (caret instanceof MarkdownText || caret instanceof MarkdownCaret)
            return caret.push_token(char, ...kwargs);
        var text = new MarkdownText(char, this.indent, ...kwargs);
        if (caret.is_Paragraph)
            this.push(text);
        else if (caret instanceof MarkdownSPAN)
            caret.push(text);
        else
            this.replace(caret, new MarkdownSPAN([caret, text], this.indent));
        return text;
    }

    toJSON() {
        var dict = super.toJSON();
        dict['level'] = this.level;
		return dict;
	}

    insert(caret, $new) {
        console.assert(caret === this.args.back());
        if ($new instanceof MarkdownText) {
            if (caret instanceof MarkdownSPAN) {
                caret.push($new);
            }
            else {
                var texts = new MarkdownSPAN([caret, $new], this.indent);
                this.replace(caret, texts);
            }
            return $new;
        }
        else 
            throw new Error("assert failed: insert(caret, \$new) " + get_class(this));
    }

    insert_h(caret, level, ...kwargs) {
        var caret = new MarkdownCaret(this.indent, ...kwargs);
        var new_h = new MarkdownH(caret, this.indent, level);
        if (level > this.level)
            this.push(new_h);
        else {
            var node = this;
            while (node.parent instanceof MarkdownH && level <= node.parent.level)
                node = node.parent;
            node.parent.push(new_h);
        }
        return caret;
    }

    process_inner_loop(i, ...kwargs) {
        if (!i) {
            var {args} = this;
            var rest = args.slice(i + 1);
            args.splice(i + 1);
            const {indent} = this;
            if (rest && rest.length) {
                if (rest.length === 1)
                    rest = rest[0];
                else
                    rest = new MarkdownSPAN(rest, indent);
            } else
                rest = new MarkdownCaret(indent, ...kwargs);
            var caret = new MarkdownCaret(indent, ...kwargs);
            let self = this;
            self.push(new MarkdownArgsBarSeparated([rest, caret], indent));
            return caret;
        }
        else
            return super.process_inner_loop(i, ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        if (caret === this.header)
            return this.insert_token(caret, '|', ...kwargs);
        return MarkdownSPAN.prototype.insert_bar.call(this, caret, ...kwargs);
    }
}
MarkdownH.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownH.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;

class MarkdownPairedGroup extends Closable(MarkdownUnary) {
    is_indented() {
        return false;
    }

    insert(caret, func) {
        if (this.arg === caret) {
            if (caret instanceof MarkdownCaret) {
                this.arg = new func(caret, this.indent);
                return caret;
            }
        }
        throw new Error(`insert is unexpected for ${get_class(this)}`);
    }
}

class MarkdownLatex extends MarkdownUnary {
    static char = '$';
    static regex_skip = /(?<![$\\])\$[^$]*\n/;
    static regex_text = /(?<![$\\])\$([^$]*)$/d;
    static get regex_span() { 
        return this.regex_text; 
    }
    get is_token() {
        return true;
    }
    constructor(caret, indent, block='$$', parent=null) {
        super(caret, indent, parent);
        this.block = block;
    }

    get kwargs_list() {
        return [this.block];
    }

    get block() {
        return this.kwargs.block;
    }

    set block(block) {
        this.kwargs.block = block;
    }

    get is_Paragraph() {
        return ['\\[', '$$'].includes(this.block[0]);
    }
    
    is_indented() {
        return false;
    }
    strFormat() {
        const block = this.block;
        var s = `${block[0]}%s`;
        if (this.is_closed)
            s += block[1];
        return s;
    }

    insert_space(caret, ...kwargs) {
        return caret.push_token(' ', ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return caret.push_token('*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return caret.push_token('_', ...kwargs);
    }
    insert_left_bracket(caret, ...kwargs) {
        return caret.push_token('[', ...kwargs);
    }
    insert_left_parenthesis(caret, ...kwargs) {
        return caret.push_token('(', ...kwargs);
    }
    insert_right_bracket(caret, ...kwargs) {
        if (this.block[1] == "\\]" && caret instanceof MarkdownText && caret.text.match(/(?<!\\)(\\\\)*\\$/)) {
            caret.text = caret.text.slice(0, -1);
            this.is_closed = true;
            return this;
        }
        return caret.push_token(']', ...kwargs);
    }
    insert_right_parenthesis(caret, ...kwargs) {
        if (this.block[1] == "\\)" && caret instanceof MarkdownText && caret.text.match(/(?<!\\)(\\\\)*\\$/)) {
            caret.text = caret.text.slice(0, -1);
            this.is_closed = true;
            return this;
        }
        return caret.push_token(')', ...kwargs);
    }
    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }
    insert_lt(caret, ...kwargs) {
        return caret.push_token('<', ...kwargs);
    }
    insert_ampersand(caret, ...kwargs) {
        return caret.push_token('&', ...kwargs);
    }
    insert_bar(caret, ...kwargs) {
        return caret.push_token('|', ...kwargs);
    }
    insert_tilde(caret, ...kwargs) {
        return caret.push_token('~', ...kwargs);
    }
    insert_quote(caret, quote, ...kwargs) {
        var previousElementSibling;
        if (caret instanceof MarkdownCaret && 
            this.parent instanceof MarkdownSPAN && 
            ((previousElementSibling = this.previousElementSibling) instanceof MarkdownText) &&
            new RegExp(`(?<!\\\\)${quote}[^${quote}]*$`).test(previousElementSibling.text)
        ) {
            previousElementSibling.text += String(this) + quote;
            this.remove();
            return previousElementSibling;
        }
        return this.insert_token(caret, quote, ...kwargs);
    }
    insert_apostrophe(caret, ...kwargs) {
        return this.insert_quote(caret, "'", ...kwargs);
    }
    insert_quotation(caret, ...kwargs) {
        return this.insert_quote(caret, '"', ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        return this.insert_token(caret, '`', ...kwargs);
    }
    insert_dollar(caret, ...kwargs) {
        if (this.block[1] == '$')
            return this;
        return caret.push_token('$', ...kwargs);
    }
}
MarkdownLatex.try_pattern = MarkdownCODE.try_pattern;

class MarkdownLI extends MarkdownArgs {
    constructor(args, indent, text, parent) {
        super(args, indent, parent);
        this.text = text;
    }

    get is_MarkdownLI() {
        return true;
    }

    is_indented() {
        return true;
    }

    get start_idx() {
        return this.args[0].start_idx - this.text.length - 1;
    }

    htmlFormat() {
        return "<li>%s</li>".format(Array(this.args.length).fill('%s').join(""));
    }

    strFormat() {
        return this.text + ' ' + Array(this.args.length).fill('%s').join('');
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(MarkdownPreCode.code_start_regex))
                return this.insert_code(caret, m, indent, ...kwargs);
            if (isinstance(this.parent, MarkdownUL) && (m = caret.text.match(new RegExp(`^(?: *[${this.text}]){2,} *$`)))) {
                const $new = new MarkdownHR(this.indent, this.start_idx);
                if (this.args.length === 1) {
                    this.parent.parent.push($new);
                    this.remove();
                } else
                    this.replace(caret, $new);
                return $new;
            }
            if (m = caret.text.match(MarkdownHR.regex))
                return this.insert_hr(caret, m, ...kwargs);
            if (newline_count > 1 && !next.match(/[-*0-9]/)) {
                caret = indent? new MarkdownText(' '.repeat(indent), 0, ...kwargs) : new MarkdownCaret(indent, ...kwargs);
                caret.start_idx += newline_count;
                var self = this;
                let hit = false;
                while (self instanceof MarkdownLI && indent <= self.indent) {
                    self = self.parent.parent;
                    hit = true;
                }
                if (hit)
                    self.push(caret);
                else
                    self.push(new MarkdownP([caret], indent));
            }
            else
                caret.text += "\n".repeat(newline_count) + ' '.repeat(indent);
        }
        else {
            caret = new MarkdownText("\n".repeat(newline_count) + ' '.repeat(indent), indent, ...kwargs);
            this.push(caret);
        }
        return caret;
    }

    insert_li(indent, text, child_indent, ...kwargs) {
        var $new = new MarkdownCaret(child_indent, ...kwargs);
        var new_li = new MarkdownLI([$new], indent, text);
        const cls = text.endsWith('.')? MarkdownOL: MarkdownUL;
        var warning = null;
        if (indent < this.indent) {
            var node = this;
            let loopBroken = false;
            while (indent < node.indent) {
                node = node.parent.parent;
                if (!(node instanceof MarkdownLI)) {
                    loopBroken = true;
                    break;
                }
            }
            if (!loopBroken) {
                // Normal end of while loop
                if (!isinstance(node.parent, cls)) {
                    node = node.parent;
                    new_li = new cls([new_li], indent);
                }
                else if (indent > node.indent) {
                    warning = `indent adjusted from ${new_li.indent} to ${node.indent}`;
                    new_li.indent = node.indent;
                }
                node.parent.push(new_li);
            }
            else 
                // Handle break in while loop
                node.push(new cls([new_li], indent));
        }
        else if (!isinstance(this.parent, cls)) {
            var self = indent == this.indent? this.parent.parent: this;
            self.push(new cls([new_li], indent));
        }
        else if (indent == this.indent)
            this.parent.push(new_li);
        else if (this.indent && indent < this.indent + 2) {
            warning = `indent adjusted from ${new_li.indent} to ${this.indent}`;
            new_li.indent = this.indent;
            this.parent.push(new_li);
        } else
            this.push(new cls([new_li], indent));
        $new.warning = warning;
        return $new;
    }

    insert_space(caret, ...kwargs) {
        var m;
        if (caret instanceof MarkdownText) {
            var previousElementSibling = caret.previousElementSibling;
            var newline = isinstance(previousElementSibling, [MarkdownPreCode, MarkdownTABLE, MarkdownP, MarkdownH, MarkdownDocument, MarkdownHR, MarkdownBR, MarkdownListBase])? '(?<=^|\\n)' : '\\n';
            if (m = caret.text.match(new RegExp(newline + `( *)([-*])$`))) {
                var indent = m[1].length;
                var warning = null;
                if (indent == this.indent + 1 && this.indent) {
                    warning = `indent adjusted from ${indent} to ${this.indent}`;
                    indent = this.indent;
                }
                caret.text = caret.text.slice(0, -m[0].length);
                let child_indent = m[0].length;
                if (newline !== '\\n')
                    ++child_indent;
                var $new = this.insert_li(indent, m[2], child_indent, ...kwargs);
                $new.warning = warning;
                return $new;
            }
            if (m = caret.text.match(new RegExp(newline + `( *)(\\d+\\.)$`))) {
                caret.text = caret.text.slice(0, -m[0].length);
                var indent = m[1].length;
                let child_indent = m[0].length + 1;
                if (!indent && (newline !== '\\n' && !caret.text.endsWith('\n') || !caret.text)) {
                    indent = caret.indent;
                    child_indent += indent;
                }
                if (this.parent instanceof MarkdownOL && this.indent < indent && indent <= this.indent + 2)
                    indent = this.indent;
                var $new = this.insert_li(indent, m[2], child_indent, ...kwargs);
                if (!caret.text)
                    caret.remove();
                return $new;
            }
            if (caret.indent < 4 && (m = caret.text.match(new RegExp(newline + MarkdownH.regex_text)))) {
                var level = m[1].length;
                caret.text = caret.text.slice(0, -m[0].length);
                return this.insert_h(caret, level, ...kwargs);
            }
            if (m = caret.text.match(new RegExp(newline + MarkdownBLOCKQUOTE.regex_text))) {
                caret.text = caret.text.slice(0, -m[0].length);
                let $new = this.insert_blockquote(caret, ...kwargs);
                if (!caret.text)
                    caret.remove();
                return $new;
            }
        }
        if (caret === this.args[0] && caret instanceof MarkdownCaret) {
            ++caret.indent;
            return caret;
        }
        return caret.push_token(' ', ...kwargs);
    }

    insert_asterisk(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var $new = this.try_indent_li(caret, '*', ...kwargs);
            if ($new)
                return $new;
            return caret.push_asterisk(...kwargs);
        }
        return this.insert_token(caret, '*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            return caret.push_underscore(...kwargs);
        return this.insert_token(caret, '_', ...kwargs);
    }
    try_indent_li(caret, word, ...kwargs) {
        var node = this;
        var {text} = caret;
        var m;
        if (text.match(/\n\n$/)) {
            var ol_match = word.match(/^ *\d+\.?/);
            var ul_match = word.match(/^ *[-*]/);
            var preprocess = _ => word;
            var count = Infinity;
        }
        else if (m = text.match(/\n\n( *)[-*]$/)) {
            if (m[1] && m[1].length >= this.indent)
                return;
            var ol_match = false;
            var ul_match = word.match(/^ +/);
            var preprocess = caret => {
                caret.text = caret.text.slice(0, -m[0].length);
                return m[0] + word;
            };
            var count = Infinity;
        }
        else if (m = text.match(/([\s\S]*)\n( +)$/)) {
            // possibly the beginning of a new list
            if ('-*'.includes(word))
                return;
            else if (this.parent instanceof MarkdownOL) {
                if (new Range(this.indent, this.indent + 4).contains(m[2].length) && word.isdigit())
                    return;
                if (m[2].length >= this.args[0].indent && '-*'.includes(word))
                    return;
            }
            if (!m[1].endsWith('\n') && this.parent instanceof MarkdownListBase) {
                var indent = m[2].length;
                caret.text = text.slice(0, -(indent + 1));
                this.push(new MarkdownBR(indent, caret.end_idx));
                const $new = new MarkdownText(word, indent, ...kwargs);
                this.push($new);
                return $new;
            }
            if (m[2] && m[2].length >= this.indent && m[2].length < this.args[0].indent) {
                var ol_match = false;
                var ul_match = false;
                var preprocess = caret => {
                    caret.text = caret.text.slice(0, -m[2].length);
                    return m[2] + word;
                };
                var count = 1;
            } else
                return;
        }
        else 
            return;
        var i = 0;
        while (node && node.parent) {
            ++i;
            if (i < count && node.parent.parent instanceof MarkdownLI) 
                node = node.parent.parent;
            else {
                if (node.parent instanceof MarkdownOL && !ol_match || node.parent instanceof MarkdownUL && !ul_match) {
                    if (node.parent.parent)
                        return node.parent.parent.insert_token(node.parent, preprocess(caret), ...kwargs);
                    throw new Error('insert_token is not defined for', get_class(this), caret);
                }
                break;
            }
        }
    }

    insert_token(caret, word, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var $new = this.try_indent_li(caret, word, ...kwargs);
            if ($new)
                return $new;
        }
        return super.insert_token(caret, word, ...kwargs);
    }
}
MarkdownLI.prototype.append = MarkdownSPAN.prototype.append;
MarkdownLI.prototype.insert_bar = MarkdownSPAN.prototype.insert_bar;
MarkdownLI.prototype.insert_backtick = MarkdownSPAN.prototype.insert_backtick;
MarkdownLI.prototype.try_pattern = MarkdownSPAN.prototype.try_pattern;

class MarkdownListBase extends MarkdownArgs {
    get is_Paragraph() {
        return true;
    }
    is_indented() {
        return false;
    }

    strFormat() {
        return Array(this.args.length).fill(`${' '.repeat(this.indent)}%s`).join("\n");
    }

    push_token(word, ...kwargs) {
        const $new = new MarkdownText(word, this.indent, ...kwargs);
        if (isinstance(this.parent, [MarkdownLI, MarkdownP, MarkdownH, MarkdownDocument]))
            this.parent.push($new);
        else
            this.parent.replace(this, new MarkdownP([this, $new], this.indent));
        return $new;
    }
}
MarkdownListBase.prototype.removeChild = MarkdownSPAN.prototype.removeChild;

// unordered list
class MarkdownUL extends MarkdownListBase {
    htmlFormat() {
        return "<ul>\n%s\n</ul>".format(Array(this.args.length).fill('%s').join("\n"));
    }
}

// ordered list
class MarkdownOL extends MarkdownListBase {
    constructor(args, indent, parent) {
        super(args, indent, parent);
        const li = args[0];
        var start = null;
        if (li instanceof MarkdownLI) {
            start = parseInt(li.text.slice(0, -1));
            if (start == 1)
                start = null;
        }
        this.start = start;
    }

    get start() {
        return this.kwargs.start;
    }

    set start(start) {
        this.kwargs.start = start;
    }

    htmlFormat() {
        const ol = this.start ? `<ol start=${this.start}>` : '<ol>';
        return `${ol}\n%s\n</ol>`.format(Array(this.args.length).fill('%s').join("\n"));
    }
}

class MarkdownTD extends MarkdownUnary {
    is_indented() {
        return false;
    }

    get textAlign() {
        return this.kwargs.textAlign;
    }

    set textAlign(textAlign) {
        this.kwargs.textAlign = textAlign;
    }

    htmlFormat() {
        var {textAlign} = this;
        if (textAlign)
            return `<td style="text-align: ${textAlign}">%s</td>`;
        return '<td>%s</td>';
    }

    strFormat() {
        return '%s';
    }
}

class MarkdownTH extends MarkdownUnary {
    is_indented() {
        return false;
    }

    get textAlign() {
        return this.kwargs.textAlign;
    }

    set textAlign(textAlign) {
        this.kwargs.textAlign = textAlign;
    }

    htmlFormat() {
        var {textAlign} = this;
        if (textAlign)
            return `<th style="text-align: ${textAlign}">%s</th>`;
        return '<th>%s</th>';
    }

    strFormat() {
        return '%s';
    }
}

class MarkdownTR extends MarkdownArgs {
    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<tr>%s</tr>'.format(Array(this.args.length).fill('%s').join(""));
    }

    strFormat() {
        return Array(this.args.length).fill("%s").join(" | ");
    }
}

class MarkdownTABLE extends MarkdownArgs {
    get is_Paragraph(){
        return true;
    }
    is_indented() {
        return false;
    }

    htmlFormat() {
        return '<table border=1>%s</table>'.format(Array(this.args.length).fill('%s').join("\n"));
    }

    strFormat() {
        let colgroup = [''];
        for (const th of this.args[0].args) {
            switch (th.textAlign) {
                case 'center':
                    colgroup.push(":---:");
                    break;
                case 'left':
                    colgroup.push(":---");
                    break;
                case 'right':
                    colgroup.push("---:");
                    break;
                default:
                    colgroup.push("---");
            }
        }
        colgroup.push('');
        colgroup = colgroup.join(' | ');
        let args = Array(this.args.length).fill("%s");
        args.splice(1, 0, colgroup);
        return args.join('\n');
    }

    insert_space(caret, ...kwargs) {
        if (caret instanceof MarkdownText)
            caret.text += ' ';
        else 
            return caret.push_token(' ', ...kwargs);
        return caret;
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }

    insert_bar(caret, ...kwargs) {
        var {indent} = caret;
        const $new = new MarkdownCaret(indent, ...kwargs);
        this.replace(caret, new MarkdownArgsBarSeparated([caret, $new], indent));
        return $new;
    }
}
MarkdownTABLE.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownTABLE.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;

class MarkdownP extends MarkdownSPAN {
    get is_Paragraph() {
        return true;
    }
    htmlFormat() {
        return '<p>%s</p>'.format(Array(this.args.length).fill('%s').join(""));
    }

    strFormat() {
        return '%s'.repeat(this.args.length) + '\n\n';
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (this.parent instanceof MarkdownArgsBarSeparated)
            return this.parent.insert_newline(this, newline_count, indent, next, ...kwargs);
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(MarkdownPreCode.code_start_regex))
                return this.insert_code(caret, m, indent, ...kwargs);
            if (m = caret.text.match(MarkdownHR.regex))
                return this.insert_hr(caret, m, ...kwargs);
        }
        if (newline_count == 1 || this.parent instanceof MarkdownLI)
            return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
        let $new = indent > 0? new MarkdownText(' '.repeat(indent), indent, ...kwargs) : new MarkdownCaret(indent, ...kwargs);
        $new.start_idx += newline_count;
        this.parent.push($new);
        return $new;
    }

    insert_list(cls, caret, m, ...kwargs) {
        if (this.parent instanceof MarkdownSPAN)
            return this.parent.insert_list(cls, caret, m, ...kwargs);
        return super.insert_list(cls, caret, m, ...kwargs);
    }
}

class MarkdownBracket extends MarkdownPairedGroup {
    get is_token() {
        return true;
    }
    get start_idx() {
        return this.arg.start_idx - 1;
    }
    strFormat() {
        if (this.is_closed)
            return '[%s]';
        return '[%s';
    }

    push_left_bracket(...kwargs) {
        var indent = this.indent;
        var caret = new MarkdownCaret(indent, ...kwargs);
        caret.start_idx++;
        var $new = new MarkdownBracket(caret, indent);
        if (this.parent instanceof MarkdownSPAN)
            this.parent.push($new);
        else
            this.parent.replace(this, new MarkdownSPAN([this, $new], indent));
        return caret;
    }

    push_left_parenthesis(...kwargs) {
        var indent = this.indent;
        var caret = new MarkdownCaret(indent, ...kwargs);
        caret.start_idx++;
        var textNode, cls;
        if (isinstance(textNode = this.previousElementSibling, MarkdownText) && textNode.text.endsWith('!')) {
            textNode.text = textNode.text.slice(0, -1);
            cls = MarkdownIMG;
        }
        else
            cls = MarkdownA;
        var $new = new cls([this.arg, caret], indent);
        this.parent.replace(this, $new);
        return caret;
    }

    insert_left_bracket(caret, ...kwargs) {
        var warning = `nested brackets detected ${caret}`;
        var $new = super.insert_left_bracket(caret, ...kwargs);
        $new.warning = warning;
        return $new;
    }

    insert_space(caret, ...kwargs) {
        return this.insert_token(caret, ' ', ...kwargs);
    }

    insert_right_bracket(caret, ...kwargs) {
        if (caret instanceof MarkdownText && this.parent instanceof MarkdownLI && this.previousElementSibling == null) {
            var checked = null;
            switch (caret.text) {
            case ' ':
                checked = false;
                break;
            case '*':
                checked = true;
                break;
            }
            if (checked !== null) {
                var checkbox = new MarkdownCheckbox(this.indent, checked, this.start_idx);
                this.parent.replace(this, checkbox);
                return checkbox
            }
        }
        if (caret instanceof MarkdownCaret) {
            const $new = new MarkdownText("[]", this.indent, this.start_idx);
            this.parent.replace(this, $new);
            return $new;
        }
        this.is_closed = true;
        return this;
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        console.assert(caret === this.arg);
        const $new = new MarkdownText('[', this.indent, this.start_idx);
        caret = new MarkdownSPAN(
            caret instanceof MarkdownSPAN?
                [$new, ...caret.args]:
                [$new, caret],
            this.indent
        );
        var {parent} = this;
        if (parent instanceof MarkdownSPAN) {
            parent.replace(this, caret.args);
            caret = caret.args.back();
        } else
            parent.replace(this, caret);
        return parent.insert_newline(caret, newline_count, indent, next, ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        if (caret instanceof MarkdownCaret) {
            const $new = this.push_backtick(...kwargs);
            if ($new instanceof MarkdownCODE) {
                var {arg : {plainText, start_idx}, indent} = $new;
                $new.arg = new MarkdownText(plainText, indent, start_idx);
                return $new;
            }
        }
        return MarkdownH.prototype.insert_backtick.call(this, caret, ...kwargs);
    }
    push_backtick(...kwargs) {
        return this.push_patten(MarkdownCODE);
    }
    push_patten(cls, stop = null) {
        if (this.parent instanceof MarkdownSPAN || this.parent instanceof MarkdownLI) {
            const $new = cls.try_pattern(this, stop);
            if ($new)
                return $new;
        }
    }
}
MarkdownBracket.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownBracket.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;
MarkdownBracket.prototype.push_token = MarkdownI.prototype.push_token;

// https://spec.commonmark.org/0.31.2/#thematic-break
class MarkdownHR extends Markdown {
    constructor(indent, start_idx, parent) {
        super(indent, parent);
        this.start_idx = start_idx;
    }
    get is_Paragraph() {
        return true;
    }
    static regex = /(?:^|\n) {0,3}([-*_])(?: *\1){2,} *$/;
    get end_idx() {
        return this.start_idx + this.indent + 3;
    }
    get text() {
        return '---';
    }
    htmlFormat() {
        return '<hr>';
    }

    strFormat() {
        return this.text + '\n';
    }

    insert_space(caret, ...kwargs) {
        return this.insert_token(caret, ' ', ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return this.insert_token(caret, '*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return this.insert_token(caret, '_', ...kwargs);
    }
}

class MarkdownBR extends Markdown {
    constructor(indent, start_idx, parent) {
        super(indent, parent);
        this.start_idx = start_idx;
    }
    get end_idx() {
        return this.start_idx + this.indent + 1;
    }
    get text() {
        return '\n';
    }
    htmlFormat() {
        return '<br>';
    }

    strFormat() {
        return '\n\n';
    }

    insert_space(caret, ...kwargs) {
        return this.insert_token(caret, ' ', ...kwargs);
    }
    insert_asterisk(caret, ...kwargs) {
        return this.insert_token(caret, '*', ...kwargs);
    }
    insert_underscore(caret, ...kwargs) {
        return this.insert_token(caret, '_', ...kwargs);
    }
}

class MarkdownCheckbox extends Markdown {
    constructor(indent, checked, start_idx, parent) {
        super(indent, parent);
        this.checked = checked;
        this.start_idx = start_idx;
    }
    get text() {
        const x = this.checked ? 'x' : ' ';
        return `[${x}]`;
    }
    get kwargs_list() {
        return [this.checked];
    }

    get checked() {
        return this.kwargs.checked;
    }

    set checked(checked) {
        this.kwargs.checked = checked;
    }

    htmlFormat() {
        var checked = this.checked? ' checked' : '';
        return `<input type="checkbox" disabled${checked}>`;
    }

    strFormat() {
        return this.text;
    }
}

class MarkdownBLOCKQUOTE extends MarkdownSPAN {
    static regex_text = ' *>$';

    get start_idx() {
        return this.args[0].start_idx - 2;
    }

    is_indented() {
        return false;
    }

    htmlFormat() {
        return `<blockquote>${super.strFormat()}</blockquote>`;
    }
    strFormat() {
        return '> ' + '%s'.repeat(this.args.length);
    }
}

class MarkdownDocument extends MarkdownArgs {
    get is_Paragraph() {
        return true;
    }
    get is_MarkdownDocument() {
        return true;
    }

    is_indented() {
        return false;
    }

    strFormat() {
        return Array(this.args.length).fill('%s').join("\n");
    }

    insert_space(caret, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(new RegExp('(?<=^|\\n)' + MarkdownH.regex_text))) {
                var level = m[1].length;
                caret.text = caret.text.slice(0, -m[0].length);
                var $new = this.insert_h(caret, level, ...kwargs);
                if (!caret.text)
                    caret.remove();
                return $new;
            }
            if (m = caret.text.match(/(?<=^|\n)( *)([-*])$/))
                return this.insert_ul(caret, m, ...kwargs);
            if (m = caret.text.match(/(?<=^|\n)( *)(\d+\.)$/))
                return this.insert_ol(caret, m, ...kwargs);
            caret.text += ' ';
        }
        else {
            let $new = new MarkdownText(' ', this.indent, ...kwargs);
            if (caret instanceof MarkdownCaret)
                this.replace(caret, $new);
            else
                this.replace(caret, new MarkdownSPAN([caret, $new], caret.indent));
            return $new;
        }
        return caret;
    }

    get root() {
        return this;
    }

    insert_newline(caret, newline_count, indent, next, ...kwargs) {
        if (caret instanceof MarkdownText) {
            var m;
            if (m = caret.text.match(MarkdownPreCode.code_start_regex))
                return this.insert_code(caret, m, indent, ...kwargs);
            if (m = caret.text.match(MarkdownHR.regex))
                return this.insert_hr(caret, m, ...kwargs);
        }
        if (newline_count > 1) {
            if (caret.is_token) {
                if (indent >= 4) {
                    const caret = new MarkdownText(' '.repeat(indent), this.indent, ...kwargs);
                    caret.start_idx += newline_count;
                    this.push(new MarkdownPreCode(caret, this.indent, null));
                    return caret;
                }
                this.replace(caret, new MarkdownP([caret], caret.indent));
            } 
            caret = new MarkdownText("\n".repeat(newline_count - 1) + ' '.repeat(indent), this.indent, ...kwargs);
            caret.start_idx++;
            this.push(caret);
            return caret;
        }
        return this.insert_token(caret, "\n".repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }

    insert_h(caret, level, ...kwargs) {
        caret = new MarkdownCaret(this.indent, ...kwargs);
        this.push(new MarkdownH(caret, this.indent, level));
        return caret;
    }

    insert_token(caret, char, ...kwargs) {
        var {is_token} = caret;
        if (!is_token && !caret.is_Paragraph || caret instanceof MarkdownText)
            return super.insert_token(caret, char, ...kwargs);
        var $new = new MarkdownText(char, this.indent, ...kwargs);
        if (is_token)
            this.replace(caret, new MarkdownSPAN([caret, $new], this.indent));
        else
            this.push($new);
        return $new;
    }

    append($new) {
        this.push($new);
        return $new;
    }

    get bind() {
        if (!this._bind)
            this._bind = super.bind;
        var bind = this._bind;
        const xml = this.args[0];
        var className = null;
        if (xml instanceof XMLParser) {
            const tagBegin = xml.root.args[0];
            if (tagBegin.is_XMLTagBegin && tagBegin.tagName.text == 'think')
                className = 'think';
        }
        bind.kwargs.class = className;
        console.log('bind.kwargs.class = ', bind.kwargs.class);
        return bind;
    }

    insert_bar(caret, ...kwargs) {
        for (var i of range(this.args.length - 1, -1, -1)) {
            var $new = this.process_inner_loop(i, ...kwargs);
            if ($new)
                return $new;
        }
        var $new = new MarkdownCaret(caret.indent, ...kwargs);
        this.push(new MarkdownArgsBarSeparated([caret, $new], caret.indent));
        return $new;
    }
}
MarkdownDocument.prototype.insert_asterisk = MarkdownI.prototype.insert_asterisk;
MarkdownDocument.prototype.insert_underscore = MarkdownI.prototype.insert_underscore;
MarkdownDocument.prototype.insert_backtick = MarkdownH.prototype.insert_backtick;
MarkdownDocument.prototype.insert_dollar = MarkdownH.prototype.insert_dollar;
Markdown.MarkdownCODE = MarkdownCODE;
Markdown.MarkdownText = MarkdownText;
Markdown.MarkdownBracket = MarkdownBracket;

export default class MarkdownParser extends AbstractParser {
    constructor() {
        super(new MarkdownCaret(0, 0));
        this.root = new MarkdownDocument([this.caret], 0);
    }

    toString() {
        return String(this.root);
    }

    get html() {
        return this.root.html;
    }

    build(text) {
        for (var [start_idx, token] of enumerate(text))
            // [...text].slice(0, start_idx).join('').endsWith("**已验证解决方案**：\n     -")
            // use [...text][start_idx] instead of text[start_idx] because of non-BMP surrogate pairs issues
            this.parse(token, start_idx);
        var start_idx = text.length;
        this.parse("\n", start_idx);
        this.parse("", start_idx + 1);
        return this.root;
    }

    static components = [
        'MarkdownA',
        'MarkdownB',
        'MarkdownI',
        'MarkdownH',
        'MarkdownP',
        'MarkdownS',
        'MarkdownUL',
        'MarkdownOL',
        'MarkdownLI',
        'MarkdownTR',
        'MarkdownTH',
        'MarkdownTD',
        'MarkdownHR',
        'MarkdownBR',
        'MarkdownIMG',
        'MarkdownCODE',
        'MarkdownSPAN',
        'MarkdownTABLE',
        'MarkdownText', 
        'MarkdownPreCode',
        'MarkdownLatex',
        'MarkdownBLOCKQUOTE',
        'xml', 
        'MarkdownCheckbox',
        'MarkdownBracket',
        'MarkdownArgsBarSeparated',
    ];

    get is_MarkdownCaret() {
        var {args} = this.root;
        if (args.length == 1)
            return isinstance(args[0], MarkdownCaret);
    }

    get is_MarkdownText() {
        var {caret} = this;
        return isinstance(caret, MarkdownText);
    }
}

console.log('import markdown.js');
