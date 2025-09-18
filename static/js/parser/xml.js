import { IndentedNode, Closable, AbstractParser } from "./node.js"
import NewLineParser from "./newline.js";

class XML extends IndentedNode {
    get zeros() {
		return [];
	}

	get style() {
		return {};
	}

	push_special(token, ...kwargs) {
		const $new = new XMLText(String(this) + token, 0, this.start_idx);
		this.parent.replace(this, $new);
		return $new;
	}

    modify_style(tag) {
		if (this.text) {
			var set = new Range(0, this.text.length);
	        var _style = this.style;
	        if (tag in _style)
	            _style[tag] = _style[tag].union_without_merging(set);
	        else
	            _style[tag] = set;
		}
    }

    get length() {
		return this.end_idx - this.start_idx;
	}

	sanctity_check() {
	}

	interval(className){
		var {text} = this;
		if (text) {
			var zeros = this.zeros;
			if (!zeros.length || zeros[0])
				zeros.unshift(0);

			if (!zeros.length || zeros.back() < text.length)
				zeros.push(text.length);

			return ranged(1, zeros.length).map(i => {
				return {offsetStart: zeros[i - 1], offsetStop: zeros[i], className};
			});
		}
		else
			return [];
	}

	getLogicalIndices(segments) {
		var logicalOffset = [];
		var start_idx = 0;
		var logicalText = this.text;
		var totalLength = logicalText.length;
		for (var [index, seg] of enumerate(segments)) {
			while (logicalText[start_idx] && logicalText[start_idx].isspace())
				++start_idx;

			if (!logicalText.startsWith(seg, start_idx)) {
				var sCumulated = '';
				var hit = false;

				for (var i of range(start_idx, totalLength)) {
					if (!logicalText[i])
					    continue;

					if (logicalText[i].isspace())
						continue;

					sCumulated += logicalText[i];
					if (sCumulated == seg) {
						hit = true;
						break;
					}
				}

				if (hit)
					seg = logicalText.slice(start_idx, i + 1);
				else {
					console.log("richText.text.slice(start_idx).startsWith(seg)");
					console.log(segments);
					console.log(this.text);
					segments.delete(index, segments.length - index);
					break;
				}

			}

			var end = start_idx + seg.length;

			logicalOffset.push({start_idx, end});
			start_idx = end;
		}

		return logicalOffset;
	}

	parse(token, ...kwargs) {
		switch (token) {
			case ' ':
				return this.parent.insert_space(this, ...kwargs);
			case '\n':
				return new NewLineParser(this, null, ...kwargs);
			case '<':
				return this.parent.insert_lt(this, ...kwargs);
			case '>':
				return this.parent.insert_gt(this, ...kwargs);
			case '"':
				return this.parent.insert_quotation(this, ...kwargs);
			case "'":
				return this.parent.insert_apostrophe(this, ...kwargs);
			case '/':
				return this.parent.insert_solidus(this, ...kwargs);
			case '=':
				return this.parent.insert_eq(this, ...kwargs);
			case '!':
				return this.parent.insert_exclamation(this, ...kwargs);
			case '&':
				return this.parent.insert_ampersand(this, ...kwargs);
			case ';':
				return this.parent.insert_semicolon(this, ...kwargs);
			case '`':
				return this.parent.insert_backtick(this, ...kwargs);
			case ']':
				return this.parent.insert_right_bracket(this, ...kwargs);
			case '\t':
				return this.parent.insert_token(this, '    ', ...kwargs);
			default:
				return this.parent.insert_token(this, token, ...kwargs);
		}
	}

	has_newline() {
		return false;
	}

    get html() {
        return String(this);
    }
}

class XMLCaret extends XML {
    constructor(indent = 0, start_idx = null, parent = null, ...kwargs) {
        console.assert(Number.isInteger(indent) && (start_idx === null || Number.isInteger(start_idx)));
        super(indent, parent, ...kwargs);
        this.start_idx = start_idx;
    }

    get end_idx() {
        return this.start_idx;
    }

	strFormat() {
	  	return '';
	}

	append(newElement) {
		this.parent.replace(this, newElement);
		return newElement;
	}
  
	push_token(word, ...kwargs) {
		const $new = new XMLText(word, 0, ...kwargs);
		this.parent.replace(this, $new);
		return $new;
	}

	get text() {
	  	return '';
	}
  
	get physicalText() {
	  	return "";
	}
  
	get logicalLength() {
	  	return 0;
	}
  
	get texts() {
	  	return [];
	}
  
	*enumerate() {
	  // Empty generator
	}
  
	has(cls) {
	  	return this instanceof cls;
	}
  
	get length() {
	  	return 0;
	}
}

class XMLText extends XML {
	get is_XMLText(){
		return true;
	}

	constructor(text, indent = 0, start_idx=null, parent = null, ...kwargs) {
        console.assert (typeof text === 'string' && Number.isInteger(indent) && Number.isInteger(start_idx));
		super(indent, parent, ...kwargs);
		this.text = text;
        this.start_idx = start_idx;
	}

    append($new) {
        if (this.parent)
            return this.parent.insert(this, $new);
        console.log('append is not defined for', get_class(this), $new);
        return this;
    }

	push_token(word, ...kwargs) {
        this.text += word;
        return this;
    }

	strFormat() {
        return this.text;
    }

    get kwargs_list() {
        return [this.text];
    }

	get plainText() {
		return this.arg.plainText;
	}

	get logicalLength() {
		return this.arg.length;
	}

	get texts() {
		return [this.text];
	}

    logical2physical(pos) {
		return pos;
	}

    physical2logical(pos) {
		return pos;
	}

    getPhysicalIndices(start_idx, end_idx) {
		return [start_idx, end_idx];
    }
}

class XMLArgs extends XML {
    get is_XMLArgs() {
		return true;
	}

    constructor(args, indent = 0, parent = null) {
        super(indent, parent);
        this.args = args;
        for (const arg of args)
            arg.parent = this;
    }

    clone() {
        return new this.constructor(this.args.clone(), this.indent, ...this.kwargs_list);
    }

	strFormat() {
        return '%s'.repeat(this.args.length);
    }

	insert_lt(caret, ...kwargs) {
		if (caret instanceof XMLCaret) {
            caret.start_idx++;
            this.replace(caret, new XMLTagBegin(caret));
        }
		else {
			caret = new XMLCaret(...kwargs);
            caret.start_idx++;
			this.push(new XMLTagBegin(caret));
		}
		return caret;
	}

	insert_gt(caret, ...kwargs) {
		return this.parent.insert_gt(this, ...kwargs);
	}

	insert_ampersand(caret, ...kwargs) {
		if (caret instanceof XMLCaret) {
            caret.start_idx++;
			this.replace(caret, new XMLEntity(caret));
			return caret;
		} else {
			const $new = new XMLCaret(...kwargs);
            $new.start_idx++;
			this.replace(caret, new XMLArgsNullSeparated([caret, new XMLEntity($new)]));
			return $new;
		}
	}

	insert_newline(caret, newline_count, indent, ...kwargs) {
		return this.insert_token(caret, '\n'.repeat(newline_count) + ' '.repeat(indent), ...kwargs);
	}

	insert_semicolon(caret, ...kwargs) {
		return this.insert_token(caret, ';', ...kwargs);
	}

	insert_space(caret, ...kwargs) {
		return this.insert_token(caret, ' ', ...kwargs);
	}

	insert_backtick(caret, ...kwargs) {
		return this.insert_token(caret, '`', ...kwargs);
	}

	insert_right_bracket(caret, ...kwargs) {
		return this.insert_token(caret, ']', ...kwargs);
	}

    insert_apostrophe(caret, ...kwargs) {
        return this.insert_token(caret, "'", ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        return this.insert_token(caret, '"', ...kwargs);
    }

    insert_solidus(caret, ...kwargs) {
        return this.insert_token(caret, '/', ...kwargs);
    }

    insert_eq(caret, ...kwargs) {
        return this.insert_token(caret, '=', ...kwargs);
    }

    insert_exclamation(caret, ...kwargs) {
        return this.insert_token(caret, '!', ...kwargs);
    }

	push_token(token, ...kwargs) {
		const $new = new XMLText(token, 0, ...kwargs);
		this.parent.push($new);
		return $new;
	}

	insert_token(caret, token, ...kwargs) {
		return caret.push_token(token, ...kwargs);
	}

	has_newline() {
		return this.args.some(arg => arg.has_newline());
	}

    get start_idx() {
        return this.args[0].start_idx;
    }

    get end_idx() {
        return this.args.back().end_idx;
    }
}

class XMLArgsNullSeparated extends XMLArgs {
    insert_ampersand(caret, ...kwargs) {
        if (caret instanceof XMLCaret) {
            caret.start_idx++;
            this.replace(caret, new XMLEntity(caret));
            return caret;
        }
        const $new = new XMLCaret(...kwargs);
        $new.start_idx++;
        this.push(new XMLEntity($new));
        return $new;
    }

    insert_token(caret, token, ...kwargs) {
        if (caret instanceof XMLCaret || caret instanceof XMLText)
            return super.insert_token(caret, token, ...kwargs);
        caret = new XMLText(token, 0, ...kwargs);
        this.push(caret);
        return caret;
    }

    get html() {
        return this.args.map(arg => arg.html).join('');
    }
}

class XMLTagBase extends XMLArgs {
    get start_idx() {
        return this.tagName.start_idx - 1;
    }
    
    set start_idx(start_idx) {
        this.tagName.start_idx = start_idx + 1;
    }
    
    get end_idx() {
        return super.end_idx + 1;
    }

    get tagName() {
        return this.args[0];
    }

    get attributes() {
        return this.args.slice(1);
    }

    insert_space(caret, ...kwargs) {
        if (caret === this.tagName && caret instanceof XMLCaret)
            return this.push_special(' ', ...kwargs);
        const $new = new XMLCaret(...kwargs);
        this.push($new);
        return $new;
    }

    insert_token(caret, token, ...kwargs) {
        if (
            (caret instanceof XMLCaret && (/\d/.test(token) || "`~@#$%^&()_=+[{]}\\|,./?-".includes(token))) ||
            (caret instanceof XMLText && "`~@#$%^&()=+[{]}\\|,/?".includes(token)) ||
            (caret instanceof XMLEq)
        )
            return this.push_special(token, ...kwargs);
        return caret.push_token(token, ...kwargs);
    }

    insert_eq(caret, ...kwargs) {
        if (caret === this.tagName && caret instanceof XMLCaret)
            return this.push_special('=', ...kwargs);
        const $new = new XMLCaret(...kwargs);
        $new.start_idx++;
        this.replace(caret, new XMLEq(caret, $new));
        return $new;
    }

    insert_lt(caret, ...kwargs) {
        if (caret instanceof XMLCaret && caret === this.tagName) {
            const text = this.toString();
            const prev = this.previousElementSibling;
            if (prev && prev instanceof XMLText) {
                prev.text += text;
            } else {
                this.parent.replace(this, [new XMLText(text, 0, this.start_idx), this]);
                this.start_idx = kwargs.start_idx;
            }
            return caret;
        }
        return super.insert_lt(caret, ...kwargs);
    }

    insert_gt(caret, ...kwargs) {
        this.is_closed = true;
        return this;
    }

    insert_exclamation(caret, ...kwargs) {
        if (caret === this.tagName && caret instanceof XMLCaret)
            return this.insert_token(caret, '!', ...kwargs);
        return this.push_special('!', ...kwargs);
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.push_special("'", ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        return this.push_special('"', ...kwargs);
    }
}

class XMLTagBegin extends Closable(XMLTagBase) {
    get is_XMLTagBegin() {
		return true;
	}

    constructor(arg, indent = 0, parent = null, kwargs = {}) {
        super([arg], indent, parent, kwargs);
    }

    toString() {
        let s = `<${this.tagName}`;
        const attributes = Array.from(this.attributes).map(attr => attr.toString()).join(' ');
        if (attributes) {
            s += ' ' + attributes;
        }
        if (this.is_closed) {
            s += '>';
        }
        return s;
    }

    insert_solidus(caret, ...kwargs) {
        if (caret === this.tagName) {
            if (caret instanceof XMLCaret) {
                caret.start_idx++;
                this.parent.replace(this, new XMLTagEnd(caret));
                return caret;
            }
            return this.push_special('/', ...kwargs);
        }
        this.parent.replace(this, new XMLTagVoid(this.args));
        return caret;
    }
}

class XMLTagVoid extends Closable(XMLTagBase) {
    get is_XMLTagVoid() {
		return true;
	}

    toString() {
        let s = `<${this.tagName}`;
        const attributes = this.attributes.map(attr => attr.toString()).join(' ');
        if (attributes) {
            s += ` ${attributes}`;
        }
        s += ' /';
        if (this.is_closed) {
            s += '>';
        }
        return s;
    }

    insert_solidus(caret, ...kwargs) {
        return this.push_special('/', ...kwargs);
    }
}

class XMLUnary extends XMLArgs {
    constructor(arg, indent = 0, parent = null) {
        super([], indent, parent);
        this.arg = arg; // Uses the arg setter
    }

    clone() {
        return new this.constructor(this.arg.clone(), this.indent, ...this.kwargs_list);
    }

    get arg() {
        return this.args[0];
    }

    set arg(argVal) {
        if (this.args.length === 0)
            this.args.push(null);
        this.args[0] = argVal;
        argVal.parent = this;
    }

    toJSON() {
        return this.arg.toJSON();
    }

    push(arg) {
        throw new Error(`push operation not allowed for ${this.constructor.name}`);
    }

    unshift(arg) {
        throw new Error(`unshift operation not allowed for ${this.constructor.name}`);
    }

    strFormat() {
        return '%s';
    }

    insert_token(caret, token, ...kwargs) {
        return caret.push_token(token, ...kwargs);
    }

    replace(old, $new) {
        if (Array.isArray($new))
            $new = new XMLArgsNullSeparated($new);
        super.replace(old, $new);
    }
}

class XMLPairedGroup extends Closable(XMLUnary) {
	insert_space(caret, ...kwargs) {
	  return this.insert_token(caret, ' ', ...kwargs);
	}
  
	insert_solidus(caret, ...kwargs) {
	  return this.insert_token(caret, '/', ...kwargs);
	}
  
	insert_eq(caret, ...kwargs) {
	  return this.insert_token(caret, '=', ...kwargs);
	}
  
	insert_exclamation(caret, ...kwargs) {
	  return this.insert_token(caret, '!', ...kwargs);
	}
  
	insert_lt(caret, ...kwargs) {
	  return this.insert_token(caret, '<', ...kwargs);
	}
  
	insert_gt(caret, ...kwargs) {
	  return this.insert_token(caret, '>', ...kwargs);
	}
  
	insert_ampersand(caret, ...kwargs) {
	  return this.insert_token(caret, '&', ...kwargs);
	}
  
	insert_semicolon(caret, ...kwargs) {
	  return this.insert_token(caret, ';', ...kwargs);
	}
  
	insert_backtick(caret, ...kwargs) {
	  return this.insert_token(caret, '`', ...kwargs);
	}
}

class XMLApostrophe extends XMLPairedGroup {
    strFormat() {
        let s = "'%s";
        if (this.is_closed)
            s += "'";
        return s;
    }

    insert_apostrophe(caret, ...kwargs) {
        this.is_closed = true;
        return this;
    }

    insert_quotation(caret, ...kwargs) {
        return this.insert_token(caret, '"', ...kwargs);
    }
}

class XMLQuotation extends XMLPairedGroup {
    strFormat() {
        let s = '"%s';
        if (this.is_closed)
            s += '"';
        return s;
    }

    insert_quotation(caret, ...kwargs) {
        this.is_closed = true;
        return this;
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.insert_token(caret, "'", ...kwargs);
    }
}

class XMLTagEnd extends Closable(XMLUnary) {
	get is_XMLTagEnd() {
		return true;
	}

    get tagName() {
        return this.arg;
    }

    toString() {
        let s = `</${this.tagName}`;
        if (this.is_closed)
            s += '>';
        return s;
    }

    insert_gt(caret, ...kwargs) {
        this.is_closed = true;
        if (!(this.parent instanceof XMLUnary)) {
            var tagName = this.tagName.text.toLowerCase();
            var args = this.parent.args;
            if (args.length == 1) {
                var parent;
                if ((parent = this.parent) instanceof XMLDocument && (parent = parent.parent) instanceof XMLParser && (parent = parent.parent) && parent.is_MarkdownSPAN) {
                    var tagBegin = this.parent.parent.search_tagBegin(arg => XMLParser.match_XMLTagBegin(arg, tagName), XMLContainerTag);
                    if (tagBegin) {
                        let containerTag = tagBegin.parent;
                        let document = containerTag.parent;
                        containerTag.setitem(0, containerTag.tagBegin.root.args[0]);
                        containerTag.setitem(containerTag.length - 1, containerTag.tagEnd.root.args[0]);
                        console.assert(containerTag.args.all(arg => arg.parent === containerTag));
                        tagBegin.root.setitem(0, containerTag);
                        console.assert(document.args.back() === containerTag);
                        document.setitem(document.args.length - 1, tagBegin);
                        tagBegin.caret = tagBegin.root.args[0];
                        console.assert(document.args.all(arg => arg.parent === document));
                        return tagBegin;
                    }
                }
            }
            else {
                for (let i = args.length - 2; i >= 0; i--) {
                    if (args[i] instanceof XMLTagBegin && args[i].tagName.text.toLowerCase() === tagName) {
                        const tag = new XMLContainerTag(args.slice(i));
                        args.splice(i, args.length - i);
                        this.parent.push(tag);
                        return tag;
                    }
                }
            }
        }
        return this;
    }

    insert_lt(caret, ...kwargs) {
        var caret = new XMLCaret(...kwargs);
        caret.start_idx++;
        this.parent.replace(this, [new XMLText(String(this), 0, ...kwargs), new XMLTagBegin(caret)]);
        return caret;
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.push_special("'", ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        return this.push_special('"', ...kwargs);
    }

    insert_newline(caret, newline_count, indent, ...kwargs) {
        return this.push_special('\n'.repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }

    insert_solidus(caret, ...kwargs) {
        return this.push_special('/', ...kwargs);
    }

    insert_exclamation(caret, ...kwargs) {
        return this.push_special('!', ...kwargs);
    }

    insert_eq(caret, ...kwargs) {
        return this.push_special('=', ...kwargs);
    }
}

class XMLBinary extends XMLArgs {
    constructor(lhs, rhs, indent = 0, parent = null) {
        super([lhs, rhs], indent, parent);
    }

    get lhs() {
        return this.args[0];
    }

    set lhs(value) {
        this.args[0] = value;
        value.parent = this;
    }

    get rhs() {
        return this.args[1];
    }

    set rhs(value) {
        this.args[1] = value;
        value.parent = this;
    }

    toJSON() {
        return {
            [this.func]: [
                this.lhs.toJSON(),
                this.rhs.toJSON()
            ]
        };
    }

    push(arg) {
        throw new Error(`push operation not allowed for ${this.constructor.name}`);
    }
}

class XMLEq extends XMLBinary {
    strFormat() {
        return '%s=%s';
    }

    insert_apostrophe(caret, ...kwargs) {
        if (caret === this.rhs && caret instanceof XMLCaret)
            this.rhs = new XMLApostrophe(caret);
        return caret;
    }

    insert_quotation(caret, ...kwargs) {
        if (caret === this.rhs && caret instanceof XMLCaret)
            this.rhs = new XMLQuotation(caret);
        return caret;
    }

    insert_space(caret, ...kwargs) {
        caret = new XMLCaret(...kwargs);
        this.parent.push(caret);
        return caret;
    }

    insert_newline(caret, newline_count, indent, ...kwargs) {
        const parent = this.parent;
        if (parent instanceof XMLTagBegin)
            return parent.push_special('\n'.repeat(newline_count) + ' '.repeat(indent), ...kwargs);
        return super.insert_newline(caret, newline_count, indent, ...kwargs);
    }
    insert_solidus(caret, ...kwargs) {
        return this.parent.insert_solidus(this, ...kwargs);
    }
    insert_ampersand(caret, ...kwargs) {
        return this.push_special('&', ...kwargs);
    }
    insert_lt(caret, ...kwargs) {
        return this.push_special('<', ...kwargs);
    }
    insert_eq(caret, ...kwargs) {
        return this.push_special('=', ...kwargs);
    }
    insert_exclamation(caret, ...kwargs) {
        return this.push_special('!', ...kwargs);
    }
    insert_token(caret, token, ...kwargs) {
        return this.parent.insert_token(this, token, ...kwargs);
    }
}

class XMLEntity extends Closable(XMLUnary) {
	get is_XMLEntity() {
		return true;
	}

    get start_idx() {
        return this.arg.start_idx - 1;
    }

    get end_idx() {
        return this.arg.end_idx
    }

    unescape() {
        // Minimal entity unescaper for common entities and numeric codes
        const entityStr = `&${this.arg};`;
        const match = entityStr.match(/^&(?:#(\d+)|#x([\da-f]+)|(\w+));$/i);
        if (match) {
            if (match[1]) {  // Decimal numeric entity
                return String.fromCharCode(parseInt(match[1], 10));
            }
            if (match[2]) {  // Hexadecimal numeric entity
                return String.fromCharCode(parseInt(match[2], 16));
            }
            // Named entities
            const entities = {
                'amp': '&',
                'apos': "'",
                'gt': '>',
                'lt': '<',
                'nbsp': ' ',
                'quot': '"'
            };
            const name = match[3].toLowerCase();
            return entities[name] || entityStr;
        }
        return entityStr;
    }

    strFormat() {
        let s = '&' + this.arg;
        if (this.is_closed) {
            s += ';';
        }
        return s;
    }

    insert_semicolon(caret, ...kwargs) {
        this.is_closed = true;
        return this;
    }

    insert_token(caret, token, ...kwargs) {
        if (caret instanceof XMLText && caret.text.length >= 32)
			// &(#[0-9]+|#x[0-9a-f]+|[^\t\n\f <&#;]{1,32});
            return this.push_special(token, ...kwargs);
        return super.insert_token(caret, token, ...kwargs);
    }

    // Insertion handlers for special characters
    insert_ampersand(caret, ...kwargs) {
        return this.push_special('&', ...kwargs);
    }

    insert_lt(caret, ...kwargs) {
        return this.push_special('<', ...kwargs);
    }

    insert_space(caret, ...kwargs) {
        return this.push_special(' ', ...kwargs);
    }

    insert_newline(caret, newline_count, indent, ...kwargs) {
        return this.push_special('\n'.repeat(newline_count) + ' '.repeat(indent), ...kwargs);
    }

    insert_eq(caret, ...kwargs) {
        return this.push_special('=', ...kwargs);
    }

    insert_exclamation(caret, ...kwargs) {
        return this.push_special('!', ...kwargs);
    }

    insert_solidus(caret, ...kwargs) {
        return this.push_special('/', ...kwargs);
    }

    insert_apostrophe(caret, ...kwargs) {
        return this.push_special("'", ...kwargs);
    }

    insert_quotation(caret, ...kwargs) {
        return this.push_special('"', ...kwargs);
    }
    insert_backtick(caret, ...kwargs) {
        let doc, parser, md;
        if ((doc = this.parent) instanceof XMLDocument && (parser = doc.parent) instanceof XMLParser && (md = parser.parent)) {
            let $new = this.push_special('', kwargs.start_idx - 1);
            const {MarkdownText} = md.constructor;
            $new = new MarkdownText($new.text, md.indent, $new.start_idx);
            md.replace(parser, $new);
            return $new.parse('`', ...kwargs);
        }
        return this.push_special('`', ...kwargs);
    }
}

class XMLContainerTag extends XMLArgs {
    get is_XMLContainerTag() { return true; }

    get tagBegin() {
        return this.args[0];
    }

    get tagEnd() {
        return this.args[this.args.length - 1];
    }

    set tagEnd(tagEnd) {
        this.args[this.args.length - 1] = tagEnd;
        if (this.__computedProperties && this.__computedProperties.hasOwnProperty('physicalText')) {
            delete this.__computedProperties.physicalText;
        }
    }

    get children() {
        return this.args.slice(1, -1);
    }

    set_tagEnd(tagEnd) {
        this.tagEnd = tagEnd;
    }

    get tag() {
        return this.tagBegin.tag;
    }

    get start_idx() {
        return this.tagBegin.start_idx;
    }

    get end_idx() {
        if (this.is_unbalanced) {
            if (this.args.length === 1 && this.args[0] instanceof XMLCaret) {
                return this.tagBegin.end_idx;
            }
            return this.args[this.args.length - 1].end_idx;
        }
        return this.tagEnd.end_idx;
    }

    get physicalText() {
        if (!this.__computedProperties) this.__computedProperties = {};
        if (!this.__computedProperties.hasOwnProperty('physicalText')) {
            let s = this.tagBegin.toString() + this.args.slice(1).map(arg => arg.toString()).join('');
            if (this.is_unbalanced) {
                this.__computedProperties.physicalText = s;
            } else {
                this.__computedProperties.physicalText = s + this.tagEnd.toString();
            }
        }
        return this.__computedProperties.physicalText;
    }

    get text() {
        if (!this.__computedProperties) this.__computedProperties = {};
        if (!this.__computedProperties.hasOwnProperty('text')) {
            this.__computedProperties.text = this.args.map(arg => arg.text).join('');
        }
        return this.__computedProperties.text;
    }

    get logicalLength() {
        return this.args.reduce((sum, el) => sum + el.logicalLength, 0);
    }

    get texts() {
        if (!this.__computedProperties) this.__computedProperties = {};
        if (!this.__computedProperties.hasOwnProperty('texts')) {
            this.__computedProperties.texts = this.args.flatMap(nd => nd.texts);
        }
        return this.__computedProperties.texts;
    }

    get zeros() {
        if (!this.__computedProperties) this.__computedProperties = {};
        if (!this.__computedProperties.hasOwnProperty('zeros')) {
            if (!this.text) {
                this.__computedProperties.zeros = [0];
            } else {
                let zeros = [];
                let length = 0;
                for (const arg of this.args) {
                    zeros = zeros.concat(arg.zeros.map(zero => zero + length));
                    length += arg.text.length;
                }
                this.__computedProperties.zeros = zeros;
            }
        }
        return this.__computedProperties.zeros;
    }

    get style() {
        if (!this.__computedProperties) this.__computedProperties = {};
        if (!this.__computedProperties.hasOwnProperty('style')) {
            let _style = {};
            if (this.text) {
                const arg = this.children; // Inconsistency in original: used both children and "this.arg"
                if (Array.isArray(arg)) {
                    const args = arg;
                    if (["msub", "munder"].includes(this.tag)) {
                        if (args.length === 2) {
                            args[1].modify_style('sub');
                        }
                    } else if (["msup", "mover"].includes(this.tag)) {
                        if (args.length === 2) {
                            args[1].modify_style('sup');
                        }
                    } else if (["msubsup", "munderover"].includes(this.tag)) {
                        if (args.length === 3) {
                            args[1].modify_style('sub');
                            args[2].modify_style('sup');
                        }
                    }
                }

                _style[this.tag] = new Range(0, this.text.length);

                for (const [tag, set] of Object.entries(arg.style)) {
                    if (_style[tag]) {
                        _style[tag] = _style[tag].union_without_merging(set);
                    } else {
                        _style[tag] = set;
                    }
                }
            }
            this.__computedProperties.style = _style;
        }
        return this.__computedProperties.style;
    }

    get is_unbalanced() {
        return !this.tagEnd || (this.tagEnd.constructor && this.tagEnd.constructor.name === 'XMLUnbalancedTag');
    }

    logical2physical(pos) {
        return this.arg.logical2physical(pos) + this.tagBegin.length;
    }

    physical2logical(pos) {
        return Math.max(
            Math.min(
                this.arg.physical2logical(pos - this.tagBegin.length),
                this.text.length - 1
            ),
            0
        );
    }

    is_physically_valid(pos) {
        const beginLength = this.tagBegin.length;
        const endLength = this.is_unbalanced ? 0 : this.tagEnd.length;
        if (beginLength <= pos && pos < this.length - endLength) {
            return this.arg.is_physically_valid(pos - beginLength);
        }
    }

    is_sibling(start_idx, end) {
        const beginLength = this.tagBegin.length;
        const endLength = this.is_unbalanced ? 0 : this.tagEnd.length;
        if (beginLength <= start_idx && end <= this.length - endLength) {
            start_idx -= beginLength;
            end -= beginLength;
            return this.arg.is_sibling(start_idx, end);
        }
    }

    getPhysicalIndices(start_idx, end_idx) {
        [start_idx, end_idx] = this.arg.getPhysicalIndices(start_idx, end_idx);

        const physicalText = this.arg.toString();
        let _stop = end_idx;
        while (_stop < physicalText.length && physicalText[_stop].match(/\s/)) {
            _stop++;
        }

        if (_stop === physicalText.length) {
            if (!start_idx) {
                end_idx = _stop + (this.is_unbalanced ? 0 : this.tagEnd.length);
            }
        }

        end_idx += this.tagBegin.length;
        if (start_idx)
            start_idx += this.tagBegin.length;

        return [start_idx, end_idx];
    }

    enumerate() {
        return this.ptr.enumerate();
    }

    has(cls) {
        if (this instanceof cls) {
            return true;
        }
        return this.ptr.has(cls);
    }

    reduceToText() {
        const arg = this.arg;
        const tagBegin = this.tagBegin;
        const tagEnd = this.tagEnd;
        const parent = this.parent;
        console.assert(!tagEnd, "tagEnd should be null");

        if (parent.is_XMLArgs) {
            const index = parent.args.indexOf(this);
            let count = 1;
            let args;

            if (Array.isArray(arg)) { // arg.is_XMLArgs
                args = [...arg];
                args.forEach(a => a.parent = parent);

                if (args[0].is_XMLText) {
                    args[0].start_idx = tagBegin.start_idx;
                } else {
                    args.unshift(new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx, parent));
                }

                if (index > 0 && parent.args[index - 1].is_XMLText) {
                    index--;
                    count++;
                    args[0].start_idx = parent.args[index].start_idx;
                }
            }
            else if (arg instanceof XMLCaret) {
                const newArg = new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx, parent);
                if (index + 1 < parent.args.length && parent.args[index + 1].is_XMLText) {
                    count++;
                    newArg.end_idx = parent.args[index + 1].end_idx;
                }
                if (index > 0 && parent.args[index - 1].is_XMLText) {
                    index--;
                    count++;
                    newArg.start_idx = parent.args[index].start_idx;
                }
                args = [newArg];
            } 
            else {
                arg.parent = parent;
                if (arg.is_XMLText) {
                    if (index + 1 < parent.args.length && parent.args[index + 1].is_XMLText) {
                        count++;
                        arg.end_idx = parent.args[index + 1].end_idx;
                    }
                    if (index > 0 && parent.args[index - 1].is_XMLText) {
                        index--;
                        count++;
                        arg.start_idx = parent.args[index].start_idx;
                    } 
                    else {
                        arg.start_idx = tagBegin.start_idx;
                    }
                    args = [arg];
                } 
                else {
                    args = [
                        new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx, parent), 
                        arg
                    ];
                    if (index > 0 && parent.args[index - 1].is_XMLText) {
                        index--;
                        count++;
                        args[0].start_idx = parent.args[index].start_idx;
                    }
                }
            }

            // Splice implementation
            parent.args.splice(index, count, ...args);
        } 
        else { // parent.is_XMLContainerTag
            let newChild;
            if (Array.isArray(arg)) { // arg.is_XMLArgs
                newChild = [...arg];
                if (newChild[0].is_XMLText) {
                    newChild[0].start_idx = tagBegin.start_idx;
                } 
                else
                    newChild.unshift(new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx, arg));
            } 
            else if (arg.is_XMLText) {
                arg.start_idx = tagBegin.start_idx;
                newChild = arg;
            } 
            else if (arg instanceof XMLCaret)
                newChild = new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx);
            else {
                newChild = new XMLArgs([
                    new XMLText(tagBegin.reduceToText(), 0, tagBegin.start_idx), 
                    arg
                ]);
            }

            newChild.parent = parent;
            parent.replace(this, newChild);
        }
    }

    get html() {
        return this.args.map(arg => arg.html).join('');
    }
}

class XMLDocument extends XMLArgs {
    insert_backtick(caret, ...kwargs) {
        let thisObj = this.parent;
        let md = thisObj?.parent;
        if (md && (md.is_MarkdownSPAN || md.is_MarkdownLI) && !this.has_newline()) {
            let mdText = thisObj.previousElementSibling;
            if (mdText && mdText.is_MarkdownText) {
                let regex = /(?<!`)`([^`]*)$/;
                let m = mdText.text.match(regex);
                if (m) {
                    let MarkdownCODE = md.constructor.MarkdownCODE;
                    let MarkdownText = mdText.constructor;
                    let latter = m[1] || '';
                    mdText.text = mdText.text.substring(0, mdText.text.length - m[0].length);
                    if (!mdText.text) {
                        mdText.remove();
                    }
                    let code = new MarkdownCODE(
                        new MarkdownText(
                            latter + String(this), 
                            md.indent, 
                            this.start_idx - latter.length
                        ), 
                        md.indent
                    );
                    md.replace(thisObj, code);
                    return code;
                }
            }
        }
        return this.insert_token(caret, '`', ...kwargs);
    }

    insert_gt(caret, ...kwargs) {
        return this.insert_token(caret, '>', ...kwargs);
    }

    insert_token(caret, token, ...kwargs) {
        if (caret instanceof XMLText) {
            let thisObj = this.parent;
            let md = thisObj?.parent;
            if (md) {
                var $new = new md.constructor.MarkdownText(caret.text, md.indent, caret.start_idx);
                $new.text += token;
                caret = $new;
                if (this.args.length > 1) {
                    this.args.pop();
                    $new = [thisObj, $new];
                }
                md.replace(thisObj, $new);
                return caret;
            }
        }
        return caret.push_token(token, ...kwargs);
    }

    insert_right_bracket(caret, ...kwargs) {
        let thisObj = this.parent;
        let md = thisObj?.parent;
        if (md && md instanceof md.constructor.MarkdownBracket) {
            md.is_closed = true;
            return md;
        }
        return this.insert_token(caret, ']', ...kwargs);
    }

    get html() {
        return this.args.map(arg => arg.html).join('\n');
    }
}

export default class XMLParser extends AbstractParser {
    is_Paragraph = false;
    is_token = true;

    constructor(parent = null, ...kwargs) {
        super(new XMLCaret(...kwargs));
        this.root = new XMLDocument([this.caret], 0, this);
        this.parent = parent;
        this.indent = 0;
    }

    get previousElementSibling() {
        const index = this.parent.args.indexOf(this);
        if (index > 0)
            return this.parent.args[index - 1];
        return null;
    }

    get start_idx() {
        return this.root.start_idx;
    }

    get end_idx() {
        return this.root.end_idx;
    }

    get html() {
        return this.root.html;
    }

    has_newline() {
        return this.root.has_newline();
    }

    get plainText() {
        return String(this);
    }

    toString() {
        return String(this.root);
    }

    build(text) {
        for (var [start_idx, token] of enumerate(text))
            this.parse(token, start_idx);
        var start_idx = text.length;
        this.parse("\n", start_idx);
        this.parse('', start_idx + 1);
        return this.root;
    }

    static components = [
        'XMLText', 
        'XMLTagBegin',
        'XMLTagEnd',
        'XMLTagVoid',
        'XMLEntity',
        'XMLContainerTag',
        'XMLArgsNullSeparated',
    ];
    static match_XMLTagBegin(arg, tagName) {
        if (arg instanceof this) {
            var {root : {args}} = arg;
            if (args.length == 1) {
                var [tagBegin] = args;
                return tagBegin instanceof XMLTagBegin && tagBegin.tagName.text.toLowerCase() == tagName;
            }
        }
    }
    find_path() {
    }
}
XMLParser.prototype.search_tagBegin = IndentedNode.prototype.search_tagBegin;

console.log('import xml.js');
