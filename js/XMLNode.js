class XMLNode {
    constructor(parent) {
		this.parent = parent;
    }

    get root() {
		var self = this;
    	while (self.parent)
        	self = self.parent;
        return self;
	}

    append_left_tag(tag) {
        var parent = this.parent;
        var caret = new XMLNodeCaret();
        var node = new XMLNodeContainerTag(tag, caret, null, parent);
        if (parent instanceof XMLNodeArray)
            parent.args.push(node);
		else {
			node = new XMLNodeArray([this, node], parent);
	        if (parent)
	            parent.replace(this, node);
		}

		return caret;
	}

    append_text_node(text) {
		var parent = this.parent;
		var node = new XMLNodeText(text, parent);
        if (parent instanceof XMLNodeArray) {
			console.assert(!parent.args.back().is_XMLNodeText, "!this.args.back().is_XMLNodeText");
			parent.args.push(node);
        	return node;
		}
		else {
	        var array = new XMLNodeArray([this, node], parent);
	        if (parent)
	            parent.replace(this, array);
	        return array;
		}
	}

    append_single_tag(tag) {
		var parent = this.parent;
		var node = new XMLNodeVoidTag(tag, parent);
        if (parent instanceof XMLNodeArray) {
            parent.args.push(node);
            return node;
		}
		else {
	        var array = new XMLNodeArray([this, node], parent);
	        if (parent)
	            parent.replace(this, array);
	        return array;
		}
	}

    get zeros() {
		return [];
	}

	get style() {
		return {};
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
		return this.stop - this.start;
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
		var start = 0;
		var logicalText = this.text;
		var totalLength = logicalText.length;
		for (var [index, seg] of enumerate(segments)) {
			while (logicalText[start] && logicalText[start].isspace())
				++start;

			if (!logicalText.startsWith(seg, start)) {
				var sCumulated = '';
				var hit = false;

				for (var i of range(start, totalLength)) {
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
					seg = logicalText.slice(start, i + 1);
				else {
					console.log("richText.text.slice(start).startsWith(seg)");
					console.log(segments);
					console.log(this.text);
					segments.delete(index, segments.length - index);
					break;
				}

			}

			var end = start + seg.length;

			logicalOffset.push({start, end});
			start = end;
		}

		return logicalOffset;
	}
}

export class XMLNodeCaret extends XMLNode {
    get is_XMLNodeCaret(){
		return true;
	}

	constructor(parent){
		super(parent);
	}

    append_left_tag(tag) {
        var caret = new XMLNodeCaret();
        var node = new XMLNodeContainerTag(tag, caret, null, this.parent);
        if (this.parent)
            this.parent.replace(this, node);
        return caret;
	}

    append_text_node(text) {
        var node = new XMLNodeText(text, this.parent);
        if (this.parent)
            this.parent.replace(this, node);
        return node;
	}

    append_single_tag(tag) {
        var node = new XMLNodeVoidTag(tag, this.parent);
        if (this.parent)
            this.parent.replace(this, node);
        return node;
	}

	get text() {
		return '';
	}

	get plainText() {
		return '';
	}

	get logicalLength() {
		return 0;
	}

	get texts() {
		return [];
	}

    toString() {
        return "";
    }

    get length() {
		return 0;
	}
}

class XMLNodeText extends XMLNode {
    get is_XMLNodeText(){
		return true;
	}

    constructor(text, parent) {
		super(parent);
		this.arg = text;
    }

    toString() {
        return this.arg.toString();
    }

    get start() {
		return this.arg.start;
	}

    get stop() {
		return this.arg.stop;
	}

    set start(start) {
		this.arg.start = start;
	}

    set stop(stop) {
		this.arg.stop = stop;
	}

	get text() {
		return this.arg.text;
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

    getPhysicalIndices(start, stop) {
		return [start, stop];
    }

    append_text_node(text) {
		console.assert(this.stop == text.start, "this.stop == text.start");
		this.stop = text.stop;
		return this;
	}
}

export class XMLNodeContainerTag extends XMLNode {
    get is_XMLNodeContainerTag(){
		return true;
	}

	constructor(tagBegin, arg, tagEnd, parent) {
		super(parent);
        Object.assign(this, {tagBegin, arg, tagEnd});
        this.arg.parent = this;
    }

	get tag() {
		return this.tagBegin.tag;
	}

    get start() {
		return this.tagBegin.start;
	}

    get stop() {
		if (this.is_unbalanced) {
			if (this.arg.is_XMLNodeCaret)
                return this.tagBegin.stop;
			return this.arg.stop;
		}

		return this.tagEnd.stop;
	}

    toString() {
		var s = this.tagBegin.toString() + this.arg.toString();
		if (this.is_unbalanced)
			return s;
        return s + this.tagEnd.toString();
    }

	get text() {
		return this.arg.text;
	}

	get plainText() {
		switch (this.tag) {
		case 'script':
		case 'style':
			return '';
		}
		var {plainText} = this.arg;
		switch (this.tag.toLowerCase()) {
		case 'div':
		case 'p':
		case 'h1':
		case 'h2':
		case 'h3':
		case 'h4':
		case 'h5':
		case 'h6':
			if (!plainText.match(/[\r\n]$/))
				plainText += '\n';
		}
		return plainText;
	}

	get logicalLength() {
		return this.arg.logicalLength;
	}

	get texts() {
		return this.arg.texts;
	}

    get zeros() {
		return this.text? this.arg.zeros : [0];
	}

	get style() {
		if (!this._style) {
	        var _style = {};
	        if (this.text) {
				if (this.arg.is_XMLNodeArray) {
					var args = this.arg.args;
					switch (this.tag) {
					case 'msub':
					case 'munder':
						if (args.length == 2)
							args[1].modify_style('sub');
						break;
					case 'msup':
					case 'mover':
						if (args.length == 2)
							args[1].modify_style('sup');
						break;
					case 'msubsup':
					case 'munderover':
						if (args.length == 3) {
							args[1].modify_style('sub');
							args[2].modify_style('sup');
						}
						break;
					}
				}

				_style[this.tag] = new Range(0, len(this.text));
		        for (var [tag, set] of Object.entries(this.arg.style)) {
		            if (tag in _style)
						_style[tag] = _style[tag].union_without_merging(set);
		            else
		                _style[tag] = set;
				}
			}

	        this._style = _style;
		}

		return this._style;
	}

	get is_unbalanced() {
		return !this.tagEnd || this.tagEnd.is_XMLNodeUnbalancedTag;
	}

    logical2physical(pos) {
        return this.arg.logical2physical(pos) + this.tagBegin.length;
	}

    physical2logical(pos) {
        return (this.arg.physical2logical(pos) - this.tagBegin.length).clip(0, len(this.text) - 1);
	}

    getPhysicalIndices(start, stop) {
		[start, stop] = this.arg.getPhysicalIndices(start, stop);
		var physicalText = this.arg.toString();

        var _stop = stop;
        //ignore white spaces to the end;
        while (physicalText[_stop] && physicalText[_stop].isspace())
        	++_stop;

        if (_stop == len(physicalText)) {
			_stop += this.tagEnd.length;
            if (!start)
				stop = _stop;
		}

		stop += this.tagBegin.length;
		if (start)
			start += this.tagBegin.length;

		return [start, stop];
    }

	replace(old, node) {
        if (this.arg != old)
            throw new Error("arg != old");
        this.arg = node;

        if (!node.is_XMLNodeCaret) {
			console.assert(this.tagBegin.stop == node.start, "this.tagBegin.stop == node.start");
			if (!this.is_unbalanced)
				console.assert(node.stop == this.tagEnd.start, "node.stop == this.tagEnd.start");
		}

        if (node.parent)
            console.assert(node.parent == this, "node.parent == this");
        else
            node.parent = this;
    }

	reduceToNodeText() {
		var {arg, tagBegin, tagEnd, parent} = this;
		console.assert(tagEnd == null, "tagEnd == null");
		if (parent.is_XMLNodeArray) {
			var index = parent.args.indexOf(this);
			var count = 1;
			var args;
			if (arg.is_XMLNodeArray) {
				args = arg.args;
				for (var arg of args)
					arg.parent = parent;

				if (args[0].is_XMLNodeText)
					args[0].start = tagBegin.start;
				else
					args.unshift(new XMLNodeText(tagBegin.reduceToNodeText(), parent));

				if (index && parent.args[index - 1].is_XMLNodeText) {
					--index;
					++count;
					args[0].start = parent.args[index].start;
				}
			}
			else if (arg.is_XMLNodeCaret) {
				arg = new XMLNodeText(this.tagBegin.reduceToNodeText(), parent);
				if (parent.args[index + 1] && parent.args[index + 1].is_XMLNodeText) {
					++count;
					arg.stop = parent.args[index + 1].stop;
				}

				if (index && parent.args[index - 1].is_XMLNodeText) {
					--index;
					++count;
					arg.start = parent.args[index].start;
				}

				args = [arg];
			}
			else {
				arg.parent = parent;
				if (arg.is_XMLNodeText) {
					if (parent.args[index + 1] && parent.args[index + 1].is_XMLNodeText) {
						++count;
						arg.stop = parent.args[index + 1].stop;
					}

					if (index && parent.args[index - 1].is_XMLNodeText) {
						--index;
						++count;
						arg.start = parent.args[index].start;
					}
					else
						arg.start = tagBegin.start;

					args = [arg];
				}
				else {
					args = [new XMLNodeText(this.tagBegin.reduceToNodeText(), parent), arg];
					if (index && parent.args[index - 1].is_XMLNodeText) {
						--index;
						++count;
						args[0].start = parent.args[index].start;
					}
				}
			}

			parent.args.splice(index, count, ...args);
		}
		else {
			console.assert(parent.is_XMLNodeContainerTag, "parent.is_XMLNodeContainerTag");
			if (arg.is_XMLNodeArray) {
				var args = arg.args;
				if (args[0].is_XMLNodeText)
					args[0].start = tagBegin.start;
				else
					args.unshift(new XMLNodeText(tagBegin.reduceToNodeText(), arg));
			}
			else if (arg.is_XMLNodeText)
				arg.start = tagBegin.start;
			else if (arg.is_XMLNodeCaret)
				arg = new XMLNodeText(tagBegin.reduceToNodeText());
			else
				arg = new XMLNodeArray([new XMLNodeText(this.tagBegin.reduceToNodeText()), arg]);

			arg.parent = parent;
			parent.replace(this, arg);
		}
	}

    append_tag(node) {
		var parent = this.parent;
        if (parent instanceof XMLNodeArray) {
			node.parent = parent;
			console.assert(!node.is_XMLNodeCaret, "!node.is_XMLNodeCaret");
            parent.args.push(node);
            return node;
		}
		else {
	        var array = new XMLNodeArray([this, node], parent);
	        if (parent)
	            parent.replace(this, array);
	        return array;
		}
	}

	sanctity_check() {
		var {tagBegin, arg, tagEnd} = this;
		if (this.is_unbalanced) {
			if (!arg.is_XMLNodeCaret) {
				if (tagBegin.stop != arg.start)
					return "tagBegin.stop != arg.start";
			}
		}
		else {
			if (arg.is_XMLNodeCaret) {
				if (tagBegin.stop != tagEnd.start)
					return "tagBegin.stop != tagEnd.start";
			}
			else {
				if (tagBegin.stop != arg.start)
					return "tagBegin.stop != arg.start";

				if (arg.stop != tagEnd.start)
					return "arg.stop != tagEnd.start";
			}
		}

		return arg.sanctity_check();
	}
}

class XMLNodeVoidTag extends XMLNode {
	get is_XMLNodeVoidTag(){
		return true;
	}

    constructor(arg, parent) {
        super(parent);
        this.arg = arg;
    }

	get tag() {
		return this.arg.tag;
	}

    get start() {
		return this.arg.start;
	}

    get stop() {
		return this.arg.stop;
	}

    toString() {
        return this.arg.toString();
    }

	get text() {
		return this.arg.text;
	}

	get plainText() {
		return this.arg.plainText;
	}

	get logicalLength() {
		return 1;
	}

	get texts() {
		return [this.text];
	}

	get style() {
		if (!this._style) {
	        var _style = {};
            _style[this.tag] = new Range(0, len(this.text));
	        this._style = _style;
		}

		return this._style;
	}

    logical2physical(pos) {
		return this.arg.length - 2;
	}

    physical2logical(pos) {
        return 0;
	}

	getPhysicalIndices(start, stop) {
		return [0, this.arg.length];
    }
}


class XMLNodeArray extends XMLNode {
	get is_XMLNodeArray(){
		return true;
	}

    constructor(args, parent) {
		super(parent);
        this.args = args;
        for (let ptr of args)
			ptr.parent = this;
    }

    append_left_tag(tag) {
        var caret = new XMLNodeCaret();
        this.args.push(new XMLNodeContainerTag(tag, caret, null, this));
        return caret;
	}

    append_text_node(text) {
		var node = new XMLNodeText(text, this);
		console.assert(!this.args.back().is_XMLNodeText, "!this.args.back().is_XMLNodeText");
        this.args.push(node);
        return node;
	}

    append_single_tag(tag) {
		var node = new XMLNodeVoidTag(tag, this);
        this.args.push(node);
        return node;
	}

    append_tag(node) {
		node.parent = this;
		console.assert(!node.is_XMLNodeCaret, "!node.is_XMLNodeCaret");
        this.args.push(node);
        return node;
	}

    toString() {
        return this.args.map(el => el.toString()).join('');
    }

    get start() {
		return this.args[0].start;
	}

    get stop() {
		return this.args.back().stop;
	}

	get text() {
		return this.args.map(el => el.text).join('');
	}

	get plainText() {
		return this.args.map(el => el.plainText).join('');
	}

	get logicalLength() {
		return sum(this.args.map(el => el.logicalLength));
	}

	get texts() {
		var texts = [];
		for (var arg of this.args) {
			texts.push(...arg.texts);
		}
		return texts;
	}

    get zeros() {
        var zeros = [];
        var length = 0;
        for (var arg of this.args) {
            zeros.push(...arg.zeros.map(zero => zero + length));
            length += len(arg.text);
		}
        return zeros;
	}

	get style() {
		if (!this._style) {
			for (var [i, tagEnd] of enumerate(this.args)) {
				if (tagEnd.is_XMLNodeUnbalancedTag) {
					var self = tagEnd.binaryTag;
					console.assert(self.tagEnd === tagEnd, "self.tagEnd === tagEnd");
					var parent;
					do {
						parent = self.parent;
						if (parent.is_XMLNodeArray) {
							var index = parent.args.indexOf(self);
							for (var j of range(index + 1, parent !== this? parent.args.length: i)) {
								parent.args[j].modify_style(tagEnd.tag);
							}
						}
						self = parent;
					}
					while (parent !== this);
				}
			}

			var _style = {};
	        var length = 0;
	        for (var arg of this.args) {
		        for (var [tag, set] of Object.entries(arg.style)) {
					set = set.add(length);
		            if (tag in _style)
						_style[tag] = _style[tag].union_without_merging(set);
		            else
		                _style[tag] = set;
				}
				length += len(arg.text);
			}

	        this._style = _style;
		}

		return this._style;
	}

    replace(old, node) {
        var i = this.args.indexOf(old);
        if (i < 0)
            throw new Error("replace(old, node)");

        console.assert (!node.is_XMLNodeCaret, "!node.is_XMLNodeCaret");
        this.args[i] = node;
        if (i) {
			console.assert (this.args[i - 1].stop == node.start, "this.args[i - 1].stop == node.start");
			if (node.is_XMLNodeText)
				console.assert(!this.args[i - 1].is_XMLNodeText, "!this.args[i - 1].is_XMLNodeText");
		}

        if (this.args[i + 1]) {
			console.assert (this.args[i + 1].start == node.stop, "this.args[i + 1].start == node.stop");
			if (node.is_XMLNodeText)
				console.assert(!this.args[i + 1].is_XMLNodeText, "!this.args[i + 1].is_XMLNodeText");
		}

        if (node.parent)
            console.assert(node.parent == this, "node.parent == this");
        else
            node.parent = this;
    }

    get logicalOffset() {
		if (!this._logicalOffset) {
	        var logicalOffset = [];
	        var start = 0;
	        for (var arg of this.args) {
	            stop = start + arg.logicalLength;
	            logicalOffset.push([start, stop]);
	            start = stop;
	        }

	        this._logicalOffset = logicalOffset;
		}

		return this._logicalOffset;
	}

    get physicalOffset() {
		if (!this._physicalOffset) {
	        var physicalOffset = [];
	        var start = 0;
	        for (var arg of this.args) {
	            stop = start + arg.length;
	            physicalOffset.push([start, stop]);
	            start = stop;
	        }

	        this._physicalOffset = physicalOffset;
		}
		return this._physicalOffset;
	}

    get offsets() {
		if (!this._offsets) {
			var offsets = [];
	        var offset = 0;
	        for (var arg of this.args) {
	            offsets.push(offset);
	            offset += arg.length - arg.logicalLength;
	        }
	        this._offsets = offsets;
		}
		return this._offsets;
	}

    logical2physical(pos) {
        var {logicalOffset, offsets} = this;
        var index = logicalOffset.binary_search(pos, (args, hit) => hit >= args[1] ? -1 : hit < args[0]? 1 : 0);
        var prev_start = logicalOffset[index][0];
        return this.args[index].logical2physical(pos - prev_start) + prev_start + offsets[index];
	}

    physical2logical(pos) {
        var {physicalOffset, offsets} = this;
        var index = physicalOffset.binary_search(pos, (args, hit) => hit >= args[1] ? -1 : hit < args[0]? 1 : 0);
        var prev_start = physicalOffset[index][0];
        return this.args[index].physical2logical(pos - prev_start) + prev_start - offsets[index];
	}

	cmp(args, hit) {
		return hit >= args[1] ? -1 : hit < args[0]? 1 : 0;
	}

	getPhysicalIndices(start, stop) {
        var {logicalOffset, offsets} = this;
        var index = logicalOffset.binary_search(start, this.cmp);
        var _index = logicalOffset.binary_search(stop - 1, this.cmp);

        if (index == _index) {
			var prev_start = logicalOffset[index][0];
	        return this.args[index].getPhysicalIndices(start - prev_start, stop - prev_start).add(prev_start + offsets[index]);
		}
		else {
			var [prev_start, prev_stop] = logicalOffset[index];
        	var _prev_start = logicalOffset[_index][0];
	        start = this.args[index].getPhysicalIndices(start - prev_start, prev_stop - prev_start).add(prev_start + offsets[index])[0];
	        stop = this.args[_index].getPhysicalIndices(0, stop - _prev_start).add(_prev_start + offsets[_index])[1];
	        return [start, stop];
		}
    }

	sanctity_check() {
		for (var i of range(this.args.length)) {
			if (i) {
				if (this.args[i].is_XMLNodeText && this.args[i - 1].is_XMLNodeText)
				 	return "this.args[i].is_XMLNodeText && this.args[i - 1].is_XMLNodeText";

				if (this.args[i].start != this.args[i - 1].stop)
					return "this.args[i].start != this.args[i - 1].stop";
			}

			if (this.args[i].is_XMLNodeCaret)
				return "this.args[i].is_XMLNodeCaret";

			var error = this.args[i].sanctity_check();
			if (error)
				return error;
		}
	}
}

export class XMLNodeUnbalancedTag extends XMLNode {
    get is_XMLNodeUnbalancedTag(){
		return true;
	}

	constructor(tagEnd, binaryTag, parent) {
		super(parent);
        Object.assign(this, {tagEnd, binaryTag});
		binaryTag.tagEnd = this;
    }

	get tag() {
		return this.tagEnd.tag;
	}

    get start() {
		return this.tagEnd.start;
	}

    get stop() {
		return this.tagEnd.stop;
	}

    toString() {
        return this.tagEnd.toString();
    }

	get text() {
		return '';
	}

	get plainText() {
		return '';
	}

	get logicalLength() {
		return 0;
	}

	get texts() {
		return [];
	}

    get zeros() {
		return [0];
	}
}

console.log('import XMLNode.js');
