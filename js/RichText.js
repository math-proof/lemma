import {XMLNodeCaret, XMLNodeContainerTag, XMLNodeUnbalancedTag} from "./XMLNode.js"

function compile(infix) {
    var caret = new XMLNodeCaret();

	var leftTagCount = {};
    for (var text of infix) {
        if (text.is_TagBegin) {
			caret = caret.append_left_tag(text);

			if (!leftTagCount[text.tag])
				leftTagCount[text.tag] = [];
			leftTagCount[text.tag].push(caret.parent);
			//console.assert(caret.parent.tagBegin === text, "caret.parent.tagBegin === text");
		}
        else if (text.is_TagEnd) {
            var root;
            var old = caret;
            while (true) {
                if (caret) {
	                root = caret;
	                caret = caret.parent;
	                if (caret instanceof XMLNodeContainerTag && caret.tag == text.tag) {
	                    caret.tagEnd = text;
						while (true) {
							var _caret = leftTagCount[text.tag].pop();
							if (caret === _caret)
								break;
							_caret.reduceToNodeText();
						}
	                    break;
	                }
                }
                else if (leftTagCount[text.tag].length) {
					var parent = leftTagCount[text.tag].pop();
					var caret = new XMLNodeUnbalancedTag(text, parent);
					while (parent.stop < root.stop)
						parent = parent.parent;

					caret = parent.append_tag(caret);
                    break;
				}
				else {
					text = text.reduceToNodeText();
					caret = old.append_text_node(text);
					break;
				}
            }
        }
        else if (text.is_VoidTag || text.is_HTMLEntity)
            caret = caret.append_single_tag(text);
        else
            caret = caret.append_text_node(text);
	}

	for (var tag in leftTagCount) {
		while (leftTagCount[tag].length) {
			leftTagCount[tag].pop().reduceToNodeText();
		}
	}

    return caret.root;
}

export function construct_rich_text(text){
	var start = 0;

	var richTexts = [];
	var leftTagCount = {};
	for (let m of text.matchAll(/<([a-z][-:_a-z]*\d*)(?:\s+:?[a-z][-:_a-z]*(?:=(?:"[^"]*"|'[^']*'))?)*\s*>(?=[\s\S]*?<\/\1>)|<\/([a-z][-:_a-z]*\d*)>|<(img|mspace|br|input|span|meta|link)(?:\s+:?[a-z][-:_a-z]*(?:=(?:"[^"]*"|'[^']*'))?)*\s*\/>|&(#[0-9]+|#x[0-9a-f]+|[^\t\n\f <&#;]{1,32});/ig)) {
//                                (1----------------)                                                                           (2----------------)   (3---------------------------------)                                                         (4---------------------------------------)
		var prevText = text.slice(start, m.index);
		if (prevText)
			richTexts.push(new PlainText(text, start, m.index));

		var end = m.index + m[0].length;
		var richText;
		if (m[1]) {
			var tag = m[1];
			richText = new TagBegin(text, m.index, end, tag);
			if (!(tag in leftTagCount))
				leftTagCount[tag] = 0;
			++leftTagCount[tag];
		}
		else if (m[2]) {
			var tag = m[2];
			if (leftTagCount[tag]){
				--leftTagCount[tag];
				richText = new TagEnd(text, m.index, end, tag);
			}
			else if (prevText) {
				richText = richTexts.pop();
				richText.stop = end;
			}
			else
				richText = new PlainText(text, m.index, end);
		}
		else if (m[3])
			richText = new VoidTag(text, m.index, end, m[3]);
		else
			richText = new HTMLEntity(text, m.index, end, m[4]);

		richTexts.push(richText);
		start = end;
	}

	var restText = text.slice(start);
	if (restText)
		richTexts.push(new PlainText(text, start, len(text)));

	return compile(richTexts);
}

class XMLText {
	constructor(src, start, stop){
		Object.assign(this, {src, start, stop});
	}

    toString(){
		return this.src.slice(this.start, this.stop);
	}

    get length() {
		return this.stop - this.start;
	}

	reduceToNodeText() {
		return new PlainText(this.src, this.start, this.stop);
	}
}

class TagBegin extends XMLText {
	is_TagBegin = true;
	constructor(src, start, stop, tag){
		super(src, start, stop);
		this.tag = tag;
	}
}

class TagEnd extends XMLText {
	is_TagEnd = true;
	constructor(src, start, stop, tag){
		super(src, start, stop);
		this.tag = tag;
	}
}

class VoidTag extends XMLText {
	is_VoidTag = true;
	constructor(src, start, stop, tag){
		super(src, start, stop);
		var text;
		switch (tag.toLowerCase()) {
		case 'img':
			text = '★';
			break;
		case 'mspace':
			text = ' ';
			break;
		case 'br':
			text = '\n';
			break;
		default:
			text = '?';
		}

		Object.assign(this, {text ,tag});
	}

	get plainText() {
		var {text} = this;
		return text == '?'? '': text;
	}
}

class HTMLEntity extends XMLText {
	is_HTMLEntity = true;
	constructor(src, start, stop, tag){
		super(src, start, stop);
		var text = he.unescape(`&${tag};`);
		if (text.length != 1)
			text = '?';

		tag = 'entity-' + tag;
		Object.assign(this, {text, tag});
	}
}

class PlainText extends XMLText {
	is_PlainText = true;

	constructor(src, start, stop){
		super(src, start, stop);
	}

	get text() {
		return this.src.slice(this.start, this.stop);
	}

	get plainText() {
		return this.text;
	}
}


function style_type(ptr, style){
	var {offsetStart, offsetStop} = ptr;
	var this_set = new Range(offsetStart, offsetStop);
	var style_intersected = {};
	for (var tag in style){
		var set = style[tag];

		var intersection = set.intersects(this_set);
		if (intersection.is_EmptySet)
			continue;

		style_intersected[tag] = intersection;
	}

	if (isEmpty(style_intersected))
		return;

	var indicator = [];
	for (var i of range(offsetStop - offsetStart)){
		indicator[i] = {className: ptr.className};
	}

	function processRangeObject(set, tag) {
		var {start, stop} = set;
		for (var i of range(start, stop)) {
			var {className} = indicator[i];
			if (className)
				indicator[i].className += ' ' + tag;
			else
				indicator[i].className = tag;
		}
	}

	for (var tag in style_intersected) {
		var set = style_intersected[tag];
		set = set.add(-offsetStart);

		var args = set.is_Range? [set]: set.args;
		for (var [i, s] of enumerate(args)) {
			if (i && args[i - 1].stop == s.start)
                tag = tag.toggleCase();
			processRangeObject(s, tag);
		}
	}

	var interval = [];
	var i = 0;
	while (i < indicator.length){
		for (var j = i + 1; j < indicator.length; ++j){
			if (indicator[j].className != indicator[i].className)
				break;
		}

		var className = indicator[i].className;
		if (!className)
			className = ptr.className;
		interval.push({offsetStart: i + offsetStart, offsetStop: j + offsetStart, className});
		i = j;
	}
	return interval;
}

export function split_interval_by_entity(self, clazzName, entity) {
	var style = {...self.style};
	for (var ent of entity) {
		if (!ent)
			continue;

		var {offsetStart, offsetStop, className} = ent;
		if (!style[className])
			style[className] = new EmptySet;

		style[className] = style[className].union(new Range(offsetStart, offsetStop));
	}

	return detect_style(self.interval(clazzName), style);
}

export function interval(self, className) {
	return detect_style(self.interval(className), self.style);
}

export function detect_style(interval, style){
	for (var i = 0; i < interval.length; ++i){
		var ptr = interval[i];

		var stype = style_type(ptr, style);
		if (Array.isArray(stype)){
			interval.splice(i, 1, ...stype);
			i += stype.length - 1;
		}
		else if (stype){
			ptr.className += ` ${stype}`;
		}
	}

	return interval;
}

console.log('import RichText.js');