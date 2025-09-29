"use strict";

function argmin(args){
	if (arguments.length == 1){
		args = arguments[0];
	}
	else{
		args = arguments;
	}

	var min = Infinity;
	var argmin = -1;
	for (var index of range(args.length)){
		if (args[index] < min){
			min = args[index];
			argmin = index;
		}
	}

	return argmin;
}

function argmax(args){
	if (arguments.length == 1){
		args = arguments[0];
	}
	else{
		args = arguments;
	}

	var max = -Infinity;
	var argmax = -1;
	for (var index of range(args.length)){
		if (args[index] > max){
			max = args[index];
			argmax = index;
		}
	}

	return argmax;
}

function $(selector){
	return document.querySelector(selector);
}

function get(url, data) {
	return axios.get(url, {params: data}).then(result => result.data);
}

function form_post(url, data) {
	if (url.match(/^https?:\/\//)) {
		data = {url, data};
		url = 'php/request/post.php';
	}

	return axios.post(url, Qs.stringify(data)).then(result => {
		var {data} = result;
		if (data && data.isString)
			return data.trim();
		return data;
	});
}

function json_post(url, data, header, stream) {
	var method = 'post';
	if (url.match(/^https?:\/\//)) {
		data = {url, data};
		url = 'php/request/post.php';
		data.header = header;
		if (stream) {
			var {id, signal, onmessage, onclose, onerror} = stream;
			data.id = id;
			return fetchEventSource(url, {
				method,
				headers: {
					"Content-Type": "application/json",
				},
				body: JSON.stringify(data),
				signal,
				onmessage,
				onclose,
				onerror,
				onopen(response) {
					if (response.ok && response.headers.get("content-type").includes("text/event-stream")) {
						return; // everything's good
					} else if (response.status >= 400 && response.status < 500 &&response.status !== 429) {
						// client-side errors are usually non-retriable:
						throw new FatalError();
					} else {
						throw new FatalError();
					}
				},
				openWhenHidden: true
			});
		}
	}

	var header = {'Content-Type': 'application/json'};
	return axios({url, method, data, header}).then(result => {
		var {data} = result;
		if (data.isString && data.back() == '\n')
			data = data.slice(0, -1);
		return data;
	});
}

function octet_stream_post(url, data, successCallback, errorCallback) {
	var {filename, binary} = data;
	var xhr = new XMLHttpRequest();
	xhr.open("POST", url);
	xhr.setRequestHeader('filename', filename);
	xhr.overrideMimeType("application/octet-stream");
	if(xhr.sendAsBinary)
		xhr.sendAsBinary(binary);
	else
		xhr.send(binary);

	xhr.onreadystatechange = function(event){
		if(xhr.readyState===4){
			if(xhr.status===200){
				var jqXHR = event.target;
				if (successCallback) {
					successCallback(JSON.parse(jqXHR.responseText));
				}
			}else{
				if (errorCallback) {
					errorCallback(jqXHR.responseText);
				}
			}
		}
	}
}

function ord(s) {
	return s.charCodeAt(0);
}

function chr(unicode) {
	return String.fromCharCode(unicode);
}

function strlen(s) {
	var length = 0;
	for (let i = 0; i < s.length; i++) {
		var code = s.charCodeAt(i)
		switch (code) {
		case 0x2002:
		//case 0x2014:
		case 0x2212:
			length += 1;
			break;
		default:
			if (code & 0xff80)
				length += 2;
			else
				length += 1;
		}
	}
	return length;
}

function getParameterByName(name, defaultValue) {
	return new URLSearchParams(window.location.search).get(name) || defaultValue;
}

function getParameter(name, evaluate) {
	var attrs = [];
	for (var m of name.matchAll(/\[([^\[\]]+)\]/g)) {
		attrs.push(m[1]);
	}
	name = name.replace(/(\[[^\[\]]+\])/g, "");
	var reg = new RegExp("(?<=^|&)" + name + "((?:\\[[^\\[\\]]+\\])*)=([^&]*)(?=&|$)", 'g');
	var {search} = window.location;
	if (search.startsWith("?")) {
		search = search.substr(1);
		var result = {};
		var hit = false;
		for (var m of search.matchAll(reg)) {
			var attr = m[1];
			var expr = unescape(m[2]);
			if (evaluate) {
				if (expr && expr.isString)
					expr = eval(expr);
			}
			if (attr) {
				var arglist = [];
				for (var m of attr.matchAll(/\[([^\[\]]+)\]/g)) {
					arglist.push(m[1]);
				}

				if (attrs.length) {
					if (attrs.equals(arglist))
						return expr;

					if (attrs.length >= arglist.length || arglist.slice(0, attrs.length).equals(attrs))
						continue;

					arglist = arglist.slice(attrs.length);
				}
				setitem(result, ...arglist, expr);
				hit = true;
			}
			else {
				if (!attrs.length) {
					return expr;
				}
			}
		}
		if (hit) {
			if (!attrs.length) {
				return list(result);
			}
		}
	}
}

function getParameters() {
	var kwargs = {};
	var search = window.location.search;
	if (search.startsWith("?")) {
		for (var tuple of search.slice(1).split('&')) {
			input_kwargs(kwargs, ...tuple.split('='));
		}
	}

	return kwargs;
}

function input_kwargs(kwargs, name, value){
	if (name.match(/[\[\]]+/)) {
		name = name.split(/[\[\]]+/);
		name = name.slice(0, -1);
		setitem(kwargs, ...name, value);
	}
	else {
		kwargs[name] = value;
	}
}

function equals(obj, _obj){
	if (obj == null){
		return _obj == null;
	}

	if (_obj == null){
		return false;
	}

	if (Array.isArray(obj)){
		if (Array.isArray(_obj)){
			return obj.equals(_obj);
		}
		return false;
	}

	if (Array.isArray(_obj)){
		return false;
	}

	if (typeof(obj) === "object"){
		if (typeof(_obj) === "object"){
			return dict_equals(obj, _obj);
		}
		return false;
	}

	if (typeof(_obj) === "object"){
		return false;
	}

	return obj == _obj;
}

function dict_equals(dict, _dict){
	var keys = Object.keys(dict);
	var _keys = Object.keys(_dict);
	if (keys.length != _keys.length)
		return false;

	for (let key of keys){
		if (!_dict.hasOwnProperty(key))
			return false;

		if (!equals(dict[key], _dict[key])){
			return false;
		}
	}

	return true;
}

Number.prototype.isNumber = true;

Number.prototype.compareTo = function(that) {
	return this - that;
};

Number.prototype.percentage = function() {
	return (this * 10000).round() / 100 + '%';
};

Number.prototype.equals = function(rhs){
	return this == rhs;
};

Number.prototype.add = function(rhs){
	if (rhs.is_Real)
		return rhs.add(this);

	if (rhs.isBigInt)
		return BigInt(this) + rhs;

	return this + rhs;
};

Number.prototype.sub = function(rhs){
	if (rhs.is_Real)
		return rhs.neg().add(this);

	if (rhs.isBigInt)
		return BigInt(this) - rhs;

	return this - rhs;
};

Number.prototype.mul = function(rhs){
	if (rhs.is_Real)
		return rhs.mul(this);

	if (rhs.isBigInt)
		return BigInt(this) * rhs;

	return this * rhs;
};

Number.prototype.div = function(rhs){
	if (rhs.is_Real)
		return rhs.inverse().mul(BitInt(this));

	return Rational.new(this, rhs);
};

Number.prototype.gt = function(rhs){
	if (rhs.is_Real)
		return rhs.lt(this);

	if (rhs.isBigInt)
		return BigInt(this) > rhs;

	return this > rhs;
};

Number.prototype.lt = function(rhs){
	if (rhs.is_Real)
		return rhs.gt(this);

	if (rhs.isBigInt)
		return BigInt(this) < rhs;

	return this < rhs;
};

Number.prototype.ge = function(rhs){
	if (rhs.is_Real)
		return rhs.le(this);

	if (rhs.isBigInt)
		return BigInt(this) >= rhs;

	return this >= rhs;
};

Number.prototype.le = function(rhs){
	if (rhs.is_Real)
		return rhs.ge(this);

	if (rhs.isBigInt)
		return BigInt(this) <= rhs;

	return this <= rhs;
};

Number.prototype.float = function() {
	return this;
};

Number.prototype.__defineGetter__("isNaN", function() {
	return Number.isNaN(this);
});

Number.prototype.__defineGetter__("is_positive", function() {
	return this > 0;
});

Number.prototype.__defineGetter__("is_negative", function() {
	return this < 0;
});

Number.prototype.__defineGetter__("is_nonpositive", function() {
	return this <= 0;
});

Number.prototype.__defineGetter__("is_nonnegative", function() {
	return this >= 0;
});

Number.prototype.__defineGetter__("is_zero", function() {
	return this == 0;
});

Number.prototype.__defineGetter__("isInteger", function() {
	return Number.isInteger(this);
});

Number.prototype.sign = function() {
	return Math.sign(this);
};

Number.prototype.round = function() {
	return Math.round(this);
};

Number.prototype.floor = function() {
	return Math.floor(this);
};

Number.prototype.ceil = function() {
	return Math.ceil(this);
};

Number.prototype.abs = function() {
	return Math.abs(this);
};

Number.prototype.neg = function() {
	return -this;
};

Number.prototype.sqrt = function() {
	return Math.sqrt(this);
};

Number.prototype.inverse = function() {
	return Rational.new(1, this);
};

Number.prototype.clip = function(min, max){
	if (this.lt(min))
		return min;

	if (this.gt(max))
		return max;

	return this;
};

Number.prototype.relu = function() {
	return this.is_positive? this: 0;
};

Number.prototype.toRational = function() {
	if (this.isInteger)
		return this;
	return Rational.new((this * (1 << 20)).round(), 1 << 20);
};

Number.prototype.encodeURI = function() {
	return this.toString();
};

//BigInt
BigInt.prototype.isBigInt = true;

BigInt.prototype.equals = function(rhs){
	if (rhs.is_Real)
		return false;

	if (!rhs.isBigInt) {
		if (rhs == Infinity || rhs == -Infinity)
			return false;

		rhs = BigInt(rhs);
	}


	return this == rhs;
};

BigInt.prototype.add = function(rhs){
	if (rhs.is_Real)
		return rhs.add(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity || rhs == -Infinity)
			return rhs;

		rhs = BigInt(rhs);
	}

	return this + rhs;
};

BigInt.prototype.sub = function(rhs){
	if (rhs.is_Real)
		return rhs.neg().add(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity || rhs == -Infinity)
			return -rhs;

		rhs = BigInt(rhs);
	}

	return this - rhs;
};

BigInt.prototype.mul = function(rhs){
	if (rhs.is_Real)
		return rhs.mul(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity || rhs == -Infinity)
			return this.sign() * rhs;

		rhs = BigInt(rhs);
	}

	return this * rhs;
};

BigInt.prototype.div = function(rhs){
	if (rhs.is_Real)
		return rhs.inverse().mul(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity || rhs == -Infinity)
			return 0;

		rhs = BigInt(rhs);
	}

	return Rational.new(this, rhs);
};

BigInt.prototype.gt = function(rhs){
	if (rhs.is_Real)
		return rhs.lt(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity)
			return false;

		if (rhs == -Infinity)
			return true;

		rhs = BigInt(rhs)
	}

	return this > rhs;
};

BigInt.prototype.lt = function(rhs){
	if (rhs.is_Real)
		return rhs.gt(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity)
			return true;

		if (rhs == -Infinity)
			return false;

		rhs = BigInt(rhs)
	}

	return this < rhs;
};

BigInt.prototype.ge = function(rhs){
	if (rhs.is_Real)
		return rhs.le(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity)
			return false;

		if (rhs == -Infinity)
			return true;

		rhs = BigInt(rhs)
	}

	return this >= rhs;
};

BigInt.prototype.le = function(rhs){
	if (rhs.is_Real)
		return rhs.ge(this);

	if (!rhs.isBigInt) {
		if (rhs == Infinity)
			return true;

		if (rhs == -Infinity)
			return false;

		rhs = BigInt(rhs)
	}

	return this <= rhs;
};

BigInt.prototype.__defineGetter__("is_positive", function() {
	return this > 0n;
});

BigInt.prototype.__defineGetter__("is_negative", function() {
	return this < 0n;
});

BigInt.prototype.__defineGetter__("is_nonpositive", function() {
	return this <= 0n;
});

BigInt.prototype.__defineGetter__("is_nonnegative", function() {
	return this >= 0n;
});

BigInt.prototype.__defineGetter__("is_zero", function() {
	return this == 0n;
});

BigInt.prototype.float = function() {
	return parseInt(this);
};

BigInt.prototype.isInteger = true;

BigInt.prototype.sign = function() {
	if (this > 0n)
		return 1;
	if (this < 0n)
		return -1;
	return 0;
};

BigInt.prototype.round = function() {
	return this.float();
};

BigInt.prototype.floor = function() {
	return this;
};

BigInt.prototype.ceil = function() {
	return this;
};

BigInt.prototype.abs = function() {
	if (this.sign() < 0)
		return -this;
	return this;
};

BigInt.prototype.neg = function() {
	return -this;
};

BigInt.prototype.sqrt = function() {
	return Math.sqrt(this.float());
};

BigInt.prototype.inverse = function() {
	return Rational.new(1n, this);
};

BigInt.prototype.toJSON = function() {
	if (this.abs() < (1n << 53n))
		return this.float();
	throw new Error("Do not know how to serialize a BigInt greater than 1 << 53");
};

BigInt.prototype.clip = function(min, max) {
	if (this.lt(min))
		return min;

	if (this.gt(max))
		return max;

	return this;
};

BigInt.prototype.relu = function() {
	return this.is_positive? this: 0n;
};

BigInt.prototype.toRational = function() {
	return this;
};

String.prototype.__defineGetter__("isInteger", function() {
	return this.isdigit();
});

String.prototype.__defineGetter__("isNumber", function() {
	return /^-?\d+(\.\d+)?$/.test(this);
});

String.prototype.lang = function() {
	if (this.match(XRegExp('\\p{Hiragana}')))
		return 'jp';

	if (this.length <= 2) {
		if (this.match(XRegExp('\\p{Han}')))
			return 'cn';
	}
	else {
		if (this.match(XRegExp('\\p{Han}{2,}')))
			return 'cn';
	}

	if (this.match(/[éèàùçœæ]/))
		return 'fr';

	if (this.match(/[äöüß]/))
		return 'de';

	if (this.match(XRegExp('\\p{Arabic}')))
		return 'ar';

	if (this.match(XRegExp('\\p{Hangul}')))
		return 'kr';

	return 'en';
};

String.prototype.rows = function() {
	return this.split('\n').length;
};

String.prototype.cols = function() {
	var cols = [];
	for (var line of this.split('\n')) {
		cols.push(line.strlen());
	}
	return cols.max() + 1;
};

String.prototype.equals = function(rhs){
	return this == rhs;
};

//python equivalent:
//from urllib import parse
//parse.urlparse(url)
//parse.quote(text)
String.prototype.encodeURI = function() {
	return encodeURIComponent(this);
};

String.prototype.compareTo = function(that){
	var lhs = Number(this);
	if (lhs.isNaN)
		return this.localeCompare(rhs);

	var rhs = Number(that);
	if (rhs.isNaN)
		return this.localeCompare(rhs);

	return lhs - rhs;
};

String.prototype.contains = function(rhs){
	return this.indexOf(rhs) >= 0;
};

String.prototype.format = function() {
	var args = arguments;
	var index = 0;
	return this.replace(/%[sd]/g,
		function() {
			return args[index++];
		}
	);
};

String.prototype.percentage = function() {
	return 'NaN';
};

// similar with String.replace
String.prototype.transform = function(regex, transformer){
	var newText = [];
	var start = 0;

	for (let m of this.matchAll(regex)){
		newText.push(this.slice(start, m.index));
		newText.push(transformer(m));

		start = m.index + m[0].length;
	}

	newText.push(this.slice(start));
	return newText.join('');
}

String.prototype.capitalize = function() {
	return this[0].toUpperCase() + this.slice(1).toLowerCase();
};

String.prototype.__defineGetter__("hump", function() {
	return this.replace(/_[a-z]/g, s => s.slice(1).capitalize());
});

String.prototype.protectReverseSolidus = function() {
	return this.replace(/\\/g, "\\\\").replace(/\n/g, "\\n");
};

String.prototype.toggleCase = function() {
	var array = [];
	for (var i = 0; i < this.length; ++i) {
		var ch = this[i];
		if (ch.islower())
			ch = ch.toUpperCase();
		else if (ch.isupper())
			ch = ch.toLowerCase();
		array.push(ch);
	}

	return array.join('');
};

String.prototype.executeReverseSolidus = function() {
	return this.replace(/\\n/g, "\n").replace(/\\\\/g, "\\");
};

String.prototype.ltrim = function(char) {
	if (char)
		return this.replace(new RegExp(`^[${char}]*`, 'g'), "");
	else
		return this.replace(/^\s*/g, "");
};

String.prototype.rtrim = function(char) {
	if (char)
		return this.replace(new RegExp(`[${char}]*$`, 'g'), "");
	else
		return this.replace(/\s*$/g, "");
};

String.prototype.strip = function() {
	return this.trim();
};

String.prototype.mysqlStr = function() {
	var text = this.replace(/'/g, "''").replace(/\\/g, "\\\\");
	return `'${text}'`;
};

String.prototype.back = function() {
	return this.slice(-1);
};

String.prototype.isdigit = function() {
	return /^\d+$/.test(this);
};

String.prototype.isChinese = function() {
	var chineseCharCount = 0;
	for (var ch of this) {
		if (XRegExp('\\p{Han}').test(ch))
			++chineseCharCount;
	}

	return chineseCharCount > this.length / 8;
};

String.prototype.isalpha = function() {
	return /^[a-zA-Z]+$/.test(this);
};

String.prototype.isupper = function() {
	return /^[A-Z]+$/.test(this);
};

String.prototype.islower = function() {
	return /^[a-z]+$/.test(this);
};

String.prototype.ispunct = function() {
	if (/^\s+$/.test(this))
		return false;
	return /^\W+$/.test(this);
};

String.prototype.fullmatch = function(regex){
	var {source} = regex;
	return this.match(
		new RegExp(
			`^(?:${source})$`,
			regex.ignoreCase? 'i': ''
		)
	);
};

String.prototype.isspace = function() {
	return /^\s+$/.test(this);
};

String.prototype.regexp = function(flags='') {
    return new RegExp(this, flags);
}

String.prototype.strlen = function() {
	return strlen(this);
};

String.prototype.isString = true;

NodeList.prototype.indexOf = function(e) {
	for (var i = 0; i < this.length; ++i) {
		if (this[i] == e)
			return i;
	}
	return -1;
};

NodeList.prototype.pop = function() {
	var lastChild = this[this.length - 1];
	lastChild.remove();
	return lastChild;
};

NodeList.prototype.shift = function() {
	var firstChild = this[0];
	firstChild.remove();
	return firstChild;
};

NodeList.prototype.reverse = function() {
	return [...this].reverse();
};

NodeList.prototype.splice = function() {
	var [index, howmany, ...items] = arguments;
	var deletes = [];
	if (index < 0)
		index = this.length + index;

	var parent = this[0].parentElement;

	for (var i = index; i < index + howmany; ++i) {
		deletes.push(this[i]);
	}

	for (let node of deletes) {
		node.remove();
	}

	if (items) {
		if (index == this.length) {
			for (let item of items)
				parent.appendChild(item);
		}
		else {
			var pivot = this[index];
			for (let item of items)
				parent.insertBefore(item, pivot);
		}
	}

	return this;
};

NodeList.prototype.slice = function(start, end) {
	return [...this].slice(start, end);
};

NodeList.prototype.back = function() {
	return this[this.length - 1];
};

NodeList.prototype.map = function(fn) {
	return [...this].map(fn);
};

NodeList.prototype.filter = function(fn) {
	return [...this].filter(fn);
};

HTMLCollection.prototype.slice = function(start, end) {
	var list = [...this];
	if (end < 0)
		end += list.length;

	if (start < 0)
		start += list.length;

	return list.slice(start, end);
};

HTMLCollection.prototype.indexOf = function(e) {
	for (var i = 0; i < this.length; ++i) {
		if (this[i] == e)
			return i;
	}
	return -1;
};

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Spread_syntax
HTMLCollection.prototype.splice = function() {
	var [index, howmany, ...items] = arguments;
	var deletes = [];
	if (index < 0)
		index = this.length + index;

	var parent = this[0].parentElement;

	for (var i = index; i < index + howmany; ++i) {
		deletes.push(this[i]);
	}

	for (let node of deletes) {
		node.remove();
	}

	if (items) {
		if (index == this.length) {
			for (let item of items)
				parent.appendChild(item);
		}
		else {
			var pivot = this[index];
			for (let item of items)
				parent.insertBefore(item, pivot);
		}
	}

	return this;
};

HTMLCollection.prototype.map = function(f) {
	return [...this].map(f);
};

HTMLCollection.prototype.filter = function(f) {
	return [...this].filter(f);
};

HTMLCollection.prototype.back = function() {
	return this[this.length - 1];
};

Array.prototype.equals = function(rhs){
	if (!Array.isArray(rhs))
		return false;

	if (this.length != rhs.length){
		return false;
	}

	for (let i = 0; i < rhs.length; ++i){
		if (!equals(this[i], rhs[i])){
			return false;
		}
	}

	return true;
};

Array.prototype.sum = function() {
	return sum(this);
};

Array.prototype.remove = function(item) {
	var index = this.indexOf(item);
	if (index >= 0)
		this.delete(index);
};

Array.prototype.delete = function(index, size) {
	if (size == null)
		return this.splice(index, 1)[0];
	return this.splice(index, size);
};

Array.prototype.clear = function() {
	this.splice(0, this.length);
};

Array.prototype.resize = function(newSize, defaultValue) {
    while (newSize > this.length)
        this.push(defaultValue);
    this.length = newSize;
};

Array.prototype.insert = function(index, value) {
	if (index == this.length)
		return this.push(value);

	if (index > this.length)
		this.push(...[null].repeat(index - this.length));

	return this.splice(index, 0, value);
};

Array.prototype.back = function(val) {
	if (val == null){
		return this[this.length - 1];
	}

	this[this.length - 1] = val;
};

Array.prototype.contains = function(val) {
	// return this.include(val);
	for (let obj of this){
		if (equals(obj, val)){
			return true;
		}
	}

	return false;
};

Array.prototype.all = function(func) {
	if (!func)
		func = obj => obj;
	return this.every(func);
};

Array.prototype.any = function(func) {
	if (!func)
		func = obj => obj;
	return this.some(func);
};

Array.prototype.enumerate = function*(func) {
	for (var i of range(this.length)){
		yield func(i, this[i]);
	}
};

Array.prototype.enumerated = function(func) {
	return [...this.enumerate(func)];
};

Array.prototype.repeat = function(count) {
	var array = [];
	for (var _ of range(count)){

		for (var el of this){
			if (Array.isArray(el)){
				el = [...el];
			}
			array.push(el);
		}
	}
	return array;
};

Array.prototype.swap = function(i, j) {
	[this[i], this[j]] = [this[j], this[i]];
	return this;
};

Array.prototype.sub = function(rhs){
	var ret = [];
	if (rhs.isArray) {
		for (let i = 0; i < rhs.length; ++i){
			ret[i] = this[i] == null? NaN: this[i].sub(rhs[i]);
		}
	}
	else {
		for (let i = 0; i < this.length; ++i){
			ret[i] = this[i] == null? NaN: this[i].sub(rhs);
		}
	}

	return ret;
};

Array.prototype.add = function(rhs){
	var ret = [];
	if (rhs.isArray) {
		for (let i = 0; i < rhs.length; ++i) {
			ret[i] = this[i].add(rhs[i]);
		}
	}
	else {
		for (let i = 0; i < this.length; ++i) {
			ret[i] = this[i].add(rhs);
		}
	}

	return ret;
};

Array.prototype.is_constant = function() {
	return this.all(b => b.equals(this[0]));
};

Array.prototype.isArray = true;

Array.prototype.compareTo = function(that) {
	for (var i = 0; i < this.length; ++i) {
		if (i < that.length) {
			var cmp = this[i].isArray? this[i].compareTo(that[i]): this[i].sub(that[i]).sign();
			if (cmp)
				return cmp;
		}
		else
			return 1;
	}
	return 0;
};

Array.prototype.mul = function(that){
	var ret = [];
	if (that.isArray) {
		console.assert(this.length == that.length, "this.length == rhs.length");

		for (let i = 0; i < this.length; ++i){
			ret[i] = this[i].mul(that[i]);
		}
	}
	else {
		for (let i = 0; i < this.length; ++i){
			ret[i] = this[i].mul(that);
		}
	}

	return ret;
};

Array.prototype.matmul = function(that){
	var rows = this.length;
	var cols = this[0].length;
	if (cols == null) {
		var _rows = that.length;
		if (rows == _rows) {
			var _cols = that[0].length;
			if (_cols == null) {
				var mat = 0;
				for (var k of range(_rows)) {
					mat = mat.add(this[k].mul(that[k]));
				}
			}
			else {
				var mat = [0].repeat(_cols);
				for (var j of range(_cols)) {
					for (var k of range(_rows)) {
						mat[j] = mat[j].add(this[k].mul(that[k][j]));
					}
				}
			}
		}
		else {
			throw Error("matrix size does not match");
		}
	}
	else {
		var _rows = that.length;
		if (cols == _rows) {
			var _cols = that[0].length;
			if (_cols == null) {
				var mat = [0].repeat(rows);
				for (var i of range(rows)) {
					for (var k of range(cols)) {
						mat[i] = mat[i].add(this[i][k].mul(that[k]));
					}
				}
			}
			else{
				var mat = [null].repeat(rows);
				for (var i of range(rows)) {
					mat[i] = [0].repeat(_cols);
					for (var j of range(_cols)) {
						for (var k of range(cols)) {
							mat[i][j] = mat[i][j].add(this[i][k].mul(that[k][j]));
						}
					}
				}
			}
		}
		else {
			throw Error("matrix size does not match");
		}
	}

	return mat;
};

Array.prototype.toRational = function() {
	return this.map(x => x.toRational());
};

Array.prototype.round = function() {
	return this.map(x => x.round());
};

Array.prototype.float = function() {
	return this.map(x => x.float());
};

Array.prototype.equal_range = function(value, compareTo) {
	if (!compareTo)
		compareTo = (a, b) => a.compareTo(b);

    var begin = 0, end = this.length;
    for (;;) {
        if (begin == end)
            break;

        var mid = begin + end >> 1;

        var ret = compareTo(this[mid], value);
        if (ret < 0)
            begin = mid + 1;
        else if (ret > 0)
            end = mid;
        else{
			var stop = begin - 1;
			begin = mid;
			for (;;){
				var pivot = -(-begin - stop >> 1);
				if (pivot == begin)
					break;

				if (compareTo(this[pivot], value))
					stop = pivot;
				else
					begin = pivot;
			}

			for (;;){
				var pivot = mid + end >> 1;
				if (pivot == mid)
					break;

				if (compareTo(this[pivot], value))
					end = pivot;
				else
					mid = pivot;
			}

			break;
		}
    }
    return [begin, end];
}

// Fisher-Yates (Knuth) Shuffle algorithm
Array.prototype.shuffle = function() {
    for (let i = this.length - 1; i > 0; --i) {
        // Generate a random index between 0 and i (inclusive)
        const j = randrange(i + 1);
        // Swap elements at indices i and j
        [this[i], this[j]] = [this[j], this[i]];
    }
	return this;
}

Array.prototype.clone = function() {
	return this.map(value => (typeof value?.clone === 'function')? value.clone() : value);
}

function compareTo(lhs, rhs) {
	if (lhs.isString)
		return compareTo(lhs.map(ch => ord(ch)), rhs.map(ch => ord(ch)));

	if (lhs.isArray) {
		for (var [lhs, rhs] of zip(lhs, rhs)) {
			var cmp = compareTo(lhs, rhs);
			if (cmp)
				return cmp;
		}

		return 0;
	}

	return lhs - rhs;
}

Array.prototype.binary_search = function(value, compareTo) {
	if (compareTo) {
		if (compareTo.length == 1) {
			var key = compareTo;
			compareTo = (lhs, rhs) => window.compareTo(key(lhs), key(rhs));
		}
	}
	else {
		compareTo = (a, b) => a.compareTo(b);
	}

    var begin = 0, end = this.length;
    for (;;) {
        if (begin == end)
            return begin;

        var mid = begin + end >> 1;

        var ret = compareTo(this[mid], value);
        if (ret < 0)
            begin = mid + 1;
        else if (ret > 0)
            end = mid;
        else
            return mid;
    }
}

Array.prototype.binary_insert = function(value, compareTo) {
	this.insert(this.binary_search(value, compareTo), value);
}

Array.prototype.max = function() {
	return max(this);
};

Array.prototype.array_diff = function (other) {
	if (!(other instanceof Set))
		other = new Set(other);

	return this.filter(x => !other.has(x));
}

Array.prototype.array_merge = function (other) {
	return [...new Set([...this, ...other])];
}

Array.prototype.array_assign = function (other) {
	this.length = 0;
	this.push(...other);
	// this.splice(0, this.length, ...other);
}

Array.prototype.array_intersect = function (other) {
	var set = [];
	if (!(other instanceof Set))
		other = new Set(other);
	for (let x of this) {
		if (other.has(x))
			set.push(x);
	}
	return set;
}

Set.prototype.array_diff = function (other) {
	return new Set([...this].array_diff(other));
}

Set.prototype.array_merge = function (other) {
	return new Set([...this, ...other]);
}

Set.prototype.array_intersect = function (other) {
	var set = new Set();
	for (let x of this) {
		if (other.has(x))
			set.add(x);
	}
	return set;
}

/**
 * @template T
 */
class Deque {
	/**
	 * @param {Iterable<T>=} items The initial elements. The actual logical list is represented as :
	 * [...itemsReversed.reverse(), ...items]
	 */
	constructor(items) {
		/** @private @type {T[]} */
		this._list = items ? Array.from(items) : [];
		/** @private @type {T[]} */
		this._listReversed = [];
		return new Proxy(this, {
			get(target, prop) {
				if (prop.isInteger)
					return target.at(Number(prop));
				return target[prop];
			}
		});
	}

	/**
	 * Returns the number of elements in this queue.
	 * @returns {number} The number of elements in this queue.
	 */
	get length() {
		return this._list.length + this._listReversed.length;
	}

	isEmpty() {
		return !this.length;
	}
	/**
	 * Appends the specified element to this queue.
	 * @param {T} item The element to add.
	 * @returns {void}
	 */
	push(...args) {
		this._list.push(...args);
	}

	unshift(...args) {
		this._listReversed.push(...args.reverse());
	}
	/**
	 * Retrieves and removes the head of this queue.
	 * @returns {T | undefined} The head of the queue of `undefined` if this queue is empty.
	 */
	shift() {
		if (this._listReversed.length === 0) {
			if (this._list.length === 0) return undefined;
			if (this._list.length === 1) return this._list.pop();
			if (this._list.length < 16) return this._list.shift();
			const temp = this._listReversed;
			this._listReversed = this._list.reverse();
			this._list = temp;
		}
		return this._listReversed.pop();
	}
	pop() {
        if (this._list.length === 0) {
            if (this._listReversed.length === 0) return undefined;
            if (this._listReversed.length === 1) return this._listReversed.pop();
            if (this._listReversed.length < 16) return this._listReversed.shift();
            const temp = this._list;
            this._list = this._listReversed.reverse();
            this._listReversed = temp;
        }
		return this._list.pop();
    }
	/**
	 * Finds and removes an item
	 * @param {T} item the item
	 * @returns {void}
	 */
	delete(item) {
		const i = this._list.indexOf(item);
		if (i >= 0) {
			this._list.splice(i, 1);
		} else {
			const i = this._listReversed.indexOf(item);
			if (i >= 0) this._listReversed.splice(i, 1);
		}
	}

	at(index) {
		const n = this.length;
		if (index < 0) index += n;
		if (index < 0 || index >= n) return undefined;
		const leftLen = this._listReversed.length;
		if (index < leftLen)
			return this._listReversed[leftLen - 1 - index];
		return this._list[index - leftLen];
	}

	*[Symbol.iterator]() {
		for (let i of range(this._listReversed.length - 1, -1, -1))
            yield this._listReversed[i];
        yield* this._list;
	}
}

class PriorityQueue {
    // default to a maximum heap;
    constructor(inputs) {
		if (typeof inputs == 'function'){
			this.pred = inputs;
			this.initialize_data();
			return;
		}

		if (Array.isArray(inputs)){
			this.init(true);
			var arr = inputs;
			this.make_heap(arr, arr.length);
			return;
		}

		this.init(inputs);
    }

	isEmpty() {
		return !this.length;
	}

	initialize_data() {
		this._list = [];
		this._Idx = 0; // used to look for the right kinder / parent.
	}

	init(bMaximumHeap){
        if (bMaximumHeap){
            this.pred = function(o1, o2) {
				if (o1 < o2)
					return -1;
				if (o1 > o2)
					return 1;
                return 0;
            };
		}
        else{
            this.pred = function(o1, o2) {
				if (o1 < o2)
					return 1;
				if (o1 > o2)
					return -1;
                return 0;
            };
		}

		this.initialize_data();
	}

	push(el){
		this._list.push(el);
	}

    make_heap(ptr, size) {
        for (var i = 0; i < size; ++i)
            this.push(ptr[i]);

        this.make_heap();
    }

    make_heap(arr) {
        for (var i = 0; i < arr.length; ++i)
            this.push(arr[i]);

        this.make_heap_nontrivial();
    }

    // make nontrivial [_First, _Last) into a heap, using pred
    make_heap_nontrivial() {
        var _Hole = this.length >> 1;
        while (0 < _Hole--)
            // reheap top half, bottom to top
            this.adjust_heap(_Hole);
    }

	get length() {
		return this._list.length;
	}
    // look for the right kinder _Idx * 2 + 2; remember the left kinder is
    // _Idx * 2 + 1, the right kinder might have exceed the array bound and
    // we might have failed to find the left kinder.
    shl() {
        ++this._Idx;
        this._Idx <<= 1;
        return this._Idx < this.length;
    }

	get(index){
		return this._list[index];
	}

	delete(index){
		return this._list.delete(index);
	}

	set(index, val){
		this._list[index] = val;
	}

    adjust_heap(_Hole) { // percolate _Hole to _Bottom, then push
                                 // _Val, using pred
        var _Val = this.get(_Hole);
        var _Top = _Hole;
        this._Idx = _Hole;
        while (this.shl()) { // move _Hole down to larger kinder
            if (this.pred(this.get(this._Idx), this.get(this._Idx - 1)) < 0)
                --this._Idx;
            this.set(_Hole, this.get(this._Idx));
            _Hole = this._Idx;
        }

        if (this._Idx == this.length) { // only kinder at bottom, move _Hole down to
                              // it
            --this._Idx;
            this.set(_Hole, this.get(this._Idx));
            _Hole = this._Idx;
        }
        return this.push_heap(_Top, _Hole, _Val);
    }

    shr(_Top) {// look for the right kinder (_Idx - 1) /
                                   // 2; remember the left kinder is _Idx *
                                   // 2 + 1, the right kinder might have
                                   // exceed the array bound and we might
                                   // have failed to find the left kinder.
        if (_Top < this._Idx) {
            --this._Idx;
            this._Idx >>= 1;
            return true;
        }
        return false; // what happens if _Idx <= _Top ? then the parent of
                      // _Idx will locate before _Top, which is not
                      // supposed to be done;
    }

    push_heap(_Top, _Hole, _Val) { // percolate _Hole to
                                                   // _Top or where _Val
                                                   // belongs
        this._Idx = _Hole;
        while (this.shr(_Top) && this.pred(this.get(this._Idx), _Val) < 0) {// move
                                                                // _Hole up
                                                                // to parent
            this.set(_Hole, this.get(this._Idx));
            _Hole = this._Idx;
        }
        this.set(_Hole, _Val);// drop _Val into final hole
        return _Hole;
    }

	shift() {
		this._list.shift();
	}

    // dequeue operator
    // pop *_First to *(_Last - 1) and reheap, using pred
    pop(i) {
		if (i == null){
	        if (this.length == 0)
	            return null;
	        var _Val = this.get(0);
	        if (this.length == 1) {
				this.shift();
	            return _Val;
	        }

	        this.set(0, this.get(this.length - 1));
	        this.delete(this.length - 1);
	        this.adjust_heap(0);
	        return _Val;
		}

        var _Val = this.get(i);

        var end = this.get(this.length - 1);
        this.delete(this.length - 1);
        if (i != this.length) {
            this.set(i, end);
            this.adjust_heap(i);
        }
        return _Val;
    }

    // enqueue operator
    push(_Val) {
        this._list.push(_Val);
        var _Hole = this.push_heap(0, this.length - 1, _Val);
        return _Hole;
    }

    reset(i, _Val) {
        // allow i to equal size??
        this._list[i] = _Val;
        return this.adjust_heap(i);
    }

    peek() {
        if (this.length == 0)
            return null;
        return this.get(0);
    }
}

function params(href) {
	var search;
	if (href != null) {
		search = href.slice(href.indexOf('?'));
	}
	else {
		search = location.search;
	}

	var kwargs = {};
	var query = search.substring(1);
	var vars = query.split("&");
	for (var i = 0; i < vars.length; ++i) {
		var pair = vars[i].split("=");
		kwargs[pair[0]] = pair[1];
	}

	return kwargs;
}

function* items(dict) {
	for (let k in dict) {
		yield [k, dict[k]];
	}
}

function join(sep, generator) {
	return list(generator).join(sep);
}

function list(obj) {
	if (obj.constructor == Function) {
		var arr = [];
		for (let e of obj) {
			arr.push(e);
		}
		return arr;
	}
	var array = [];
	for (var key in obj) {
		if (key.isInteger)
			array[key] = obj[key];
		else
			return obj;
	}
	return array;
}

function* map(fn, generator) {
	for (let e of generator) {
		yield fn(e);
	}
}

function mapped(fn, generator) {
	return [...map(fn, generator)];
}

function cmp(x, y) {
	// If both x and y are null or undefined and exactly the same
	if (x === y) {
		return true;
	}

	// If they are not strictly equal, they both need to be Objects
	if (!(x instanceof Object) || !(y instanceof Object)) {
		return false;
	}

	// They must have the exact same prototype chain,the closest we can do is
	// test the constructor.
	if (x.constructor !== y.constructor) {
		return false;
	}

	for (var p in x) {
		// Inherited properties were tested using x.constructor ===
		// y.constructor
		if (x.hasOwnProperty(p)) {
			// Allows comparing x[ p ] and y[ p ] when set to undefined
			if (!y.hasOwnProperty(p)) {
				return false;
			}

			// If they have the same strict value or identity then they are
			// equal
			if (x[p] === y[p]) {
				continue;
			}

			// Numbers, Strings, Functions, Booleans must be strictly equal
			if (typeof (x[p]) !== "object") {
				return false;
			}

			// Objects and Arrays must be tested recursively
			if (!cmp(x[p], y[p])) {
				return false;
			}
		}
	}

	for (var p in y) {
		// allows x[ p ] to be set to undefined
		if (y.hasOwnProperty(p) && !x.hasOwnProperty(p)) {
			return false;
		}
	}
	return true;
};

function quote_html(param) {
	return param.replace(/&/g, "&amp;").replace(/'/g, "&apos;").replace(/\\/, "\\\\");
}

function str_html(param) {
	return param.replace(/&/g, "&amp;").replace(/<(?=[a-zA-Z!/])/g, "&lt;");
}

function quote(param) {
	return param.replace(/\\/, "\\\\").replace(/'/g, "\\'");
}

function isEnglish(ch) {
	return ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z' || ch >= 'ａ' && ch <= 'ｚ' || ch >= 'Ａ' && ch <= 'Ｚ'
		|| ch >= '0' && ch <= '9' || ch >= '０' && ch <= '９';
}

function getClass(o) {
	return Object.prototype.toString.call(o).slice(8, -1);
}

function intersection(s1, s2) {
	var s = new Set();
	for (let e of s1) {
		if (s2.has(e)) {
			s.add(e);
		}
	}
	return s;
}

function deepCopy(obj, excludes) {
	var result, oClass = getClass(obj);

	if (oClass == "Object")
		result = {};
	else if (oClass == "Array") {
		result = [];

		for (var copy of obj) {
			if (getClass(copy) == "Object")
				result.push(deepCopy(copy, excludes));
			else if (getClass(copy) == "Array")
				result.push(deepCopy(copy, excludes));
			else
				result.push(copy);
		}

		return result;
	}
	else
		return obj;

	for (var i in obj) {
		var copy = obj[i];
		if (excludes && excludes.contains(i))
			result[i] = copy;
		else if (getClass(copy) == "Object")
			result[i] = deepCopy(copy, excludes);
		else if (getClass(copy) == "Array")
			result[i] = deepCopy(copy, excludes);
		else
			result[i] = copy;
	}

	if (obj.__proto__)
		result.__proto__ = obj.__proto__;
	return result;
}


HTMLElement.prototype.getScrollTop = function() {
	var scrollTop = 0;

	var current = this;
	while (current !== null) {
		scrollTop += current.scrollTop;
		current = current.parentElement;
	}

	return scrollTop;
};

HTMLElement.prototype.getOffsetTop = function() {
	var offsetTop = 0;

	var current = this;
	while (current !== null) {
		offsetTop += current.offsetTop;
		current = current.offsetParent;
	}

	return offsetTop;
};

HTMLElement.prototype.getScrollLeft = function() {
	var scrollLeft = 0;

	var current = this;
	while (current !== null) {
		scrollLeft += current.scrollLeft;
		current = current.parentElement;
	}

	return scrollLeft;
};

HTMLElement.prototype.getOffsetLeft = function() {
	var offsetLeft = 0;

	var current = this;
	while (current !== null) {
		offsetLeft += current.offsetLeft;
		current = current.offsetParent;
	}

	return offsetLeft;
};

HTMLElement.prototype.coordinate = function(rate_x, rate_y) {
	var rect = this.getBoundingClientRect();
	return [rect.x + rect.width * rate_x, rect.y + rect.height * rate_y];
};

HTMLElement.prototype.contain = function(x0, y0) {
	var rect = this.getBoundingClientRect();
	return x0 >= rect.x && x0 < rect.x + rect.width && y0 >= rect.y && y0 < rect.y + rect.height;
};

HTMLElement.prototype.center = function() {
	return this.coordinate(0.5, 0.5);
};

HTMLElement.prototype.distance = function(rhs) {
	var [x0, y0] = this.center();
	if (!Array.isArray(rhs))
		rhs = rhs.center();

	var [x1, y1] = rhs;
	return distance(x0, y0, x1, y1);
};

HTMLElement.prototype.hiddenStatus = function() {
    const {scrollLeft, scrollTop, clientWidth, clientHeight} = document.documentElement;
    var offsetLeft = this.getOffsetLeft() - scrollLeft;
    var offsetTop = this.getOffsetTop() - scrollTop;
	var {offsetWidth, offsetHeight} = this;

    var hidden = {};
    if (offsetTop < 0)
    	hidden.y = offsetTop;
    else if (offsetTop + offsetHeight > clientHeight)
    	hidden.y = offsetTop + offsetHeight - clientHeight;

    if (offsetLeft < 0)
    	hidden.x = offsetLeft;
    else if (offsetLeft + offsetWidth > clientWidth)
    	hidden.x = offsetLeft + offsetWidth - clientWidth;
    return hidden;
};

function intersects(rectA, rect) {
	function intersects(rangeA, rangeB){
		var [a0, b0] = rangeA;
		var [a1, b1] = rangeB;
		return Math.max(a0, a1) < Math.min(b0, b1);
	}

	return intersects([rect.x, rect.x + rect.width], [rectA.x, rectA.x + rectA.width]) && intersects([rect.y, rect.y + rect.height], [rectA.y, rectA.y + rectA.height]);
}

function merge_sort(arr1, arr2, compareTo, ret) {
	if (ret == null){
		ret = [];
	}

	if (compareTo == null){
		compareTo = (a, b) => a.compareTo(b);
	}

    _merge_sort(arr1, arr1.length, arr2, arr2.length, compareTo, ret);

    return ret;
}

// precondition: the destine array is not the same as the source arrays;
function _merge_sort(arr1, sz1, arr2, sz2, compareTo, dst) {
    var i = 0, j = 0, k = 0;
    while (i < sz1 && j < sz2) {
        if (compareTo(arr1[i], arr2[j]) < 0)
            dst[k++] = arr1[i++];
        else
            dst[k++] = arr2[j++];
    }

    while (i < sz1)
        dst[k++] = arr1[i++];

    while (j < sz2)
        dst[k++] = arr2[j++];
}


function toUnicodeDigit(digits){
    var diff = ord('０') - ord('0');
    var ret = '';
    for (let i = 0; i < digits.length; ++i){
        ret += chr(ord(digits[i]) + diff);
    }
    return ret;
}

function array_push() {
	var [arr, ...keys] = arguments;
	var value = keys.pop();
	for (let key of keys){
		if (arr[key] == null){
			arr[key] = [];
		}

		arr = arr[key];
	}

	arr.push(value);
}


function compare_debug(obj, _obj){
	console.log(obj, _obj, "are not equal!");

    if (obj instanceof Object && _obj instanceof Object){
        if (Object.keys(obj).length != Object.keys(_obj).length){
			console.log("keys lengths are not equal!");
			console.log(Object.keys(obj));
			console.log(Object.keys(_obj));
            return;
        }

        for (var [key, v] of Object.entries(obj)){
            var _v = _obj[key];
            if (equals(v, _v))
                continue;

            console.log("difference at key", key);
            compare_debug(v, _v);
		}
	}
    else if (obj instanceof Array && _obj instanceof Array){
        if (obj.length != _obj.length){
			console.log("lengths are not equal!");
			console.log(obj.length, _obj.length);
			return;
		}

        for (let i = 0; i < obj.length; ++i){
            if (equals(obj[i], _obj[i]))
                continue;

            console.log("difference at index", i);
            compare_debug(obj[i], _obj[i]);
		}
	}
}

function sunday(haystack, needle, offsetStart) {

	if (offsetStart == null)
		offsetStart = 0;

    var needelLength = needle.length;

    var haystackLength = haystack.length;

	var dic = {};
	for (var k = 0; k < needle.length; ++k){
		var v = needle[k];
		dic[v] = needelLength - k;
	}

    var end = needelLength + offsetStart;
    var begin, offset;

    while (end <= haystackLength) {
        begin = end - needelLength;
        if (equals(haystack.slice(begin, end), needle))
            return begin;

        if (end >= haystackLength)
            return -1;

        offset = dic[haystack[end]];
        if (!offset)
            offset = needelLength + 1;

        end += offset;
	}
    return -1;

}

function distance() {
	if (arguments.length == 4)
		var [x0, y0, x1, y1] = arguments;
	else if (arguments.length == 2)
		var [[x0, y0], [x1, y1]] = arguments;
	else
		throw new Error("arguments.length == 2 || arguments.length == 4");

	var dx = x1.sub(x0);
	var dy = y1.sub(y0);
	return dx.mul(dx).add(dy.mul(dy)).sqrt();
}

function mean(p0, p1, rate) {
	if (rate == null)
		rate = new Rational(1n, 2n);

	return p0.mul(rate.neg().add(1n)).add(p1.mul(rate));
}

function sum(array) {
	return array.reduce((a, b)=> a.add(b), 0);
}

function max(arr){
	var arr = arguments.length == 1? arguments[0]: [...arguments];
	return arr.reduce((a, b) => b.gt(a) ? b: a, -Infinity);
}

function min() {
	var arr = arguments.length == 1? arguments[0]: [...arguments];
	return arr.reduce((a, b) => b.lt(a) ? b: a, Infinity);
}

function prod(array){
	return array.reduce((a, b)=> a * b, 1);
}

function *from() {
	for (var domain of arguments){
		yield* domain;
	}
}

function ranged(start, stop, step){
	return [...range(start, stop, step)];
}

function *range(start, stop, step){
	if (step == null){
		if (stop == null){
			yield* Array(start).keys();
		}
		for (var i = start; i < stop; ++i){
			yield i;
		}
	}
	else{
		if (step > 0){
			for (var i = start; i < stop; i += step){
				yield i;
			}
		}
		else{
			for (var i = start; i > stop; i += step){
				yield i;
			}
		}
	}
}

class SymbolicSet {
	sanctity_check() {
	}

	symmetric_difference(that){
		return this.union(that).complement(this.intersects(that));
	}

	jaccard(that){
		return this.intersects(that).card / this.union(that).card;
	}

	contains(that){
		return this.intersects(that).equals(that);
	}

	get bbox() {
		if (!this._bbox)
			this._bbox = this._eval_bbox();
		return this._bbox;
	}

	complement(that) {
		if (that.is_EmptySet)
			return this;

		if (that.is_Union) {
			var args = [];
			for (var arg of that.args) {
				var arg = this.complement(arg);
				if (arg.is_Complement)
					break;

				args.push(arg);
			}

			if (args.length == that.args.length)
				return args.reduce((a, b) => a.intersects(b));
		}

		return new Complement(this, that);
	}
}

class EmptySet extends SymbolicSet {
	get is_EmptySet() {
		return true;
	}

	get card() {
		return 0;
	}

	equals(that){
		return that == null || that.is_EmptySet;
	}

	complement(that) {
		return this;
	}

	add(offset){
		return this;
	}

	union(that){
		return that;
	}

	symmetric_difference(that){
		return that;
	}

	intersects(that){
		return this;
	}

	get args() {
		return [];
	}

	[Symbol.iterator]() {
		return {
			next() {
				return {done: true};
			}
		};
	}
}

class Union extends SymbolicSet {
	static new() {
		if (!arguments.length)
			return new EmptySet;

		if (arguments.length == 1)
			return arguments[0];

		return new Union(...arguments);
	}

	get is_Union() {
		return true;
	}

	sanctity_check() {
		for (var arg of this.args) {
			if (arg.is_EmptySet || arg.is_Union) {
				console.log(arg);
				return true;
			}
			console.assert(!arg.is_EmptySet && ! arg.is_Union, "arg.is_EmptySet");
		}
		return false;
	}

	constructor() {
		super();
		this.args = [...arguments];
	}

	get card() {
		var card = 0;
		for (var arg of this.args){
			card = card.add(arg.card);
		}
		return card;
	}

	intersects(that){
		if (that.is_EmptySet)
			return that;

		var args = [];
		if (that.is_Range) {
			for (var i of range(...this.args.equal_range(that))) {
				var arg = this.args[i];
				arg = arg.intersects(that);
				console.assert(arg.is_Range, "arg.is_Range");
				args.push(arg);
			}
		}
		else {
			for (var arg of this.args) {
				arg = arg.intersects(that);
				if (arg.is_EmptySet)
					continue;

				if (arg.is_Union)
					args.push(...arg.args);
				else
					args.push(arg);
			}
		}

		return Union.new(...args);
	}

	equals(that){
		if (that && that.is_Union && this.args.length == that.args.length){
			for (var i = 0; i < this.args.length; ++i){
				if (!this.args[i].equals(that.args[i]))
					return false;
			}
			return true;
		}
	}

	complement(that) {
		var args = [];
		for (var arg of this.args){
			arg = arg.complement(that);
			if (arg.is_EmptySet)
				continue;

			if (arg.is_Union){
				args.push(...arg.args);
			}
			else{
				args.push(arg);
			}
		}

		return Union.new(...args);
	}

	add(offset){
		return new Union(...this.args.map(el => el.add(offset)));
	}

	union(that){
		if (that.is_EmptySet){
			return this;
		}

		if (that.is_Range){
			for (var i = 0; i < this.args.length; ++i){
				var arg = this.args[i];
				arg = arg.union(that);
				if (arg.is_Range){
					args = [...this.args];
					args.delete(i);
					if (args.length == 1){
						return args[0].union(arg);
					}

					return new Union(...args).union(arg);
				}
			}

			var args = [...this.args];
			var index = args.binary_search(that);

			args.insert(index, that);

			return new Union(...args);
		}
		else if (that.is_Rectangle){
			for (var i = 0; i < this.args.length; ++i){
				var arg = this.args[i];
				arg = arg.union(that);
				if (arg.is_Rectangle){
					args = [...this.args];
					args.delete(i);
					if (args.length == 1){
						return args[0].union(arg);
					}

					return new Union(...args).union(arg);
				}
			}

			var args = [...this.args];
			args.insert(args.binary_search(that), that);

			return new Union(...args).try_union();
		}
		else if (that.is_Trapezoid){
			for (var i = 0; i < this.args.length; ++i){
				var arg = this.args[i];
				arg = arg.union(that);
				if (!arg.is_Union){
					args = [...this.args];
					args.delete(i);
					if (args.length == 1){
						return args[0].union(arg);
					}

					return new Union(...args).union(arg);
				}
			}

			var args = [...this.args];
			args.insert(args.binary_search(that), that);

			return new Union(...args);
		}

		for (var arg of this.args){
			that = that.union(arg)
		}
		return that;
	}

	union_without_merging(that){
		if (that.is_EmptySet)
			return this;

		if (that.is_Range){
            for (var arg of this.args)
                that = that.complement(arg);

			if (that.is_EmptySet)
				return this;

            if (that.is_Range)
                that = [that];
            else
                that = that.args;

			var args = [...this.args];
			for (var that of that)
				args.insert(args.binary_search(that), that);

			return new Union(...args);
		}

        if (that.is_Union) {
			var self = this;
            for (var arg of that.args) {
                self = self.union_without_merging(arg);
            }
            return self;
		}
	}

	sliced(obj){
		return this.args.map(domain => domain.sliced(obj)).join('\t');
	}

	nonoverlapping_check() {
		for (var j of range(1, this.args.length)) {
			for (var i of range(j)) {
				console.assert(this.args[i].intersects(this.args[j]).is_EmptySet, "args[i].intersects(args[j]).is_EmptySet");
			}
		}
	}

	try_union() {
		//http://localhost/axiom/?module=Set.eq_card.subset.then.eq
		var bbox = this.bbox;
		return this.card == bbox.card ? bbox: this;
	}

	_eval_bbox() {
		var x_min = Infinity;
		var y_min = Infinity;
		var x_max = -Infinity;
		var y_max = -Infinity;
		for (var rect of this.args) {
			rect = rect.bbox;
			x_min = min(x_min, rect.x);
			y_min = min(y_min, rect.y);
			x_max = max(x_max, rect.x_stop);
			y_max = max(y_max, rect.y_stop);
		}

		return new Rectangle(x_min, y_min, x_max.sub(x_min), y_max.sub(y_min));
	}

	offset(dx, dy) {
		return new Union(...this.args.map(s => s.offset(dx, dy)));
	}
}

class Intersection extends SymbolicSet {
	get is_Intersection() {
		return true;
	}

	constructor() {
		super();
		this.args = [...arguments];
	}

	get card() {
	}

	union(that){
		if (that.is_EmptySet){
			return this;
		}

		var args = [];
		for (var arg of this.args){
			arg = arg.union(that);

			if (arg.is_Intersection){
				args.push(...arg.args);
			}
			else{
				args.push(arg);
			}
		}

		if (!args.length)
			return new EmptySet;

		if (args.length == 1)
			return args[0];

		return new Intersection(...args);
	}

	equals(that) {
		if (that && that.is_Intersection && this.args.length == that.args.length){
			for (var i = 0; i < this.args.length; ++i){
				if (!this.args[i].equals(that.args[i]))
					return false;
			}
			return true;
		}
	}

	complement(that) {
		var args = [];
		for (var arg of this.args){
			arg = arg.complement(that);
			if (arg.is_EmptySet)
				continue;

			if (arg.is_Intersection){
				args.push(...arg.args);
			}
			else{
				args.push(arg);
			}
		}

		if (!args.length)
			return new EmptySet;

		if (args.length == 1)
			return args[0];

		return new Intersection(...args);
	}

	add(offset){
		return new Intersection(...this.args.map(el => el.add(offset)));
	}

	intersects(that){
		if (that.is_EmptySet){
			return that;
		}

		for (var arg of this.args){
			that = that.intersects(arg);
		}
		return that;
	}

	_eval_bbox() {
	}

	static new() {
		var args = [...arguments];
		return new Intersection(...args.sort((a, b)=> a.compareTo(b)));
	}
}

class Complement extends SymbolicSet {
	get is_Complement() {
		return true;
	}

	constructor() {
		super();
		this.args = [...arguments];
	}

	get card() {
	}

	union(that){
		if (that.is_EmptySet){
			return this;
		}
	}

	equals(that) {
		if (that && that.is_Complement){
			for (var i = 0; i < this.args.length; ++i){
				if (!this.args[i].equals(that.args[i]))
					return false;
			}
			return true;
		}
	}

	complement(that) {
	}

	add(offset){
		return new Complement(...this.args.map(el => el.add(offset)));
	}

	intersects(that){
	}

	_eval_bbox() {
	}
}

class Range extends SymbolicSet {
	get is_Range() {
		return true;
	}

	constructor(start, stop){
		super();
		this.start = start;
		this.stop = stop;
	}

	get args() {
		return [this.start, this.stop];
	}

	intersects(that){
		if (that.is_Union)
			return that.intersects(this);

		var {start, stop} = that;
		if (start >= this.stop || stop <= this.start)
			return new EmptySet;

		return new Range(Math.max(this.start, start), Math.min(this.stop, stop));
	}

	equals(that){
		if (that && that.is_Range){
			return this.start == that.start && this.stop == that.stop;
		}
	}

	union(that){
		if (that.is_Range){
			var {start, stop} = that;
			if (start > this.stop)
				return new Union(this, that);

			if (stop < this.start)
				return new Union(that, this);

			return new Range(Math.min(this.start, start), Math.max(this.stop, stop));
		}

		if (that.is_EmptySet)
			return this;

		return that.union(this);
	}

	contains(pt) {
		if (pt.is_Range)
			return pt.start >= this.start && pt.stop <= this.stop;
		else
			return pt >= this.start && pt < this.stop;
	}

	union_without_merging(that){
		if (that.is_EmptySet)
			return this;

		if (that.is_Range){
			var {start, stop} = that;
			if (start >= this.stop)
				return new Union(this, that);

			if (stop <= this.start)
				return new Union(that, this);

			var mid = this.intersects(that);
			var lhs = this.complement(that);
            var rhs = that.complement(this);
	        if (rhs.is_EmptySet)
                return mid.union_without_merging(lhs);

            if (lhs.is_EmptySet)
                return mid.union_without_merging(rhs);

            if (lhs.start > rhs.start)
                [lhs, rhs] = [rhs, lhs];

            return new Union(lhs, mid, rhs);
		}

		return that.union_without_merging(this);
	}

	complement(that) {
		if (that.start >= this.stop)
			return this;

		if (that.start > this.start){
			//now that that.start < this.stop
			if (that.stop >= this.stop)
				return new Range(this.start, that.start);

			//now that that.stop < this.stop
			return new Union(new Range(this.start, that.start), new Range(that.stop, this.stop));
		}
		else{
			//now that that.start <= this.start
			if (that.stop >= this.stop)
				return new EmptySet;

			//now that that.stop < this.stop
			if (that.stop > this.start)
				return new Range(that.stop, this.stop);

			return new Range(this.start, this.stop);
		}
	}

	get card() {
		return this.stop - this.start;
	}

	add(offset){
		return new Range(this.start + offset, this.stop + offset);
	}

	sliced(obj){
		return obj.slice(this.start, this.stop);
	}

	[Symbol.iterator]() {
		var {start, stop} = this;

		return {
			next() {
				if (start == stop)
					return {done: true};

				return {value: start++};
			}
		};
	}

	compareTo(that) {
		if (this.stop <= that.start)
			return -1;

		if (that.stop <= this.start)
			return 1;

		return 0;
	}
}

class Polygon extends SymbolicSet {
	clearImage(ctx, fillStyle) {
		var oldStyle = ctx.fillStyle;
		ctx.fillStyle = fillStyle;
		var p = this.p.map(p => p.map(e => e.round()));
		ctx.moveTo(...p[0]);

		for (var i of range(1, this.p.length)) {
			ctx.lineTo(...p[i]);
		}

		ctx.lineTo(...p[0]);
		ctx.fill();
		ctx.fillStyle = oldStyle;
	}

	get p() {
		if (!this._p) {
			this._p = this._eval_p();
		}
		return this._p;
	}

	get is_Polygon() {
		return true;
	}

	distance(x0, y0) {
		return distance(this.anchorPoint(x0, y0), [x0, y0]);
	}

	complement(that) {
		return SymbolicSet.prototype.complement.apply(this, arguments);
	}

	static is_straight_line() {
		for (var i of range(2, arguments.length)) {
			if (!new Triangle(arguments[i - 2], arguments[i - 1], arguments[i]).is_straight_line())
				return false;
		}
		return true;
	}
}

class Tetragon extends Polygon {
	get is_Tetragon() {
		return true;
	}

	contains() {
		var {p} = this;
		var pt = arguments.length == 2 ? arguments: arguments[0];
		var delta0 = new Triangle(p[0], p[1], pt).direction();
		var delta1 = new Triangle(p[1], p[2], pt).direction();
		var delta2 = new Triangle(p[2], p[3], pt).direction();
		var delta3 = new Triangle(p[3], p[0], pt).direction();
		return delta0.is_positive && delta1.is_positive && delta2.is_positive && delta3.is_positive;
	}

	static new() {
		if (arguments.length >= 4)
			return new Rectangle(...arguments);
		return Trapezoid.new(...arguments);
	}

	is_nonoverlapping(that) {
		var {p} = that;
		if (p.any(pt => this.contains(pt)))
			return false;

		var {p: points} = this;
		var dir01 = points.map(pt => new Triangle(p[0], p[1], pt).direction().sign());
		var dir32 = points.map(pt => new Triangle(p[3], p[2], pt).direction().sign());
		if (dir01.is_constant() && dir32.is_constant() && dir01[0] == dir32[0])
			return true;

		var dir12 = points.map(pt => new Triangle(p[1], p[2], pt).direction().sign());
		var dir03 = points.map(pt => new Triangle(p[0], p[3], pt).direction().sign());
		if (dir12.is_constant() && dir03.is_constant() && dir12[0] == dir03[0])
			return true;
	}

	intersects(that) {
		if (that.is_EmptySet)
			return that;

		if (that.is_Parallelogram || that.is_Rectangle) {
			if (this.bbox.intersects(that).is_EmptySet)
				return new EmptySet;

			if (this.is_nonoverlapping(that))
				return new EmptySet;

			return Intersection.new(that, this);
		}

		if (that.is_Trapezoid) {
			var cmp = this.compareTo(that);
			if (cmp > 0)
				return that.intersects(this);

			if (this.y[1] <= that.y[0])
				return new EmptySet;

			if (that.p.any(pt => this.contains(pt)) || this.p.any(pt => that.contains(pt)))
				return Intersection.new(this, that);

			return new EmptySet;
		}

		return new Intersection(that, this);
	}

	complement(that) {
		return Polygon.prototype.complement.apply(this, arguments);
	}
}

class Rectangle extends Tetragon {
	get is_Rectangle() {
		return true;
	}

	constructor() {
		super();
		if (arguments.length == 4)
			var [x, y, width, height] = arguments;
		else if (arguments.length == 1){
			var {x, y, width, height} = arguments[0];
		}

		this.args = [x, y, width, height];
	}

	get x() {
		return this.args[0];
	}

	set x(x) {
		this.args[0] = x;
	}

	get y() {
		return this.args[1];
	}

	set y(y) {
		this.args[1] = y;
	}

	get width() {
		return this.args[2];
	}

	set width(width) {
		this.args[2] = width;
	}

	get height() {
		return this.args[3];
	}

	set height(height) {
		this.args[3] = height;
	}

	get x_stop() {
		return this.x.add(this.width);
	}

	set x_stop(x_stop) {
		this.width = x_stop.sub(this.x);
	}

	get y_stop() {
		return this.y.add(this.height);
	}

	set y_stop(y_stop) {
		this.height = y_stop.sub(this.y);
	}

	intersects(that){
		if (that.is_Union || that.is_Parallelogram || that.is_Trapezoid)
			return that.intersects(this);

		var {x, y, x_stop, y_stop} = that;
		if (x.ge(this.x_stop) || x_stop.le(this.x) || y.ge(this.y_stop) || y_stop.le(this.y))
			return new EmptySet;

		var x = max(this.x, x);
		var x_stop = min(this.x_stop, x_stop);

		var y = max(this.y, y);
		var y_stop = min(this.y_stop, y_stop);

		var width = x_stop.sub(x);
		var height = y_stop.sub(y);
		return new Rectangle(x, y, width, height);
	}

	equals(that){
		if (that && that.is_Rectangle){
			return this.x == that.x && this.width == that.width && this.y == that.y && this.height == that.height;
		}
	}

	union(that){
		if (that.is_Rectangle) {
			var {x, y, x_stop, y_stop} = that;
			if (x == this.x && x_stop == this.x_stop){
				if (y == this.y_stop)
					return new Rectangle(this.x, this.y, this.width, this.height + that.height);
				if (this.y == y_stop)
					return new Rectangle(x, y, this.width, this.height + that.height);
			}
			else if (y == this.y && y_stop == this.y_stop){
				if (x == this.x_stop)
					return new Rectangle(this.x, this.y, this.width + that.width, this.height);
				if (this.x == x_stop)
					return new Rectangle(x, y, this.width + that.width, this.height);
			}

			return new Union(this, that);
		}

		if (that.is_EmptySet)
			return this;

		return that.union(this);
	}

	complement(that) {
		if (that.is_Rectangle){
			if (that.x >= this.x_stop || that.y >= this.y_stop || that.x_stop <= this.x || that.y_stop <= this.y)
				return this;

			// that.x < this.x_stop && that.x_stop > this.x
			// that.y < this.y_stop && that.y_stop > this.y
			if (that.x <= this.x){
				if (that.x_stop < this.x_stop) {
					//that.x <= this.x && that.x_stop < this.x_stop
					if (that.y <= this.y){
						if (that.y_stop < this.y_stop)
							//that.y <= this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, that.y_stop, this.width, this.y_stop - that.y_stop),
								new Rectangle(that.x_stop, this.y, this.x_stop - that.x_stop, that.y_stop - this.y));
						else
							//that.y <= this.y && that.y_stop >= this.y_stop
							return new Rectangle(that.x_stop, this.y, this.x_stop - that.x_stop, this.height);
					}
					else {
						if (that.y_stop < this.y_stop)
							//that.y > this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y_stop, this.width, this.y_stop - that.y_stop),
								new Rectangle(that.x_stop, that.y, this.x_stop - that.x_stop, that.height));
						else
							//that.y > this.y && that.y_stop >= this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(that.x_stop, that.y, this.x_stop - that.x_stop, this.y_stop - that.y));
					}
				}
				else {
					//that.x <= this.x && that.x_stop >= this.x_stop
					if (that.y <= this.y){
						if (that.y_stop < this.y_stop)
							//that.y <= this.y && that.y_stop < this.y_stop
							return new Rectangle(this.x, that.y_stop, this.width, this.y_stop - that.y_stop);
						else
							//that.y <= this.y && that.y_stop >= this.y_stop
							return new EmptySet;
					}
					else {
						if (that.y_stop < this.y_stop)
							//that.y > this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y_stop, this.width, this.y_stop - that.y_stop));
						else
							//that.y > this.y && that.y_stop >= this.y_stop
							return new Rectangle(this.x, this.y, this.width, that.y - this.y);
					}
				}
			}
			else {
				if (that.x_stop < this.x_stop) {
					//that.x > this.x && that.x_stop < this.x_stop
					if (that.y <= this.y){
						if (that.y_stop < this.y_stop)
							//that.y <= this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, that.x - this.x, this.height),
								new Rectangle(that.x, that.y_stop, this.x_stop - that.x, this.y_stop - that.y_stop),
								new Rectangle(that.x_stop, this.y, this.x_stop - that.x_stop, that.y_stop - this.y));
						else
							//that.y <= this.y && that.y_stop >= this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, that.x - this.x, this.height),
								new Rectangle(that.x_stop, this.y, this.x_stop - that.x_stop, that.height));
					}
					else {
						if (that.y_stop < this.y_stop)
							//that.y > this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y, that.x - this.x, this.y_stop - that.y),
								new Rectangle(that.x, that.y_stop, this.x_stop - this.x, this.y_stop - that.y_stop),
								new Rectangle(that.x_stop, that.y, this.x_stop - that.x_stop, that.height));
						else
							//that.y > this.y && that.y_stop >= this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y, that.x - this.x, this.y_stop - that.y),
								new Rectangle(that.x_stop, that.y, this.x_stop - that.x_stop, this.y_stop - that.y));
					}
				}
				else {
					//that.x > this.x && that.x_stop >= this.x_stop
					if (that.y <= this.y){
						if (that.y_stop < this.y_stop)
							//that.y <= this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, that.x - this.x, this.height),
								new Rectangle(that.x, that.y_stop, this.x_stop - that.x, this.y_stop - that.y_stop));
						else
							//that.y <= this.y && that.y_stop >= this.y_stop
							return new Rectangle(this.x, this.y, that.x - this.x, this.height);
					}
					else {
						if (that.y_stop < this.y_stop)
							//that.y > this.y && that.y_stop < this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y, that.x - this.x, this.y_stop - that.y),
								new Rectangle(that.x, that.y_stop, this.x_stop - this.x, this.y_stop - that.y_stop));
						else
							//that.y > this.y && that.y_stop >= this.y_stop
							return new Union(
								new Rectangle(this.x, this.y, this.width, that.y - this.y),
								new Rectangle(this.x, that.y, that.x - this.x, this.y_stop - that.y));
					}
				}
			}
		}

		if (that.is_EmptySet){
			return this;
		}

		if (that.is_Union){
			var self = this;
			for (var region of that.args){
				self = self.complement(region);
			}

			return self;
		}

		if (that.is_TrapezoidV) {
			if (this.x.equals(that.x[0])) {
				if (this.x_stop.gt(that.x[1]))
					return new Rectangle(that.x[1], this.y, this.width - that.width, this.height).union(new Rectangle(this.x, this.y, that.width, this.height).complement(that));

				if (this.x_stop.lt(that.x[1])) {

				}
				else {
					var args = [];
					if (this.y.lt(that.bbox.y))
						args.push(new TrapezoidV(that.x, [this.y, this.y, that.y[1], that.y[0]]).simplify());
					else if (this.y.lt(that.y[0]))
						args.push(new Triangle([this.x, this.y], [solve_x(this.y, that.p[0], that.p[1]), this.y], [this.x, that.y[0]]));
					else if (this.y.lt(that.y[1]))
						args.push(new Triangle([solve_x(this.y, that.p[0], that.p[1]), this.y], [this.x_stop, this.y], [this.x_stop, that.y[1]]));

					if (this.y_stop.gt(that.bbox.y_stop))
						args.push(new TrapezoidV(that.x, [that.y[3], that.y[2], this.y_stop, this.y_stop]).simplify());
					else if (this.y_stop.gt(that.y[3]))
						args.push(new Triangle([this.x, that.y[3]], [solve_x(this.y_stop, that.p[2], that.p[3]), this.y_stop], [this.x, this.y_stop]));
					else if (this.y_stop.gt(that.y[2]))
						args.push(new Triangle([solve_x(this.y_stop, that.p[2], that.p[3]), this.y_stop], [this.x_stop, that.y[2]], [this.x_stop, this.y_stop]));

					return Union.new(...args);
				}
			}
			else if (this.x_stop.equals(that.x[1])) {
				var y0 = solve_y(this.x, that.p[0], that.p[1]);
				var y3 = solve_y(this.x, that.p[3], that.p[2]);
				return this.complement(new TrapezoidV([this.x, this.x_stop], [y0, that.y[1], that.y[2], y3]));
			}
		}
		else if (that.is_TrapezoidH) {
			if (this.y.equals(that.y[0])) {
				if (this.y_stop.gt(that.y[1]))
					return new Rectangle(this.x, that.y[1], this.width, this.height - that.height).union(new Rectangle(this.x, this.y, this.width, that.height).complement(that));

				if (this.y_stop.lt(that.y[1])) {

				}
				else {
					var args = [];
					if (this.x.lt(that.bbox.x))
						args.push(new TrapezoidH([this.x, that.x[0], that.x[3], this.x], that.y).simplify());
					else if (this.x.lt(that.x[0]))
						args.push(new Triangle([this.x, this.y], [that.x[0], this.y], [this.x, solve_y(this.x, that.p[3], that.p[0])]));
					else if (this.x.lt(that.x[3]))
						args.push(new Triangle([this.x, solve_y(this.x, that.p[3], that.p[0])], [that.x[3], this.y_stop], [this.x, this.y_stop]));

					if (this.x_stop.gt(that.bbox.x_stop))
						args.push(new TrapezoidH([that.x[1], this.x_stop, this.x_stop, that.x[2]], that.y).simplify());
					else if (this.x_stop.gt(that.x[1]))
						args.push(new Triangle([that.x[1], this.y], [this.x_stop, this.y], [this.x_stop, solve_y(this.x_stop, that.p[1], that.p[2])]));
					else if (this.x_stop.gt(that.x[2]))
						args.push(new Triangle([that.x[2], this.y_stop], [this.x_stop, solve_y(this.x_stop, that.p[1], that.p[2])], [this.x_stop, this.y_stop]));

					return Union.new(...args);
				}
			}
			else if (this.y_stop.equals(that.y[1])) {
				var x0 = solve_x(this.y, that.p[0], that.p[3]);
				var x1 = solve_x(this.y, that.p[1], that.p[2]);
				return this.complement(new TrapezoidH([x0, x1, that.x[2], that.x[3]], [this.y, this.y_stop]));
			}
		}

		return new Complement(this, that);
	}

	get card() {
		return this.width.mul(this.height);
	}

	offset(dx, dy) {
		return new Rectangle(this.x.add(dx), this.y.add(dy), this.width, this.height);
	}

	distance() {
		if (arguments.length == 2) {
			var [x0, y0] = arguments;
			return distance(this.anchorPoint(x0, y0), [x0, y0]);
		}
		else {
			var [that] = arguments;

			if (that.x.ge(this.x_stop)) {
				if (that.y_stop.le(this.y))
					return distance(this.x_stop, this.y, that.x, that.y_stop);

				if (that.y.ge(this.y_stop))
					return distance(this.x_stop, this.y_stop, that.x, that.y);

				return that.x.sub(this.x_stop).abs();
			}
			else if (that.x_stop.le(this.x)) {
				if (that.y_stop.le(this.y))
					return distance(this.x, this.y, that.x_stop, that.y_stop);

				if (that.y.ge(this.y_stop))
					return distance(this.x, this.y_stop, that.x_stop, that.y);

				return that.x_stop.sub(this.x).abs();
			}
			else {
				if (that.y_stop.le(this.y))
					return this.y.sub(that.y_stop).abs();

				if (that.y.ge(this.y_stop))
					return this.y_stop.sub(that.y).abs();

				return 0;
			}
		}
	}

	// the anchor point is defined to be the point that is closest to the target point;
	anchorPoint(x0, y0) {
		if (x0.lt(this.x)) {
			if (y0.lt(this.y))
				return [this.x, this.y];

			if (y0.lt(this.y_stop))
				return [this.x, y0];

			return [this.x, this.y_stop];
		}

		if (x0.lt(this.x_stop)) {
			if (y0.lt(this.y))
				return [x0, this.y];

			if (y0.lt(this.y_stop))
				return [x0, y0];

			return [x0, this.y_stop];
		}

		if (y0.lt(this.y))
			return [this.x_stop, this.y];

		if (y0.lt(this.y_stop))
			return [this.x_stop, y0];

		return [this.x_stop, this.y_stop];
	}

	rotate(anchor, theta) {
		var {x: x0, y: y0, x_stop: x1, y_stop: y1} = this;
		var rotation = rotationMatrix(theta);

		var args = [
			rotatePoint([x0, y0], anchor, rotation),
			rotatePoint([x1, y0], anchor, rotation),
			rotatePoint([x1, y1], anchor, rotation),
			rotatePoint([x0, y1], anchor, rotation),
		];

		var index = argmin(args.map(tuple => tuple[1]));
		return Parallelogram.new(args[index], args[(index + 1) % 4], args[(index + 2) % 4]);
	}

	compareTo(rhs) {
		if (rhs.is_Rectangle) {
			if (this.x.lt(rhs.x))
				return -1;

			if (this.x.gt(rhs.x))
				return 1;

			if (this.y.lt(rhs.y))
				return -1;

			if (this.y.gt(rhs.y))
				return 1;

			if (this.width.lt(rhs.width))
				return -1;

			if (this.width.gt(rhs.width))
				return 1;

			if (this.height.lt(rhs.height))
				return -1;

			if (this.height.gt(rhs.height))
				return 1;

			return 0;
		}

		return -1;
	}

	_eval_bbox() {
		return this;
	}

	_eval_p() {
		return [[this.x, this.y], [this.x_stop, this.y], [this.x_stop, this.y_stop], [this.x, this.y_stop]];
	}
}

function rotationMatrix(theta) {
	return [[Math.cos(theta), -Math.sin(theta)], [Math.sin(theta), Math.cos(theta)]];
}

function rotatePoint(point, anchor, theta) {
//https://mathjs.org/docs/reference/
	var [x0, y0] = anchor.float();
	var [x1, y1] = point.float();

	if (!theta.isArray)
		theta = rotationMatrix(theta);

	return theta.matmul([x1 - x0, y1 - y0]).add([x0, y0]);
}

function rotateLeft(point, anchor) {
	var [x0, y0] = anchor;
	var [x1, y1] = point;

	var vector = [x1.sub(x0), y1.sub(y0)];
	var theta = [[0, 1], [-1, 0]];
	return theta.matmul(vector).add(anchor);
}

function rotateRight(point, anchor) {
	var [x0, y0] = anchor;
	var [x1, y1] = point;

	var vector = [x1.sub(x0), y1.sub(y0)];
	var theta = [[0, -1], [1, 0]];
	return theta.matmul(vector).add(anchor);
}

class Triangle extends Polygon {
	//preconditio: p0 is the leftmost point;
	constructor() {
		super();
		if (arguments.length == 3)
			this.args = arguments;
		else if (arguments.length == 2) {
			var [x, y] = arguments;
			this.args = [[x[0], y[0]], [x[1], y[1]], [x[2], y[2]]];
		}
	}

	get x_min() {
		return this.x[0];
	}

	get x_max() {
		return max(this.x[1], this.x[2]);
	}

	get y_min() {
		return min(this.y[0], this.y[1], this.y[2]);
	}

	get y_max() {
		return max(this.y[0], this.y[1], this.y[2]);
	}

	_eval_bbox() {
		var {x_min, x_max, y_min, y_max} = this;
		return new Rectangle(x_min, y_min, x_max - x_min, y_max - y_min);
	}

	contains(x, y) {
		var delta0 = new Triangle(this.p[0], this.p[1], [x, y]).direction();
		var delta1 = new Triangle(this.p[1], this.p[2], [x, y]).direction();
		var delta2 = new Triangle(this.p[2], this.p[1], [x, y]).direction();
		return delta0.is_positive || delta1.is_positive || delta2.is_positive;
	}

	is_straight_line() {
		return this.direction().is_zero;
	}

	direction() {
		var [x0, y0] = this.p[0];
		var [x1, y1] = this.p[1];
		var [x, y] = this.p[2];
		return x1.sub(x0).mul(y.sub(y0)).sub(y1.sub(y0).mul(x.sub(x0)));
	}

	_eval_p() {
		var args = this.args;
		if (!args.isArray)
			args = [...args];
		return args;
	}

	get x() {
		if (this._x == null)
			this._x = this.p.map(pt => pt[0]);
		return this._x;
	}

	get y() {
		if (this._y == null)
			this._y = this.p.map(pt => pt[1]);
		return this._y;
	}

	get card() {
		var [x0, y0] = this.p[0];
		var [x1, y1] = this.p[1];
		var [x2, y2] = this.p[2];
		//(x0 * (y1 - y2) + y0 * (x2 - x1) + x1 * y2 - x2 * y1) / 2;
		return x0.mul(y1.sub(y2)).add(y0.mul(x2.sub(x1))).add(x1.mul(y2).sub(x2.mul(y1))).div(2);
	}

	offset(dx, dy) {
		var [x0, y0] = this.p[0];
		var [x1, y1] = this.p[1];
		var [x2, y2] = this.p[2];
		return new Triangle([x0.add(dx), y0.add(dy)], [x1.add(dx), y1.add(dy)], [x2.add(dx), y2.add(dy)]);
	}
}

function solve_x(y, p0, p1) {
	var [x0, y0] = p0;
	var [x1, y1] = p1;
	//(x1 - x0) * (y - y0) - (y1 - y0) * (x - x0) = 0;
	return x1.sub(x0).mul(y.sub(y0)).div(y1.sub(y0)).add(x0);
}

function solve_y(x, p0, p1) {
	var [x0, y0] = p0;
	var [x1, y1] = p1;
	//(x1 - x0) * (y - y0) - (y1 - y0) * (x - x0) = 0;
	return y1.sub(y0).mul(x.sub(x0)).div(x1.sub(x0)).add(y0);
}

class Parallelogram extends Tetragon {
	get is_Parallelogram() {
		return true;
	}

	static new(p0, p1, p2) {
		return new Parallelogram(p0.toRational(), p1.toRational(), p2.toRational());
	}

	//preconditio: p0 is the leftmost point;
	constructor(p0, p1, p2) {
		super();
		this.args = [p0, p1, p2];
	}

	_eval_bbox() {
		var {x, y} = this;
		var x_min = min(x[0], x[2], x[3]);
		var x_max = max(x[0], x[1], x[2]);
		return new Rectangle(x_min, y[0], x_max.sub(x_min), y[2].sub(y[0]));
	}

	_eval_p() {
		var p = this.args;
		return [p[0], p[1], p[2], p[0].sub(p[1]).add(p[2])];
	}

	get x() {
		if (this._x == null)
			this._x = this.p.map(pt => pt[0]);
		return this._x;
	}

	get y() {
		if (this._y == null)
			this._y = this.p.map(pt => pt[1]);
		return this._y;
	}

	offset(dx, dy) {
		var [x0, y0] = this.p[0];
		var [x1, y1] = this.p[1];
		var [x2, y2] = this.p[2];
		return new Parallelogram([x0.add(dx), y0.add(dy)], [x1.add(dx), y1.add(dy)], [x2.add(dx), y2.add(dy)]);
	}

	compareTo(rhs) {
		if (rhs.is_Parallelogram)
			return this.p.compareTo(that.p)

		if (rhs.is_Rectangle)
			return 1;

		return -1;
	}

}

class Trapezoid extends Tetragon {
	get is_Trapezoid() {
		return true;
	}

	static new(x, y) {
		if (x.length == 4)
			return new TrapezoidH(x, y);
		if (y.length == 4)
			return new TrapezoidV(x, y);
	}

	constructor(x, y){
		super();
		Object.assign(this, {x, y});
	}

	offset(dx, dy) {
		return new this.constructor(this.x.map(x => x.add(dx)), this.y.map(y => y.add(dy)));
	}

	get args() {
		return [this.x, this.y];
	}

	complement(that) {
		return Tetragon.prototype.complement.apply(this, arguments);
	}

	intersects(that) {
		if (that.is_Parallelogram || that.is_Rectangle) {
			if (that.is_nonoverlapping(this))
				return new EmptySet;
		}

		return Tetragon.prototype.intersects.apply(this, arguments);
	}

}

//horizontal Trapezoid
// in the form y: [y0, y1], x: [x0, x1, x2, x3]
class TrapezoidH extends Trapezoid {
	get is_TrapezoidH() {
		return true;
	}

	simplify() {
		if (this.x[0] == this.x[3] && this.x[2] == this.x[1])
			return new Rectangle(this.x[0], this.y[0], this.width[0], this.height)
		return this;
	}

	constructor(x, y){
		super(x, y);
	}

	equals(that){
		if (that && that.is_TrapezoidH){
			return this.x.equals(that.x) && this.y.equals(that.y);
		}
	}

	get height() {
		return this.y[1].sub(this.y[0]);
	}

	get width() {
		return [this.x[1].sub(this.x[0]), this.x[2].sub(this.x[3])];
	}

	get card() {
		var {width: [w0, w1], height} = this;
		return height.mul(w0.add(w1)).div(2);
	}

	union(that) {
		if (that.is_Rectangle) {
			if (that.y == this.y[0] && that.y_stop == this.y[1]) {

				if (this.x[0] == this.x[3]) {
					if (that.x_stop == this.x[0])
						return new TrapezoidH([that.x, this.x[1], this.x[2], that.x], this.y);
				}
				else if (this.x[2] == this.x[1]) {
					if (that.x == this.x[1])
						return new TrapezoidH([this.x[0], that.x_stop, that.x_stop, this.x[3]], this.y);
				}
			}

			return new Union(that, this);
		}

		if (that.is_EmptySet)
			return this;

		if (that.is_Union) {
			var index = that.args.binary_search(this);
			return new Union(...that.args.slice(0, index), this, ...that.args.slice(index));
		}

		if (that.is_TrapezoidH) {
			var cmp = this.compareTo(that);
			if (cmp > 0)
				return that.union(this);

			if (this.y[1].equals(that.y[0])) {
				if (that.x[0].equals(this.x[3]) && that.x[1].equals(this.x[2])) {
					if (new Triangle(this.p[0], that.p[0], that.p[3]).is_straight_line() &&
						new Triangle(this.p[1], that.p[1], that.p[2]).is_straight_line()) {
						return new TrapezoidH([this.x[0], this.x[1], that.x[2], that.x[3]], [this.y[0], that.y[1]]).simplify();
					}
				}
			}
			else if (this.y.equals(that.y)) {
				if (this.x[1].equals(that.x[0]) && this.x[2].equals(that.x[3]))
					return new TrapezoidH([this.x[0], that.x[1], that.x[2], this.x[3]], this.y).simplify();
			}
			return new Union(this, that);
		}
		else {

		}
	}

	intersects(that) {
		if (that.is_Rectangle) {
			if (this.y.equals([that.y, that.y_stop])) {
				if (that.x_stop.le(min(this.x[0], this.x[3])))
					return new EmptySet;

				if (that.x_stop.le(this.x[0]))
					return new Triangle(this.p[3], [that.x_stop, solve_y(that.x_stop, this.p[0], this.p[3])], [that.x_stop, this.y[1]]);

				if (that.x_stop.le(this.x[3]))
					return new Triangle(this.p[0], [that.x_stop, [that.x_stop, this.y[0]], solve_y(that.x_stop, this.p[0], this.p[3])]);


				if (that.x_stop.le(min(this.x[1], this.x[2]))) {
					if (that.x.le(min(this.x[0], this.x[3])))
						return new TrapezoidH(this.p[0], [that.x_stop, this.y[0]], [that.x_stop, this.y[1]], this.p[3]);
					//unfinished work!
				}
			}
		}

		return Trapezoid.prototype.intersects.apply(this, arguments);

	}

	complement(that) {
		if (that.is_TrapezoidH) {
			if (this.y[0].equals(that.y[0])) {
				if (this.y[1].lt(that.y[1])) {
					var x2 = solve_x(this.y[1], that.p[1], that.p[2]);
					var x3 = solve_x(this.y[1], that.p[0], that.p[3]);
					return this.complement(new TrapezoidH([that.x[0], that.x[1], x2, x3], this.y));
				}
				else if (this.y[1].gt(that.y[1])) {
				}
				else {
					var args = [];
					if (this.x[0].lt(that.x[0])) {
						if (this.x[3].lt(that.x[3])) {
							args.push(new TrapezoidH([this.x[0], that.x[0], that.x[3], this.x[3]], this.y).simplify());
						}
						else if (this.x[3].gt(that.x[3])) {
							throw new Error("this.x[3].gt(that.x[3])");
						}
						else {
							throw new Error("this.x[3].equals(that.x[3])");
						}
					}
					else if (this.x[0].gt(that.x[0])) {
						if (this.x[3].lt(that.x[3])) {
							throw new Error("this.x[3].lt(that.x[3])");
						}
						else if (this.x[3].gt(that.x[3])) {
							if (this.x[0].ge(that.x[1])) {
								if (this.x[3].ge(that.x[2])) {
									//emptyset;
								}
								else {
									throw new Error("this.x[3].lt(that.x[2])");
								}
							}
							else {
								throw new Error("this.x[0].lt(that.x[1])");
							}
						}
						else {
							throw new Error("this.x[3].eq(that.x[3])");
						}
					}
					else {
						if (this.x[3].lt(that.x[3])) {
							throw new Error("this.x[3].lt(that.x[3])");
						}
						else if (this.x[3].gt(that.x[3])) {
							throw new Error("this.x[3].gt(that.x[3])");
						}
						else {
							//emptyset;
						}
					}

					if (this.x[1].gt(that.x[1])) {
						if (this.x[2].gt(that.x[2])) {
							if (this.x[0].ge(that.x[1])) {
								if (this.x[3].ge(that.x[2])) {
									// emptyset;
								}
								else {
									throw new Error("this.x[2].gt(that.x[2]) && this.x[3].lt(that.x[2])");
								}
							}
							else {
								throw new Error("this.x[2].gt(that.x[2])");
							}
						}
						else if (this.x[2].lt(that.x[2])) {
							throw new Error("this.x[2].lt(that.x[2])");
						}
						else {
							throw new Error("this.x[2].eq(that.x[2])");
						}
					}
					else if (this.x[1].lt(that.x[1])) {
						if (this.x[2].gt(that.x[2])) {
							throw new Error("this.x[2].gt(that.x[2])");
						}
						else if (this.x[2].lt(that.x[2])) {
							throw new Error("this.x[2].lt(that.x[2])");
						}
						else {
							//emptyset;
						}
					}
					else {
						if (this.x[2].gt(that.x[2])) {
							throw new Error("this.x[2].gt(that.x[2])");
						}
						else if (this.x[2].lt(that.x[2])) {
							throw new Error("this.x[2].lt(that.x[2])");
						}
						else {
							//emptySet;
						}
					}

					return Union.new(...args);
				}
			}
			else if (this.y[1].equals(that.y[1])) {
				if (this.y[0].gt(that.y[0])) {
					var x0 = solve_x(this.y[0], that.p[0], that.p[3]);
					var x1 = solve_x(this.y[0], that.p[1], that.p[2]);
					return this.complement(new TrapezoidH([x0, x1, that.x[2], that.x[3]], this.y));
				}
				else if (this.y[0].lt(that.y[0])) {
					var x0 = solve_x(that.y[0], this.p[0], this.p[3]);
					var x1 = solve_x(that.y[0], this.p[1], this.p[2]);
					return new TrapezoidH([this.x[0], this.x[1], x1, x0], [this.y[0], that.y[0]]).union(new TrapezoidH([x0, x1, this.x[2], this.x[3]], [that.y[0], this.y[1]]).complement(that));
				}
				else {

				}
			}
		}

	    return Trapezoid.prototype.complement.apply(this, arguments);
	}

	_eval_bbox() {
		var {x, y} = this;
		var x_min = min(x[0], x[3]);
		var x_max = max(x[2], x[1]);
		return new Rectangle(x_min, y[0], x_max.sub(x_min), this.height);
	}

	// the anchor point is defined to be the point that is closest to the target point;
	anchorPoint(x0, y0){
		if (y0.lt(this.y[0])) {
			if (x0.ge(this.x[0]) && x0.le(this.x[1]))
				return [x0, this.y[0]];
			//now that x0 < this.x[0] || x0 > this.x[1]

			if (x0.lt(this.x[0])) {
				if (this.x[0].le(this.x[3]))
					return this.p[0];

				var p3 = rotateRight(this.p[3], this.p[0]);
				var _x0 = solve_x(y0, this.p[0], p3);

				if (x0.ge(_x0))
					return this.p[0];

				var p0 = this.p[3].add(p3).sub(this.p[0]);
				_x3 = solve_x(y0, this.p[3], p0);
				if (x0.gt(_x3))
					return mean(this.p[0], this.p[3], x0.sub(_x0).div_x3.sub(_x0));

				return this.p[3];
			}
			else {
				//now that y0 > this.y[3]
				if (this.x[2].le(this.x[3]))
					return this.p[3];

				var p2 = rotateLeft(this.p[2], this.p[3]);
				var _x3 = solve_x(y0, this.p[3], p2);

				if (x0.le(_x3))
					return this.p[3];

				var p3 = this.p[2].add(p2).sub(this.p[3]);
				_x2 = solve_x(y0, this.p[2], p3);
				if (x0.lt(_x2))
					return mean(this.p[3], this.p[2], x0.sub(_x3).div(_x2.sub(_x3)));

				return this.p[2];
			}
		}
		else if (y0.gt(this.y[1])) {
			if (x0.ge(this.x[3]) && x0.le(this.x[2]))
				return [x0, this.y[1]];
			//now that y0 < this.y[1] || y0 > this.y[2]

			if (x0.lt(this.x[3])) {
				if (this.x[0].ge(this.x[3]))
					return this.p[3];

				var p0 = rotateLeft(this.p[0], this.p[1]);
				var _x1 = solve_x(y0, this.p[1], p0);

				if (x0.ge(_x1))
					return this.p[1];

				var p1 = this.p[0].add(p0).sub(this.p[1]);
				_x0 = solve_x(y0, this.p[0], p1);
				if (x0.gt(_x0))
					return mean(this.p[1], this.p[0], x0.sub(_x1).div(_x0.sub(_x1)));

				return this.p[0];
			}
			else {
				//now that y0 > this.y[3]
				if (this.x[2].ge(this.x[1]))
					return this.p[2];

				var p2 = rotateLeft(this.p[2], this.p[1]);
				var _x1 = solve_x(y0, this.p[1], p2);

				if (x0.ge(_x1))
					return this.p[1];

				var p1 = this.p[2].add(p2).sub(this.p[1]);
				var _x2 = solve_x(y0, this.p[2], p1);
				if (x0.gt(_x2))
					return mean(this.p[2], this.p[1], x0.sub(_x2).div(_x1.sub(_x2)));

				return this.p[2];
			}
		}
		else {
			var xLeft = solve_x(y0, this.p[0], this.p[3]);
			if (x0.lt(xLeft)) {

				if (this.x[3].lt(this.x[0])) {
					var p0 = rotateLeft(this.p[0], this.p[3]);
					var _x = solve_x(y0, this.p[3], p0);
					if (x0.le(_x))
						return this.p[3];

					return mean([xLeft, y0], this.p[3], x0.sub(xLeft).div(_x.sub(xLeft)));
				}
				else if (this.x[3].gt(this.x[0])) {
					var p3 = rotateRight(this.p[3], this.p[0]);
					var _x = solve_x(y0, this.p[0], p3);
					if (x0.le(_x))
						return this.p[0];

					return mean([xLeft, y0], this.p[0], x0.sub(xLeft).div(_x.sub(xLeft)));
				}
				else
					return [xLeft, y0];
			}

			var xRight = solve_x(y0, this.p[1], this.p[2]);
			if (x0.gt(xRight)) {

				if (this.x[2].lt(this.x[1])) {
					var p2 = rotateLeft(this.p[2], this.p[1]);
					var _x = solve_x(y0, this.p[1], p2);
					if (x0.ge(_x))
						return this.p[1];

					return mean([xRight, y0], this.p[1], x0.sub(xRight).div(_x.sub(xRight)));
				}
				else if (this.x[2].gt(this.x[1])) {
					var p1 = rotateRight(this.p[1], this.p[2]);
					var _x = solve_x(y0, this.p[2], p1);
					if (x0.ge(_x))
						return this.p[2];

					return mean([xRight, y0], this.px, x0.sub(xRight).div(_x.sub(xRight)));
				}
				else
					return [xRight, y0];
			}

			return [x0, y0];
		}
	}

	compareTo(that) {
		if (that.is_TrapezoidH) {
			var cmp = this.y.compareTo(that.y);
			if (cmp)
				return cmp;
			return this.x.compareTo(that.x);
		}

		if (that.is_TrapezoidV)
			return -1;

		return 1;
	}

	_eval_p() {
		var {x, y} = this;
		return [[x[0], y[0]], [x[1], y[0]], [x[2], y[1]], [x[3], y[1]]];
	}
}

//vertical Trapezoid
// in the form [x0, x1], [y0, y1, y2, y3]
class TrapezoidV extends Trapezoid {
	simplify() {
		if (this.y[0] == this.y[1] && this.y[2] == this.y[3])
			return new Rectangle(this.x[0], this.y[0], this.width, this.height[0])
		return this;
	}

	constructor(x, y){
		super(x, y);
	}

	get is_TrapezoidV() {
		return true;
	}

	get p0() {
		return [this.x[0], this.y[0]];
	}

	get p1() {
		return [this.x[1], this.y[1]];
	}

	get p2() {
		return [this.x[1], this.y[2]];
	}

	get p3() {
		return [this.x[0], this.y[3]];
	}

	equals(that){
		if (that && that.is_TrapezoidV) {
			return this.x.equals(that.x) && this.y.equals(that.y);
		}
	}

	get width() {
		return this.x[1] - this.x[0];
	}

	get height() {
		return [this.y[3].sub(this.y[0]), this.y[2].sub(this.y[1])];
	}

	get card() {
		var {width, height: [h0, h1]} = this;
		return width.mul(h0.add(h1)).div(2);
	}

	union(that) {
		if (that.is_Rectangle) {
			if (that.x == this.x[0] && that.x_stop == this.x[1]) {

				if (this.y[0] == this.y[1]) {
					if (that.y_stop == this.y[0])
						return new TrapezoidV(this.x, [that.y, that.y, this.y[2], this.y[3]]);
				}
				else if (this.y[2] == this.y[3]) {
					if (that.y == this.y[2])
						return new TrapezoidV(this.x, [this.y[0], this.y[1], that.y_stop, that.y_stop]);
				}
			}
			return new Union(that, this);
		}

		if (that.is_EmptySet)
			return this;

		if (that.is_Union) {
			var index = that.args.binary_search(this);
			return new Union(...that.args.slice(0, index), this, ...that.args.slice(index));
		}

		if (that.is_TrapezoidV) {
			var cmp = this.compareTo(that);
			if (cmp > 0)
				return that.union(this);

			if (this.x[1].equals(that.x[0])) {
				if (new Triangle(this.p[0], that.p[0], that.p[1]).is_straight_line() &&
					new Triangle(this.p[3], this.p[2], that.p[2]).is_straight_line())
					return new TrapezoidV([this.x[0], that.x[1]], [this.y[0], that.y[1], that.y[2], this.y[3]]).simplify();
			}
			else if (this.x.equals(that.x)) {
				if (this.y[3].equals(that.y[0]) && this.y[2].equals(that.y[1]))
					return new TrapezoidV(this.x, [this.y[0], this.y[1], that.y[2], that.y[3]]).simplify();
			}
			return new Union(this, that);
		}
		else {

		}
	}

	intersects(that) {
		if (that.is_Rectangle) {
			if (this.y.equals([that.y, that.y_stop])) {
				//unfinished work!
			}
		}

		return Trapezoid.prototype.intersects.apply(this, arguments);
	}

	complement(that) {
		if (that.is_TrapezoidH) {
			if (this.x[0].equals(that.x[0])) {
				if (this.x[1].lt(that.x[1])) {
					if (this.y[0].equals(that.y[0])){
						if (this.y[3].equals(that.y[3])){
							return new EmptySet;
						}
					}
				}
			}
		}

		return Trapezoid.prototype.complement(this, arguments);
	}

	_eval_bbox() {
		var {x, y} = this;
		var y_min = min(y[0], y[1]);
		var y_max = max(y[2], y[3]);
		return new Rectangle(x[0], y_min, this.width, y_max.sub(y_min));
	}

	// the anchor point is defined to be the point that is closest to the target point;
	anchorPoint(x0, y0){
		if (x0.lt(this.x[0])) {
			if (y0.ge(this.y[0]) && y0.le(this.y[3]))
				return [this.x[0], y0];
			//now that y0 < this.y[0] || y0 > this.y[3]

			if (y0.lt(this.y[0])) {
				if (this.y[0].le(this.y[1]))
					return this.p[0];

				var p1 = rotateLeft(this.p[1], this.p[0]);
				var _y0 = solve_y(x0, this.p[0], p1);

				if (y0.ge(_y0))
					return this.p[0];

				var p0 = this.p[1].add(p1).sub(this.p[0]);
				_y1 = solve_y(x0, this.p[1], p0);
				if (y0.gt(_y1))
					return mean(this.p[0], this.p[1], y0.sub(_y0).div(_y1.sub(_y0)));

				return this.p[1];
			}
			else {
				//now that y0 > this.y[3]
				if (this.y[2].le(this.y[3]))
					return this.p[3];

				var p2 = rotateRight(this.p[2], this.p[3]);
				var _y3 = solve_y(x0, this.p[3], p2);

				if (y0.le(_y3))
					return this.p[3];

				var p3 = this.p[2].add(p2).sub(this.p[3]);
				_y2 = solve_y(x0, this.p[2], p3);
				if (y0.lt(_y2))
					return mean(this.p[3], this.p[2], y0.sub(_y3).div(_y2.sub(_y3)));

				return this.p[2];

			}
		}
		else if (x0.gt(this.x[1])) {
			if (y0.ge(this.y[1]) && y0.le(this.y[2]))
				return [this.x[1], y0];
			//now that y0 < this.y[1] || y0 > this.y[2]

			if (y0.lt(this.y[1])) {
				if (this.y[0].ge(this.y[1]))
					return this.p[1];

				var p0 = rotateRight(this.p[0], this.p[1]);
				var _y1 = solve_y(x0, this.p[1], p0);

				if (y0.ge(_y1))
					return this.p[1];

				var p1 = this.p[0].add(p0).sub(this.p[1]);
				_y0 = solve_y(x0, this.p[0], p1);
				if (y0.gt(_y0))
					return mean(this.p[1], this.p[0], y0.sub(_y1).div(_y0.sub(_y1)));

				return this.p[0];
			}
			else {
				//now that y0 > this.y[3]
				if (this.y[2].ge(this.y[3]))
					return this.p[2];

				var p3 = rotateLeft(this.p[3], this.p[2]);
				var _y2 = solve_y(x0, this.p[2], p3);

				if (y0.le(_y2))
					return this.p[2];

				var p2 = this.p[3].add(p3).sub(this.p[2]);
				_y3 = solve_y(x0, this.p[3], p2);
				if (y0.lt(_y3))
					return mean(this.p[2], this.p[3], y0.sub(_y2).div(_y3.sub(_y2)));

				return this.p[3];
			}
		}
		else {
			var yUp = solve_y(x0, this.p[0], this.p[1]);
			if (y0.lt(yUp)) {

				if (this.y[0].lt(this.y[1])) {
					var p1 = rotateLeft(this.p[1], this.p[0]);
					var _y = solve_y(x0, this.p[0], p1);
					if (y0.le(_y))
						return this.p[0];

					return mean([x0, yUp], this.p[0], y0.sub(yUp).div(_y.sub(yUp)));
				}
				else if (this.y[0].gt(this.y[1])) {
					var p0 = rotateRight(this.p[0], this.p[1]);
					var _y = solve_y(x0, this.p[1], p0);
					if (y0.le(_y))
						return this.p[1];

					return mean([x0, yUp], this.p[1], y0.sub(yUp).div(_y.sub(yUp)));
				}
				else
					return [x0, yUp];
			}

			var yDown = solve_y(x0, this.p[2], this.p[3]);
			if (y0.gt(yDown)) {

				if (this.y[3].lt(this.y[2])) {
					var p3 = rotateLeft(this.p[3], this.p[2]);
					var _y = solve_y(x0, this.p[2], p3);
					if (y0.ge(_y))
						return this.p[2];

					return mean([x0, yDown], this.p[2], y0.sub(yDown).div(_y.sub(yDown)));
				}
				else if (this.y[3].gt(this.y[2])) {
					var p2 = rotateRight(this.p[2], this.p[3]);
					var _y = solve_y(x0, this.p[3], p2);
					if (y0.ge(_y))
						return this.p[3];

					return mean([x0, yDown], this.p[3], y0.sub(yDown).div(_y.sub(yDown)));
				}
				else
					return [x0, yDown];
			}

			return [x0, y0];
		}
	}

	compareTo(that) {
		if (that.is_TrapezoidV){
			var cmp = this.x.compareTo(that.x);
			if (cmp)
				return cmp;
			return this.y.compareTo(that.y);
		}
		else
			return 1;
	}

	_eval_p() {
		var {x, y} = this;
		return [[x[0], y[0]], [x[1], y[1]], [x[1], y[2]], [x[0], y[3]]];
	}
}

function saveFile(filename, data){
	if (typeof data != 'string')
		data = JSON.stringify(data, null, 4);

	saveAs(
		new Blob(
			[data],
			{
				type: "text/plain;charset=utf-8",
				endings: 'native'
			}
		),
		filename
	);
}

function isEmpty(obj){
	if (!obj)
		return true;

    for (var _ in obj) {
        return false;
    }

    return true;
}

function arraycopy(src, srcPos, dest, destPos, length){
	for (var i of range(srcPos, srcPos + length)){
		dest[destPos + i] = src[i];
	}
	return dest;
}

function *enumerate(array){
	var i = 0;
	for (var e of array)
		yield [i++, e];
}

function enumerated(array){
	return [...enumerate(array)]
}

function len(array){
	if (Array.isArray(array) || typeof array == 'string')
		return array.length;

	return Object.keys(array).length;
}

function majority(arr){
    var value2count = {};
    for (var value of arr){
		if (!value2count[value])
			value2count[value] = 0;
		value2count[value] += 1;
	}

    var max_count = -1;
    var majority = null;
    for (var [value, count] of Object.entries(value2count)){
        if (count > max_count) {
            majority = value;
            max_count = count;
		}
    }

    return majority
}

function partitionText(text, d){
	var n = text.length;
	var lengths = [n / d].repeat(d);
	if (n % d){
		for (var i of range(n % d)){
			lengths[i] += 1;
		}
	}

	var start = 0;
	var arr = [];
	for (var length of lengths){
		stop = start + length;
		arr.push(text.slice(start, stop));
		start = stop;
	}

	for (var i of range(1, arr.length)){
		var m0 = arr[i - 1].match(/[a-z]+$/);
		var m1 = arr[i].match(/^[a-z]+/);
		if (m0 && m1){
			m0 = m0[0];
			m1 = m1[0];

			if (m0.length < m1.length) {
				arr[i - 1] = arr[i - 1].slice(0, arr[i - 1].length - m0.length);
				arr[i] = m0 + arr[i];
			}
			else {
				arr[i - 1] = arr[i - 1] + m1;
				arr[i] = arr[i].slice(m1.length);
			}
		}
	}
	return arr;
}


function *zip() {
    var size = Infinity;
    for (var arr of arguments) {
		size = Math.min(arr.length, size);
	}

    for (var i of range(size)) {
		var arrs = [];
		for (var arr of arguments) {
			arrs.push(arr[i]);
		}

        yield arrs;
    }
}

function zipped() {
    return [...zip(...arguments)];
}

function split_filename(filename){
	var index = filename.lastIndexOf('.');
	if (index >= 0) {
		var basename = filename.slice(0, index);
		var extension = filename.slice(index + 1);
		return [basename, extension];
	}
	else {
		return [filename, ''];
	}
}

function gcd(x, y) {
	if (!y)
		return x;
	return gcd(y, x % y);
}

class Real {
	get is_Real() {
		return true;
	}
}

class Rational extends Real {
	get is_Rational() {
		return true;
	}

	static new(p, q) {
		if (!p.isBigInt)
			p = BigInt(p);

		if (!q.isBigInt)
			q = BigInt(q);

		var g = gcd(p, q);
		if (g != 1n) {
			p /= g;
			q /= g;
		}

		if (q < 0n) {
			p = -p;
			q = -q;
		}

		if (q == 1n)
			return p;

		return new Rational(p, q);
	}

	constructor(p, q) {
		super();
		this.p = p;
		this.q = q;
	}

	add(that) {
		if (that.is_Rational){
			var {p, q} = that;
		}
		else{
			var q = 1n;
			if (that.isBigInt) {
				var p = that;
			}
			else if (that == Infinity || that == -Infinity){
				return that;
			}
			else if (that.isInteger) {
				var p = BigInt(that);
			}
			else {
				var {p, q} = that.toRational();
			}
		}

		return Rational.new(this.p * q + this.q * p, q * this.q);
	}

	sub(that) {
		if (that.is_Rational){
			var {p, q} = that;
		}
		else{
			var q = 1n;
			if (that.isBigInt) {
				var p = that;
			}
			else if (that == Infinity || that == -Infinity){
				return -that;
			}
			else if (that.isInteger) {
				var p = BigInt(that);
			}
			else {
				var {p, q} = that.toRational();
			}
		}

		return Rational.new(this.p * q - this.q * p, q * this.q);
	}

	mul(that) {
		if (that.is_Rational){
			var {p, q} = that;
		}
		else{
			var q = 1n;
			if (that.isBigInt) {
				var p = that;
			}
			else if (that == Infinity || that == -Infinity){
				return that * this.sign();
			}
			else if (that.isInteger) {
				var p = BigInt(that);
			}
			else {
				var {p, q} = that.toRational();
			}
		}

		return Rational.new(this.p * p, q * this.q);
	}

	div(that) {
		if (that.is_Rational){
			var {p, q} = that;
		}
		else {
			var q = 1n;
			if (that.isBigInt) {
				var p = that;
			}
			else if (that == Infinity || that == -Infinity){
				return 0n;
			}
			else if (that.isInteger) {
				var p = BigInt(that);
			}
			else {
				var {p, q} = that.toRational();
			}
		}

		return Rational.new(this.p * q, p * this.q);
	}

	neg() {
		return new Rational(-this.p, this.q);
	}

	inverse() {
		var {p: q, q: p} = this;
		if (q < 0n){
			p = -p;
			q = -q;
		}

		if (q == 1n)
			return p;

		return new Rational(p, q);
	}

	float() {
		return this.p.float() / this.q.float();
	}

	sign() {
		return this.p.sign();
	}

	gt(that) {
		return this.sub(that).is_positive;
	}

	lt(that) {
		return this.sub(that).is_negative;
	}

	ge(that) {
		return this.sub(that).is_nonnegative;
	}

	le(that) {
		return this.sub(that).is_nonpositive;
	}

	get is_zero() {
		return false;
	}

	get is_positive() {
		return this.p.is_positive;
	}

	get is_negative() {
		return this.p.is_negative;
	}

	get is_nonpositive() {
		return this.p.is_nonpositive;
	}

	get is_nonnegative() {
		return this.p.is_nonnegative;
	}

	round() {
		return this.float().round();
	}

	floor() {
		if (this.is_negative)
			return -((-this.p) / this.q) - 1n;
		return this.p / this.q;
	}

	ceil() {
		if (this.is_positive)
			return this.p / this.q + 1n;
		return -((-this.p) / this.q);
	}

	sqrt() {
		return this.float().sqrt();
	}

	clip(min, max){
		if (this.lt(min))
			return min;

		if (this.gt(max))
			return max;

		return this;
	}

	equals(that) {
		return that.is_Rational && this.p == that.p && this.q == that.q;
	}

	toRational() {
		return this;
	}

	relu() {
		return this.is_positive? this: 0n;
	}

	abs() {
		return this.sign() < 0? this.neg(): this;
	}

	toString(radix) {
		if (radix == 10) {
			var {p, q} = this;
			return `${p}/${q}`;
		}

		return this.float().toFixed(2);
	}
}

function sleep(time, message) {
	//usage: await sleep(1000);
	if (message)
		message = ' : ' + message;
	else
		message = '';
	console.log(`sleeping for ${time} seconds${message}`);
	time *= 1000;
	return new Promise((resolve, reject) => setTimeout(resolve, time));
}

function convertWithAlignment() {
	var arr = [...arguments];
    var res = [''].repeat(arr.length);

    var size = len(arr[0]);
    for (var j of range(size)) {
        var l = [0].repeat(len(arr))

        for (var i of range(len(arr))) {
            res[i] += arr[i][j] + ' ';
            l[i] = strlen(arr[i][j]);
		}

        var maxLength = max(l);
        for (var i of range(len(arr))) {
            res[i] += ' '.repeat(maxLength - l[i]);
        }
	}

    return res;
}

function *reversed(list) {
	if (!list.isArray)
		list = [...list];

	for (var i of range(list.length - 1, -1, -1)) {
		yield list[i];
	}
}

function fromEntries() {
	var obj = {};
	if (arguments.length > 1) {
		for (var i of range(0, arguments.length, 2)) {
			obj[arguments[i]] = arguments[i + 1];
		}
	}
	else {
		for (var [key, value] of arguments[0]) {
			obj[key] = value;
		}
	}

	return obj;
}

function addCSS(cssText){
	var head = document.head || document.getElementsByTagName('head')[0];
	var style = document.createElement('style');
	style.appendChild(document.createTextNode(cssText));
	head.appendChild(style);
}

function items(dict, reverse) {
	dict = Object.entries(dict);
	dict.sort(reverse ? (lhs, rhs) => rhs[0].compareTo(lhs[0]): (lhs, rhs) => lhs[0].compareTo(rhs[0]));
	return dict;
}


function setitem() {
    var [data, ...indices] = arguments;

	var value = indices.pop();
    var parentData = null;
    for (var [i, key] of enumerate(indices)) {
		if (i + 1 < indices.length) {
			if (data[key]? (data[key].isString || data[key].isNumber) : true)
				data[key] = indices[i + 1].isInteger? []: {};

			parentData = data;
			data = data[key];
		}
		else {
			if (key.isInteger) {
				if (data == null) {
					if (parentData != null && i) {
						data = [];
						parentData[indices[i - 1]] = data;
					}
				}
			}
			else if (data.isArray) {
				if (parentData != null && i) {
					data = {};
					parentData[indices[i - 1]] = data;
				}
				else {
					for (var i of reversed(range(data.length))) {
						data.delete(i);
					}
				}
			}
			data[key] = value;
		}
    }
}

function getitem() {
	var [data, ...indices] = arguments;
    for (var key of indices) {
        if (data == null)
            return;

        data = data[key];
    }

    return data;
}

function randrange(start, stop, step) {
	if (step == null) {
		if (stop == null) {
			stop = start;
			start = 0;
		}
		step = 1;
		var size = stop - start;
	}
	else {
		var size = ((stop - start) / step).ceil();
	}

	return (Math.random() * size).floor() * step + start;
}

function sample(data, count) {
	if (count > data.length)
		count = data.length;

	for (var i of range(count)) {
		var j = randrange(i, data.length); //must be >= i
		if (j > i)
			[data[i], data[j]] = [data[j], data[i]];
	}

	return data.slice(0, count);
}

function deleteIndices(arr, fn, postprocess) {
    var indicesToDelete = [];
    for (var i of range(arr.length)) {
        if (fn.length == 2 ? fn(arr, i): fn(arr[i]))
            indicesToDelete.push(i);
    }

    if (indicesToDelete.length)
        indicesToDelete = indicesToDelete.reverse();

    for (var i of indicesToDelete) {
        if (postprocess) {
			if (postprocess.length == 2)
				postprocess(arr, i);
			else
				postprocess(arr[i]);
		}

        arr.delete(i);
    }

    return indicesToDelete.length;
}

function computed(cls, attr) {
	if (arguments.length > 2) {
		var [cls, ...attr] = arguments;
		for (var attr of attr) {
			computed(cls, attr);
		}
	}
	else {
		cls.prototype.__defineGetter__(attr, function() {
			var _attr = '_' + attr;
			if (!this[_attr]) {
				this[_attr] = cls[attr](this);
			}
			return this[_attr];
		});
	}
}

function partition(data, divisor) {
	var size = data.length;

	var quotient = parseInt(size / divisor);
    var batches = [];

    var sizes = [quotient].repeat(divisor);

    for (var i of range(size % divisor)) {
		++sizes[i];
	}

	var start = 0;
    for (var [i, length] of enumerate(sizes)) {
		var stop = start + length;
		batches[i] = data.slice(start, stop);
		start = stop;
	}

    return batches;
}

function batches(data, batch_size) {
	if (!data.isArray)
		data = [...data];

	var size = data.length;
	var divisor = parseInt((size + batch_size - 1) / batch_size);
	if (divisor)
		return partition(data, divisor);
	return data;
}

function pop(obj, key) {
	var value = obj[key];
	delete obj[key];
	return value;
}

function json_extract(obj, path) {
	var paths = [];
	for (var m of path.slice(1).matchAll(/\[(\d+)\]|\.([^.\[\]]+)/g)) {
		paths.push(m[2] || parseInt(m[1]));
	}

	return getitem(obj, ...paths);
}

function not_any_of(regex) {
	return new RegExp(`(?!(?:${regex.source}))\\S+`);
}


function parseTSV(data) {
    var {data, meta, errors} = Papa.parse(data, { skipEmptyLines: true });

    var [fields, ...data] = data;
    //console.log(fields);
    //console.log(data);

    data = data.map(args => {
    	var obj = {};
    	for (var [key, value] of zip(fields, args)) {
    		obj[key] = value;
    	}
    	return obj;
    });

    return data;
}

function get_url(kwargs) {
	return get_url_array(kwargs).map(args => {
		var [key, value] = args;
		for (var i of range(1, key.length)) {
			key[i] = `[${key[i]}]`;
		}
		key = key.join('');
		return `${key}=${value}`;
	}).join('&');
}

function get_url_array(kwargs) {
	var url = [];
	for (var key in kwargs) {
		var value = kwargs[key];
		if (value == null) {
			url.push([[key], value]);
		}
		else if (value.isArray) {
			var obj = {};
			for (var [i, value] of enumerate(value)) {
				if (value != null)
					obj[i] = value;
			}

			for (var args of get_url_array(obj)) {
				url.push([[key, ...args[0]], args[1]]);
			}
		}
		else if (value.constructor == Object) {
			for (var args of get_url_array(value)) {
				url.push([[key, ...args[0]], args[1]]);
			}
		}
		else {
			url.push([[key], value]);
		}
	}

	return url;
}

function is_same(list) {
	if (!list.isArray)
        list = [...list];

    for (var i of range(1, list.length)) {
        if (list[i] != list[i - 1])
            return false;
	}
    return true;
}

class Cookie {
	constructor() {
		this.dict = {};
		//console.log("document.cookie : " + document.cookie);
		var cookie = document.cookie.split(";");
		// console.log(cookie);
		for (var i = 0; i < cookie.length; ++i) {
			var pair = cookie[i].trim().split("=");
			if (pair.length != 2)
				continue;
			// console.log(pair);
			this.dict[pair[0]] = unescape(pair[1]);
		}
	}

	set(key, value) {
		if (!key || !value) {
			this.del(key);
			return;
		}

		document.cookie = key + "=" + escape(value);
		this.dict[key] = value;
		console.log("cookie : " + document.cookie);
		console.log("this.dict = ");
		console.log(this.dict);
	}

	get(key) {
		return this.dict[key];
	}

	del(key) {
		var expires = new Date();
		expires.setTime(expires.getTime() - 10);
		document.cookie = key + '=' + escape('null') + ';expires=' + expires.toGMTString();
		delete this.dict[key];
	}
}

Cookie.instance = new Cookie();

async function createApp(component, data, id) {
	const options = {
		moduleCache: { vue: Vue },

		async getFile(url) {
			var res;
			try{
				res = await fetch(url);
			}
			catch(err){
				var dotIndex = url.lastIndexOf('.');
				var ext = url.slice(dotIndex + 1);
				var name = url.slice(0, dotIndex).split('/');
				switch (ext){
				case 'js':
					var text = getitem(window.js, ...name.slice(1));
					//console.log(text);
                    return {
						getContentData() {
							return text;
						},
						type: ".mjs"
					};
				case 'vue':
					return getitem(window.vue, ...name.slice(2));
				}
			}

			if (!res.ok)
				throw Object.assign(new Error(res.statusText + ' ' + url), { res });

			if (url.endsWith(".js")) {
				return res.text().then(text => {
                    return {
						getContentData() {
							return text;
						},
						type: ".mjs"
					};
                });
            }

			return res.text();
		},

		addStyle(textContent) {
			document.head.insertBefore(
				Object.assign(document.createElement('style'), { textContent }),
				document.head.getElementsByTagName('style')[0] || null);
		},
	};

	const { loadModule } = window['vue3-sfc-loader'];

	id ||= 'root';
	var div = document.createElement('div');
	div.setAttribute('id', id);

	if (document.body == null){
		document.body = document.createElement('body');
	}
	document.body.appendChild(div);

	var components = {};
	components[component] = await loadModule(`static/components/${component}.vue`, options);

	var args = [];
	for (let key in data){
		args.push(`:${key}=${key}`);
	}

	var App = {
		components: components,

		data() {
			return data;
		},

		template: `<${component} ref=${component} ${args.join(' ')}></${component}>`,
	};

	var app = Vue.createApp(App);
	app.mount('#' + id);
	return app;
}

function setAttribute(self, key, value){
	while (!(key in self.$data)){
		self = self.$parent;
	}
	self.$data[key] = value;
}

function track_mounted(tag){
	return {
		mounted(el, binding){
			++binding.instance.mounted[tag];
		},

		unmounted(el, binding){
			--binding.instance.mounted[tag];
			console.assert(binding.instance.mounted[tag] >= 0, "binding.instance.mounted[tag] >= 0");
		},
	};
}

const clipboard = {
	instance: null,

	contextmenu(event) {
		event.stopPropagation();
		event.preventDefault();
		clipboard.instance.onClick(event);
	},

	mounted(el) {
		var {tagName, id} = el;
		if (id) {
			id = id.replace(/([.:])/g, '\\$1');
			tagName += `#${id}`;
		}

		if (!el.getAttribute('data-clipboard-action'))
			el.setAttribute('data-clipboard-action', 'copy');
		el.setAttribute('data-clipboard-target', '[data-clipboard-action="copy"]');

		el.addEventListener('contextmenu', clipboard.contextmenu);

		if (!clipboard.instance) {
			var instance = clipboard.instance = new ClipboardJS(`${tagName}[data-clipboard-action="copy"]`);

			instance.on('success', function(event) {
				var {trigger} = event;
				if (trigger.getAttribute('data-clipboard-text')) {
					var range = document.createRange();
					range.selectNodeContents(trigger);
					var selection = window.getSelection();
					selection.removeAllRanges();
					selection.addRange(range);
				}
				else
					console.log(event);
			});

			instance.on('error', function(event) {
				console.log(event);
				event.clearSelection();
			});

			// Store the original onClick function
			const onClick = ClipboardJS.prototype.onClick;

			// Override the onClick function
			ClipboardJS.prototype.onClick = function(event) {
				// Check if the event is a left-click (event.button === 0)
				if (event.button === 0)
					// Do nothing for left-click
					return;
				// Call the original onClick function for other events (e.g., right-click)
				onClick.call(this, event);
			};
		}
	},
};

async function query(host, token, sql) {
	var data = {sql};
	data.token = token;
	var kwargs = {};
	if (host && host != 'localhost')
		kwargs.host = host;
	return await form_post('query.php?' + get_url(kwargs), data);
}

function fetchEventSource(input, _a) {
	function getMessages(onId, onRetry, onMessage) {
		let message = newMessage();
		const decoder = new TextDecoder();
		return function onLine(line, fieldLength) {
			if (line.length === 0) {
				onMessage === null || onMessage === void 0 ? void 0 : onMessage(message);
				message = newMessage();
			}
			else if (fieldLength > 0) {
				const field = decoder.decode(line.subarray(0, fieldLength));
				const valueOffset = fieldLength + (line[fieldLength + 1] === 32 ? 2 : 1);
				const value = decoder.decode(line.subarray(valueOffset));
				switch (field) {
					case 'data':
						message.data = message.data
							? message.data + '\n' + value
							: value;
						break;
					case 'event':
						message.event = value;
						break;
					case 'id':
						onId(message.id = value);
						break;
					case 'retry':
						const retry = parseInt(value, 10);
						if (!isNaN(retry)) {
							onRetry(message.retry = retry);
						}
						break;
				}
			}
		};
	}

	function concat(a, b) {
		const res = new Uint8Array(a.length + b.length);
		res.set(a);
		res.set(b, a.length);
		return res;
	}

	function newMessage() {
		return {
			data: '',
			event: '',
			id: '',
			retry: undefined,
		};
	}

	function __rest(s, e) {
		var t = {};
		for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
			t[p] = s[p];
		if (s != null && typeof Object.getOwnPropertySymbols === "function")
			for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {
				if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))
					t[p[i]] = s[p[i]];
			}
		return t;
	};

	async function getBytes(stream, onChunk) {
		const reader = stream.getReader();
		let result;
		while (!(result = await reader.read()).done) {
			onChunk(result.value);
		}
	}

	function getLines(onLine) {
		let buffer;
		let position;
		let fieldLength;
		let discardTrailingNewline = false;
		return function onChunk(arr) {
			if (buffer === undefined) {
				buffer = arr;
				position = 0;
				fieldLength = -1;
			}
			else {
				buffer = concat(buffer, arr);
			}
			const bufLength = buffer.length;
			let lineStart = 0;
			while (position < bufLength) {
				if (discardTrailingNewline) {
					if (buffer[position] === 10) {
						lineStart = ++position;
					}
					discardTrailingNewline = false;
				}
				let lineEnd = -1;
				for (; position < bufLength && lineEnd === -1; ++position) {
					switch (buffer[position]) {
						case 58:
							if (fieldLength === -1) {
								fieldLength = position - lineStart;
							}
							break;
						case 13:
							discardTrailingNewline = true;
						case 10:
							lineEnd = position;
							break;
					}
				}
				if (lineEnd === -1) {
					break;
				}
				onLine(buffer.subarray(lineStart, lineEnd), fieldLength);
				lineStart = position;
				fieldLength = -1;
			}
			if (lineStart === bufLength) {
				buffer = undefined;
			}
			else if (lineStart !== 0) {
				buffer = buffer.subarray(lineStart);
				position -= lineStart;
			}
		};
	}

	function defaultOnOpen(response) {
		const contentType = response.headers.get('content-type');
		if (!(contentType === null || contentType === void 0 ? void 0 : contentType.startsWith(EventStreamContentType))) {
			throw new Error(`Expected content-type to be ${EventStreamContentType}, Actual: ${contentType}`);
		}
	}

	const EventStreamContentType = 'text/event-stream';
	const DefaultRetryInterval = 1000;
	const LastEventId = 'last-event-id';

    var { signal: inputSignal, headers: inputHeaders, onopen: inputOnOpen, onmessage, onclose, onerror, openWhenHidden, fetch: inputFetch } = _a, rest = __rest(_a, ["signal", "headers", "onopen", "onmessage", "onclose", "onerror", "openWhenHidden", "fetch"]);
    return new Promise((resolve, reject) => {
        const headers = Object.assign({}, inputHeaders);
        if (!headers.accept) {
            headers.accept = EventStreamContentType;
        }
        let curRequestController;
        function onVisibilityChange() {
            curRequestController.abort();
            if (!document.hidden) {
                create();
            }
        }
        if (!openWhenHidden) {
            document.addEventListener('visibilitychange', onVisibilityChange);
        }
        let retryInterval = DefaultRetryInterval;
        let retryTimer = 0;
        function dispose() {
            document.removeEventListener('visibilitychange', onVisibilityChange);
            window.clearTimeout(retryTimer);
            curRequestController.abort();
        }
        inputSignal === null || inputSignal === void 0 ? void 0 : inputSignal.addEventListener('abort', () => {
            dispose();
            resolve();
        });
        const fetch = inputFetch !== null && inputFetch !== void 0 ? inputFetch : window.fetch;
        const onopen = inputOnOpen !== null && inputOnOpen !== void 0 ? inputOnOpen : defaultOnOpen;
        async function create() {
            var _a;
            curRequestController = new AbortController();
            try {
                const response = await fetch(input, Object.assign(Object.assign({}, rest), { headers, signal: curRequestController.signal }));
                await onopen(response);
                await getBytes(response.body, getLines(getMessages(id => {
                    if (id) {
                        headers[LastEventId] = id;
                    }
                    else {
                        delete headers[LastEventId];
                    }
                }, retry => {
                    retryInterval = retry;
                }, onmessage)));
                onclose === null || onclose === void 0 ? void 0 : onclose();
                dispose();
                resolve();
            }
            catch (err) {
                if (!curRequestController.signal.aborted) {
                    try {
                        const interval = (_a = onerror === null || onerror === void 0 ? void 0 : onerror(err)) !== null && _a !== void 0 ? _a : retryInterval;
                        window.clearTimeout(retryTimer);
                        retryTimer = window.setTimeout(create, interval);
                    }
                    catch (innerErr) {
                        dispose();
                        reject(innerErr);
                    }
                }
            }
        }
        create();
    });
}

class FatalError extends Error {
};

// convert obj to python-like string
function str(obj) {
	if (obj == null)
		return "None";
    if (obj.isArray)
        return "[%s]".format(obj.map(obj => str(obj)).join(", "));
    if (obj.isString) {
		obj = obj.replace(/\n/g, "\\n").replace(/\xa0/g, "\\xa0");
        if (obj.contains("'")) {
            if (obj.contains('"'))
                return "'%s'".format(obj.replace(/'/g, "\\'"));
			else
				return '"%s"'.format(obj);
        }
		else
			return "'%s'".format(obj);
    }

	var array = [];
	for (var [key, value] of Object.entries(obj)) {
		array.push(str(key) + ": " + str(value));
	}
	return "{%s}".format(array.join(", "));
}


function topologicalSortDepthFirst(graph) {
    const L = [];
    const permanentMark = new Set();
    const temporaryMark = new Set();

    function visit(n) {
        if (permanentMark.has(n))
            return;
        if (temporaryMark.has(n))
            throw new Error('Cycle detected');
        temporaryMark.add(n);
        for (let m of graph[n])
            visit(m);
        temporaryMark.delete(n);
        permanentMark.add(n);
        L.push(n);
    }

    try {
        for (let n in graph)
            visit(n);
    } catch (e) {
        return;
    }

    return L;
}


function get_class(obj) {
	if (obj == null)
		return null;
	return obj.constructor.name;
}

function isinstance(obj, cls) {
	if (cls.isArray)
		return cls.some(cls => obj instanceof cls);
	else
		return obj instanceof cls;
}
console.log("import std.js");