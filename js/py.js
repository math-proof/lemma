/**
 * Python-like APIs for the browser/Node: builtins (range, len, zip, …),
 * Number/String/Array/BigInt prototype helpers, Rational, collections,
 * and sympy-ish SymbolicSet types.
 *
 * Non-Python shared utils live in `std.js` (load after this file).
 */

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

String.prototype.decodeURI = function() {
	return decodeURIComponent(this);
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

function sortedDictEntries(dict, reverse) {
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


function is_same(list) {
	if (!list.isArray)
        list = [...list];

    for (var i of range(1, list.length)) {
        if (list[i] != list[i - 1])
            return false;
	}
    return true;
}

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

console.log("import py.js");
Object.assign(globalThis, {
	Complement,
	Deque,
	EmptySet,
	Intersection,
	PriorityQueue,
	Range,
	Rational,
	Real,
	SymbolicSet,
	Union,
	_merge_sort,
	argmax,
	argmin,
	array_push,
	arraycopy,
	batches,
	chr,
	cmp,
	compareTo,
	compare_debug,
	deleteIndices,
	dict_equals,
	enumerate,
	enumerated,
	equals,
	from,
	fromEntries,
	gcd,
	getClass,
	get_class,
	input_kwargs,
	intersection,
	isEmpty,
	is_same,
	isinstance,
	items,
	join,
	json_extract,
	len,
	list,
	majority,
	map,
	mapped,
	max,
	merge_sort,
	min,
	not_any_of,
	ord,
	partition,
	pop,
	prod,
	randrange,
	range,
	ranged,
	reversed,
	sample,
	setitem,
	getitem,
	sortedDictEntries,
	sleep,
	str,
	strlen,
	sum,
	sunday,
	toUnicodeDigit,
	zip,
	zipped,
});
