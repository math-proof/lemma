/**
 * Shared non-Python utilities: DOM helpers, HTTP, Vue SFC `createApp`,
 * geometry, cookies, clipboard, URL/query helpers, SSE, etc.
 *
 * Depends on `py.js` globals (prototype patches, range, getitem, Rational, …).
 * Classic-script load order: py.js then std.js.
 */
if (typeof window !== 'undefined' && typeof document !== 'undefined') {
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

function intersects(rectA, rect) {
	function intersects(rangeA, rangeB){
		var [a0, b0] = rangeA;
		var [a1, b1] = rangeB;
		return Math.max(a0, a1) < Math.min(b0, b1);
	}

	return intersects([rect.x, rect.x + rect.width], [rectA.x, rectA.x + rectA.width]) && intersects([rect.y, rect.y + rect.height], [rectA.y, rectA.y + rectA.height]);
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

function addCSS(cssText){
	var head = document.head || document.getElementsByTagName('head')[0];
	var style = document.createElement('style');
	style.appendChild(document.createTextNode(cssText));
	head.appendChild(style);
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

if (typeof document !== 'undefined') {
	Cookie.instance = new Cookie();
}

if (typeof window !== 'undefined') {
	// TEMP DEBUG: collect uncaught errors with stacks (remove after CM6 migration debugging)
	window.__errLog = [];
	window.addEventListener('unhandledrejection', e => window.__errLog.push('REJECTION: ' + (e.reason && e.reason.stack || e.reason)));
	window.addEventListener('error', e => window.__errLog.push('ERROR: ' + e.message + ' @ ' + e.filename + ':' + e.lineno + ':' + e.colno));
}

/** Cached import-map lookup for bare module specifiers (used by SFC loader's getFile). */
var _importMap = null;
function resolveModuleUrl(url) {
	if (!/^(https?:|\/|\.\/|\.\.\/|data:)/.test(url)) {
		if (!_importMap) {
			var el = document.querySelector('script[type="importmap"]');
			try { _importMap = el ? (JSON.parse(el.textContent).imports || {}) : {}; }
			catch (e) { _importMap = {}; }
		}
		if (url in _importMap) return _importMap[url];
		for (var scope in _importMap) {
			if (url.startsWith(scope + '/')) return _importMap[scope] + url.slice(scope.length);
		}
	}
	return url;
}

/**
 * @param {string} component  SFC base name under vue/
 * @param {Record<string, unknown>} data  Root $data passed as props to the child; each own key is bound with onUpdate:key
 * @param {string} [id='root']  Mount target element id
 */
async function createApp(component, data, id) {
	const options = {
		moduleCache: Object.assign({ vue: Vue }, window.__cmModules || {}),

		// Called by SFC loader BEFORE getFile. Intercepts bare CM6 specifiers
		// that somehow miss the moduleCache lookup (e.g. id mismatch).
		async loadModule(id, opts) {
			if (window.__cmModules && id in window.__cmModules) {
				return window.__cmModules[id];
			}
			return undefined; // fall through to getFile
		},

		async getFile(url) {
			// Handle bare CM6 specifiers from the pre-bundled modules.
			// Must check BEFORE resolveModuleUrl, which transforms bare
			// specifiers into resolved URLs (breaking the __cmModules lookup).
			if (window.__cmModules && url in window.__cmModules) {
				var mod = window.__cmModules[url];
				var src = Object.keys(mod).map(function(k) {
					return 'export var ' + k + ' = window.__cmModules["' + url + '"].' + k + ';';
				}).join('\n');
				return { getContentData() { return src; }, type: ".mjs" };
			}
			url = resolveModuleUrl(url);
			var res;
			try{
				res = await fetch(url, { cache: 'no-store' });
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
					return getitem(window.vue, ...name.slice(1));
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

	// Expose options + a component loader for SFC-compiled .js files that need
	// to lazy-load .vue components without using native import() (which the
	// SFC loader's Babel transform misses in Babel 7.x ImportExpression).
	window.__sfcOptions = options;
	window.__loadVueComponent = async function (name) {
		const mod = await window['vue3-sfc-loader'].loadModule(`vue/${name}.vue`, options);
		return { default: mod };
	};

	const { loadModule } = window['vue3-sfc-loader'];

	id ||= 'root';
	var div = document.createElement('div');
	div.setAttribute('id', id);

	if (document.body == null){
		document.body = document.createElement('body');
	}
	document.body.appendChild(div);

	data ||= {};
	const Comp = await loadModule(`vue/${component}.vue`, options);
	const $data = Vue.reactive(data);
	const Root = {
		setup(_, { expose }) {
			expose({ $data, ...Vue.toRefs($data) });
			return () => {
				const props = {};
				for (const key in data) {
					props[key] = $data[key];
					props[`onUpdate:${key}`] = (value) => { $data[key] = value; };
				}
				return Vue.h(Comp, props);
			};
		},
	};

	var app = Vue.createApp(Root);
	app.mount('#' + id);
	return app;
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

async function query(host, sql) {
	var data = {sql};
	var kwargs = {};
	if (host && host != 'localhost')
		kwargs.host = host;
	return await form_post('query?' + get_url(kwargs), data);
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

console.log("import std.js");
Object.assign(globalThis, {
	Cookie,
	FatalError,
	Parallelogram,
	Polygon,
	Rectangle,
	Tetragon,
	Trapezoid,
	TrapezoidH,
	TrapezoidV,
	Triangle,
	addCSS,
	clipboard,
	computed,
	convertWithAlignment,
	createApp,
	deepCopy,
	distance,
	fetchEventSource,
	form_post,
	get,
	getParameter,
	getParameterByName,
	getParameters,
	get_url,
	get_url_array,
	intersects,
	isEnglish,
	json_post,
	mean,
	octet_stream_post,
	params,
	parseTSV,
	partitionText,
	query,
	quote,
	quote_html,
	rotateLeft,
	rotatePoint,
	rotateRight,
	rotationMatrix,
	saveFile,
	solve_x,
	solve_y,
	split_filename,
	str_html,
	topologicalSortDepthFirst,
	track_mounted,
});
