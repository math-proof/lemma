/**
 * Shared helpers for client and server.
 * Works in both Node (import) and browser (script type="module").
 * Environment-agnostic exports (format); browser-only code guarded by typeof window.
 */

String.prototype.format = function () {
  const args = arguments;
  let index = 0;
  return this.replace(/%[sd]/g, () => args[index++]);
};

String.prototype.isspace = function () {
  return /^\s+$/.test(this);
};

String.prototype.isString = true;

Array.prototype.binary_search = function(value, cmp) {
	if (cmp) {
		if (cmp.length == 1) {
			var key = cmp;
			cmp = (lhs, rhs) => compareTo(key(lhs), key(rhs));
		}
	}
	else {
		cmp = (a, b) => a.compareTo(b);
	}

  var begin = 0, end = this.length;
  for (;;) {
      if (begin == end)
          return begin;

      var mid = begin + end >> 1;

      var ret = cmp(this[mid], value);
      if (ret < 0)
          begin = mid + 1;
      else if (ret > 0)
          end = mid;
      else
          return mid;
  }
}

export function ord(s) {
  return s.charCodeAt(0);
}

export function chr(unicode) {
	return String.fromCharCode(unicode);
}

export function compareTo(lhs, rhs) {
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

export function *zip() {
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

/** First path segment (e.g. `lean` for `/lean` or `/lean/`). Used in `/${user}/?module=…` links. */
function axiom_user() {
  if (typeof location === 'undefined' || !location.pathname) return '';
  var path = location.pathname.replace(/\/+$/, '') || '/';
  var m = path.match(/^\/([^\/]+)(?:\/.*|$)/);
  return m ? m[1] : '';
}

function textFocused(text, selectionStart) {
  var m = text.slice(selectionStart).match(/^[\w'!₀-₉]*/);
  if (m) selectionStart += m[0].length;
  var textForFocus = text.slice(0, selectionStart);
  return textForFocus.match(/(\w+)(?:\.[\w'!₀-₉]+)*$/)[0];
}

function find_and_jump(event, sections) {
  var self = event.target;

  var module = textFocused(self.value, self.selectionStart);
  console.log("module = " + module);
  var search;
  var indexOfDot = module.lastIndexOf(".");
  if (indexOfDot >= 0) {
    if (module.slice(indexOfDot + 1) == "apply") {
      module = module.slice(0, indexOfDot);
      module += "&apply=0";
    }
    search = `?module=${module}`;
  } else {
    if (sections.includes(module)) search = `?module=${module}`;
    else search = `?mathlib=${module}`;
  }

  if (event.ctrlKey) location.search = search;
  else {
    var { origin, pathname } = location;
    window.open(origin + pathname + search, "_blank");
  }
}

function getDisplayMode(latex) {
  var displayMode = null;
  if (latex.slice(0, 2) == "\\[" && latex.slice(-2) == "\\]") {
    latex = latex.slice(2, -2);
    displayMode = true;
  } else if (latex.slice(0, 2) == "\\(" && latex.slice(-2) == "\\)") {
    latex = latex.slice(2, -2);
    displayMode = false;
  }
  return { displayMode, latex };
}

function render(latex) {
  try {
    var { displayMode, latex } = getDisplayMode(latex);
    if (displayMode !== null)
      return katex.renderToString(latex, { throwOnError: true, displayMode });
  } catch (error) {
    console.log(error);
  }
}

const latex = {
  mounted(el, binding) {
    var { value: latex } = binding;
    if (latex) {
      var { block, inline } = binding.modifiers;
      var displayMode = null;
      if (block) displayMode = true;
      else if (inline) displayMode = false;
      if (displayMode === null) {
        var { displayMode, latex } = getDisplayMode(latex);
        if (displayMode === null) return;
      }
      katex.render(latex, el, {
        displayMode,
        throwOnError: false,
        errorColor: "#ff0000",
      });
    } else {
      renderMathInElement(el, {
        delimiters: [
          { left: "$$", right: "$$", display: true },
          { left: "\\[", right: "\\]", display: true },
          { left: "$", right: "$", display: false },
          { left: "\\(", right: "\\)", display: false },
        ],
        throwOnError: false,
        errorColor: "#ff0000",
      });
    }
  },
};

latex.updated = function (el, binding) {
  if (binding.oldValue === binding.value) return;
  latex.mounted(el, binding);
};

if (typeof window !== "undefined") {
  window.ord = ord;
  window.chr = chr;
  window.zip = zip;
  window.axiom_user = axiom_user;
  window.textFocused = textFocused;
  window.find_and_jump = find_and_jump;
  window.getDisplayMode = getDisplayMode;
  window.render = render;
  window.latex = latex;
}

export { axiom_user, textFocused, find_and_jump, getDisplayMode, render, latex };
