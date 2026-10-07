/** Lean CodeMirror mount hook and trivial computeds shared by renderLean. */

function ensureCodeMirror() {
	if (!window.__cmReady) {
		const base = document.baseURI;
		const paths = [
			'static/codemirror/lib/codemirror.js',
			'static/codemirror/mode/lean/lean.js',
			'static/codemirror/addon/selection/active-line.js',
			'static/codemirror/addon/hint/show-hint.js',
			'static/codemirror/addon/edit/matchbrackets.js',
			'static/codemirror/addon/comment/comment.js',
		];
		window.__cmReady = import(new URL(paths[0], base).href).then(() =>
			Promise.all(paths.slice(1).map((p) => import(new URL(p, base).href)))
		);
	}
	return window.__cmReady;
}

/** Dotted lemma path with a capitalised segment (not a local like `h₀` or `μ.bind`). */
export function isOpenStrippedLemmaName(name) {
	return /(^|\.)[A-Z]/.test(name);
}

/**
 * `open` in the page payload is `[["Random"]]`, sometimes a flat list, sometimes
 * a JSON string. `open_sections` only spreads values whose `.isArray` flag is set,
 * so a plain array yields no namespaces and F3 falls through to the DB.
 */
export function flattenOpens(open) {
	var out = [];
	function pushToken(token) {
		if (token == null)
			return;
		if (Array.isArray(token)) {
			for (var item of token)
				pushToken(item);
			return;
		}
		if (typeof token != 'string')
			return;
		var text = token.trim();
		if (!text)
			return;
		if (text[0] == '[' || text[0] == '{') {
			try {
				pushToken(JSON.parse(text));
				return;
			}
			catch (e) {
				/* not JSON; treat as a namespace token */
			}
		}
		if (/\s/.test(text)) {
			for (var part of text.split(/\s+/))
				pushToken(part);
			return;
		}
		if (text == 'scoped' || text == 'hiding' || text == 'renaming')
			return;
		out.push(text);
	}
	pushToken(open);
	var seen = new Set();
	return out.filter(ns => {
		if (!ns || seen.has(ns))
			return false;
		seen.add(ns);
		return true;
	});
}

/** null unless `result` is a `[table, module]` pair. Destructuring anything else throws. */
export function moduleLinkTarget(result) {
	if (!Array.isArray(result) || result.length < 2)
		return null;
	if (result[0] == null || result[1] == null || result[1] === '')
		return null;
	return [result[0], result[1]];
}

/**
 * Dotted lemma under the cursor, including segments to the right of the caret.
 * F3 used to stop at the current segment, so `GradV.eq.AddSum…` never matched
 * the imported `…In_Ico` module.
 */
export function dottedIdentifierAt(text, ch) {
	if (text == null)
		return null;
	ch = Math.max(0, Math.min(ch == null ? 0 : ch, text.length));
	var right = text.slice(ch);
	var wordRest = (right.match(/^[\w'!₀-₉]*/) || [''])[0];
	var prefix = text.slice(0, ch) + wordRest;
	var head = prefix.match(/([\w'!₀-₉]+)(?:\.[\w'!₀-₉]+)*$/);
	if (!head)
		return null;
	var afterWord = text.slice(prefix.length);
	var tail = (afterWord.match(/^(?:\.[\w'!₀-₉]+)*/) || [''])[0];
	var module = head[0] + tail;
	if (module.startsWith('.'))
		return null;
	return {
		module,
		postfix: afterWord.slice(tail.length),
	};
}

/** Prefix of `full` when `short` is `full` with that prefix and a dot removed. */
export function lemmaSuffixPrefix(full, short) {
	if (!full || !short || full == short)
		return null;
	var tail = '.' + short;
	if (full.endsWith(tail))
		return full.slice(0, -tail.length);
	return null;
}

function lemmaModuleOfImport(imp) {
	var s = String(imp).trim().split(/\s+/)[0];
	if (s.startsWith('Lemma.'))
		return s.slice('Lemma.'.length);
	return null;
}

/**
 * `open Foo` makes `Foo.A.B` legal as `A.B`. If an import is exactly that
 * full module and `Foo` is opened, return the full module.
 */
export function resolveOpenedImport(short, opens, imports) {
	if (!short || !opens || !opens.length || !imports)
		return null;
	var best = null;
	var bestIdx = -1;
	for (var imp of imports) {
		var full = lemmaModuleOfImport(imp);
		if (!full)
			continue;
		var prefix = lemmaSuffixPrefix(full, short);
		if (!prefix)
			continue;
		var idx = opens.lastIndexOf(prefix);
		if (idx > bestIdx) {
			bestIdx = idx;
			best = full;
		}
	}
	return best;
}

/** `{section, rest, full, ns}` for each opened namespace whose head is a lemma section. */
export function openNamespaceCandidates(short, opens, isSection) {
	var out = [];
	if (!short || !opens)
		return out;
	for (var ns of opens) {
		if (!ns || /[\s()]/.test(ns))
			continue;
		var qualified = ns + '.' + short;
		var m = qualified.match(/^([\w'!₀-₉]+)\.(.+)/);
		if (isSection && !isSection(m[1]))
			continue;
		out.push({
			ns,
			section: m[1],
			rest: m[2],
			full: qualified,
		});
	}
	return out;
}

/** Escape every dot so the section-lookup regexp matches a literal module path. */
export function moduleRegexpBody(variant) {
	return variant.replace(/\.[a-z][^.]+$/, '').replace(/\./g, '\\.');
}

/** Latest `open` wins when several opened namespaces contain the same suffix. */
export function pickLatestOpen(found, opens) {
	var best = null;
	var bestIdx = -1;
	for (var item of found) {
		var idx = opens.lastIndexOf(item.ns);
		if (idx > bestIdx) {
			bestIdx = idx;
			best = item.full;
		}
	}
	return best;
}

/**
 * Qualify `short` from `open` before any axiom.lemma regexp.
 * `disambiguate(rest, section)` is the filesystem lookup (disambiguate.php).
 * A miss is null, never undefined.
 */
export async function qualifyOpenedModule(short, opens, imports, disambiguate, isSection) {
	if (!isOpenStrippedLemmaName(short))
		return null;
	opens = flattenOpens(opens);
	if (!opens.length)
		return null;
	var imported = resolveOpenedImport(short, opens, imports || []);
	if (imported)
		return imported;
	var candidates = openNamespaceCandidates(short, opens, isSection || null);
	if (!candidates.length && isSection)
		candidates = openNamespaceCandidates(short, opens, null);
	if (!candidates.length)
		return null;
	var found = [];
	await Promise.all(candidates.map(async c => {
		try {
			var section = await disambiguate(c.rest, c.section);
			section = section == null ? '' : String(section).trim();
			if (section == c.section)
				found.push(c);
		}
		catch (e) {
			console.log(e);
		}
	}));
	return pickLatestOpen(found, opens);
}

/**
 * Section names from the axiom.lemma regexp query.
 * A failed execute is `0` or missing; an empty hit is `[]`. Always an array.
 */
export function regexpSectionNames(rows) {
	if (!Array.isArray(rows))
		return [];
	var section = [];
	for (var row of rows) {
		var name = Array.isArray(row) ? row[0] : row;
		if (name != null && name !== '')
			section.push(String(name));
	}
	return [...new Set(section)];
}

export function cmComputedUser() {
	return axiom_user();
}

export function cmComputedModule() {
	return document.querySelector('title').textContent;
}

export function codeMirrorMounted() {
		var self = this;

		function preppend(prefix) {
			if (prefix == '.')
				return prefix;
			var section = self.$parent.sections;
			if (!section || !section.length)
				section = [self.module.split(/[\/.]/)[0]];
			switch (section.length) {
			case 0:
				section = [self.module.split(/[\/.]/)[0]];
			case 1:
				return `${section[0]}.${prefix}`;
			default:
				return section.map(section => `${section}.${prefix}`);
			}
		}

		async function disambiguate_module(module) {
			var section = await form_post('php/request/disambiguate.php', {module});
			if (!section)
				return null;
			return section + '.' + module;
		}
		
		async function select_mathlib(module, op='=') {
			var sql = `
select 
  name 
from 
  mathlib
where 
  name ${op} "${module}"`;
			var list = await form_post(`php/request/execute.php`, {sql});
			return Array.isArray(list) && list.length > 0;
		}

		function knownSection(name) {
			try {
				var re = self.regexp_section;
				if (!re || name == null)
					return false;
				return !!String(name).fullmatch(re);
			}
			catch (e) {
				return false;
			}
		}

		async function F3(cm, refresh) {
			try {
				var cursor = cm.getCursor();
				var hit = dottedIdentifierAt(cm.getLine(cursor.line), cursor.ch);
				if (!hit)
					return;
				var module = hit.module;
				var lemma = module.match(/^Lemma\.(.+)/);
				if (lemma)
					module = lemma[1];
				var target = moduleLinkTarget(await get_table_of_module(module, hit.postfix));
				if (!target)
					return;
				var url = `?${target[0]}=${target[1]}`;
				if (refresh)
					location.href = url;
				else
					window.open(url);
			}
			catch (e) {
				console.log(e);
			}
		}

		function *yield_modules(module) {
			yield module;
			let m;
			if (m = module.match(/^(.+)\.eq\.Cast_([^.]+)(.*)$/))
				yield m[1] + '.as.' + m[2] + m[3];
		}

		function safeGet(node, key) {
			try {
				return node == null ? undefined : node[key];
			}
			catch (e) {
				return undefined;
			}
		}

		function pushList(into, value) {
			if (value == null)
				return;
			if (typeof value == 'string') {
				try {
					value = JSON.parse(value);
				}
				catch (e) {
					into.push(value);
					return;
				}
			}
			if (Array.isArray(value))
				into.push(...value);
		}

		/** Opens and imports from the Vue parent chain and the hidden form fields. */
		function collectOpenContext() {
			var opens = [];
			var imports = [];
			var node = self;
			var guard = 0;
			while (node && guard++ < 12) {
				opens.push(...flattenOpens(safeGet(node, 'open')));
				opens.push(...flattenOpens(safeGet(node, 'open_sections')));
				opens.push(...flattenOpens(safeGet(node, 'open_lemma_sections')));
				pushList(imports, safeGet(node, 'imports'));
				node = safeGet(node, '$parent');
			}
			if (typeof document != 'undefined') {
				var openInput = document.querySelector('input[name=open]');
				var importInput = document.querySelector('input[name=imports]');
				if (openInput)
					opens.push(...flattenOpens(openInput.value));
				if (importInput)
					pushList(imports, importInput.value);
			}
			return {
				opens: flattenOpens(opens),
				imports,
			};
		}

		// `open Foo` drops the `Foo.` prefix, so the name does not start with a
		// lemma section and the fully-qualified filesystem lookup never runs.
		async function qualifyByOpen(short) {
			var ctx = collectOpenContext();
			return qualifyOpenedModule(
				short,
				ctx.opens,
				ctx.imports,
				(rest, section) => form_post('php/request/disambiguate.php', {
					module: rest,
					section,
				}),
				name => knownSection(name),
			);
		}

		async function sectionByRegexp(variant, postfix) {
			postfix = postfix || '';
			var char = postfix.match(/^\.[A-Z]/)? '\\.': '$|\\.';
			var body = moduleRegexpBody(variant);
			var regexp = `^([\\w''!₀-₉]+)\\.${body}(?=${char})`;
			var regexp_mysql = regexp.replace(/\\/g, "\\\\");
			var sql = `
select 
	regexp_replace(module, "${regexp_mysql}.*", '$1')
from 
	axiom.lemma
where 
	module regexp "${regexp_mysql}"`;
			console.log('sql =', sql);
			var section = regexpSectionNames(await form_post(`php/request/execute.php`, {sql}));
			if (!section.length)
				return null;
			if (section.length > 1) {
				var opened = collectOpenContext().opens;
				var sectionIntersect = section.array_intersect(opened);
				if (sectionIntersect.length) {
					section = sectionIntersect;
					if (section.length > 1) {
						regexp = new RegExp(regexp);
						for (var $import of collectOpenContext().imports) {
							var m = String($import).match(/^Lemma\.(.+)/);
							if (m) {
								m = m[1].match(regexp);
								if (m) {
									if (section.includes(m[1])) {
										section = [m[1]];
										break;
									}
								}
							}
						}
					}
				}
			}
			return section[0] || null;
		}

		async function get_table_of_module(module, postfix) {
			if (module == null || module === '')
				return null;
			var symbol = null;
			var table = 'module';
			var m;
			if (module.indexOf('.') < 0) {
				if (!knownSection(module)) {
					var symbol = module;
					var qualified = await qualifyByOpen(symbol);
					if (qualified)
						module = qualified;
					else {
						module = await disambiguate_module(symbol);
						if (module == null){
							var inMathlib = false;
							try {
								inMathlib = await select_mathlib(symbol.replace('.', '\\.'), 'regexp');
							}
							catch (e) {
								console.log(e);
							}
							if (inMathlib)
								return moduleLinkTarget(['mathlib', symbol]);
							module = self.module.split(/[./]/)[0] + '.' + symbol;
						}
					}
					m = postfix && postfix.match(/\.([\w'!₀-₉]+)/);
					symbol = m? m[1]: null;
				}
			}
			else {
				m = module.match(/^([\w'!₀-₉]+)\.(.+)/);
				if (!m)
					return null;
				if (knownSection(m[1])) {
					if (!await form_post('php/request/disambiguate.php', {module: m[2]})) {
						var inMathlib = false;
						try {
							inMathlib = await select_mathlib(module);
						}
						catch (e) {
							console.log(e);
						}
						table = inMathlib ? 'mathlib' : 'module';
					}
				}
				else{
					var resolved = null;
					for (var variant of yield_modules(module)) {
						try {
							resolved = await qualifyByOpen(variant);
							if (resolved)
								break;
							var inMathlib = false;
							try {
								inMathlib = await select_mathlib(variant);
							}
							catch (e) {
								console.log(e);
							}
							if (inMathlib) {
								table = 'mathlib';
								resolved = variant;
								break;
							}
							var section = await sectionByRegexp(variant, postfix);
							if (section) {
								resolved = section + '.' + variant;
								break;
							}
						}
						catch (e) {
							console.log(e);
						}
					}
					if (!resolved)
						return null;
					module = resolved;
				}
			}
			if (symbol)
				module += `#${symbol}`;
			return moduleLinkTarget([table, module]);
		}

		function open(cm, pair) {
			cm.replaceSelection(pair[0]);

			var cursor = cm.getCursor();
			console.log("cursor.ch = " + cursor.ch);

			var text = cm.getLine(cursor.line);

			var group_count = {
				'(': 0,
				'[': 0,
				'{': 0,
			};
			// scan for unmatch right parenthesis/bracket/brace and replace it with the current closing punctuation
			var hit = null;
			var left, right;
			for (var selectionStart of range(cursor.ch, text.length)) {
				var char = text[selectionStart];
				switch (char) {
					case '(':
					case '[':
					case '{':
						++group_count[char];
						break;
					case ')':
						if (group_count['('])
							--group_count['('];
						else {
							hit = selectionStart;
							left = '(';
							right = char;
						}
						break;
					case ']':
						if (group_count['['])
							--group_count['[']
						else {
							hit = selectionStart;
							left = '[';
							right = char;
						}
						break;
					case '}':
						if (group_count['}']) 
							--group_count['}'];
						else {
							hit = selectionStart;
							left = '{';
							right = char;
						}
						break;
				}
				if (hit) {
					// replace the unmatch right parenthesis/bracket/brace with the current closing punctuation
					var group_count_start = 0;
					for (var i = 0; i < hit; ++i) {
						var char = text[i];
						if (char == left)
							++group_count_start;
						else if (char == right)
							--group_count_start;
					}
					let min = left == pair[0]? 2 : 1;
					if (group_count_start >= min)
						break;

					var {line} = cursor;
					cm.replaceRange(
						pair[1],
						{line, ch: hit},
						{line, ch: hit + 1},
					);
					cm.setCursor(cursor.line, hit + 1);
					return;
				}
			}
			var selectionStart = cursor.ch;
			var left_parenthesis_count = 0;
			var left_bracket_count = 0;
			var left_brace_count = 0;

			if (text[selectionStart] != '.') {
				for (; selectionStart < text.length; ++selectionStart) {
					var char = text[selectionStart];
					if (char.isalpha() || char.isdigit())
						continue;
					switch (char) {
						case '_':
						case '.':
							continue;
						case '(':
							++left_parenthesis_count;
							continue;
						case '[':
							++left_bracket_count;
							continue;
						case '{':
							++left_brace_count;
							continue;

						case ')':
							if (left_parenthesis_count) {
								--left_parenthesis_count;
								continue;
							}
							else
								break;
						case ']':
							if (left_bracket_count) {
								--left_bracket_count;
								continue;
							}
							else
								break;
						case '}':
							if (left_brace_count) {
								--left_brace_count;
								continue;
							}
							else
								break;
						default:
							if (left_parenthesis_count || left_bracket_count || left_brace_count)
								continue;
					}
					break;
				}
			}
			cm.setCursor(cursor.line, selectionStart);
			cm.replaceSelection(pair[1]);
			cm.setCursor(cursor.line, selectionStart);
		}

		function close(cm, ch) {
			var cursor = cm.getCursor();
			if (cursor.ch < cm.getLine(cursor.line).length && cm.getTokenAt({ ch: cursor.ch + 1, line: cursor.line }).string == ch)
				cm.setCursor(cursor.line, cursor.ch + 1);
			else
				cm.replaceSelection(ch);
		}

		var extraKeys = {
			Tab(cm) {
				cm.replaceSelection(' '.repeat(cm.getOption('indentUnit')));
			},

			'Alt-Left': function(cm) {
				history.go(-1);
			},

			'Alt-Right': function(cm) {
				history.go(1);
			},

			Alt(cm) {
			},

			"[": function(cm) {
				open(cm, '[]');
			},

			"]": function(cm) {
				close(cm, ']');
			},

			"Shift-9": function(cm) {
				open(cm, '()');
			},

			"Shift-0": function(cm) {
				close(cm, ')');
			},

			"Shift-[": function(cm) {
				open(cm, '{}');
			},

			"Shift-]": function(cm) {
				close(cm, '}');
			},

			"Alt-/": function(cm) {
				return cm.showHint();
			},

			Space(cm) {
				var cur = cm.getCursor();
				var line = cm.getLine(cur.line);
				var text = line.slice(0, cur.ch);
				var m = text.match(/\\[\w.|<>=^~{} \\+\p{Script=Greek}-]+$/u);
				if (m) {
					var prefix = m[0];
					console.log('prefix = ' + prefix);
					return cm.showHint();
				}
				else 
					cm.replaceSelection(' ');
			},

			"Ctrl-/": function(cm) {
				return cm.toggleComment();
			},

			'.': function(cm) {
				cm.replaceSelection('.');
				return cm.showHint();
			},

            'Ctrl-O': function(cm) {
				self.new_file();
            },

            'Ctrl-S': function(cm) {
				self.save();
            },

			'F5': function(cm) {
            },

            'Shift-Alt-W': function(cm) {
				self.openContainingFolder();
            },
            
            'Alt-D': function(cm) {
				const {Pos, deleteNearSelection, clipPos} = CodeMirror;
				deleteNearSelection(cm, range => ({
    				from: Pos(range.from().line, 0),
    				to: clipPos(cm.doc, Pos(cm.lineCount() + 1, 0))
  				}));
				var parent = self.$parent.$parent;
				var {index} = self;
				var i = index.back();
				if (i.isInteger) {
					var list = getitem(parent.renderLean, ...index.slice(0, -1));
					var pre_indices = index.slice(0, -1);
					for (let t = list.length - 1; t > i; --t) {
						parent.delete([...pre_indices, t]);
					}
					list.length = i;
				}
            },

            Left(cm) {
                cm.moveH(-1, "char");
                if (cm.getCursor().hitSide) {
                    cm.focus();
                    CodeMirror.commands.goDocEnd(cm);
                }
            },

            Right(cm) {
                cm.moveH(1, "char");
				if (cm.getCursor().hitSide) {
					cm = extraKeys.Down(cm);
					cm.focus();
					CodeMirror.commands.goDocStart(cm);
				}
            },

            Down(cm) {
                var cursor = cm.getCursor();
                if (cursor.line + 1 < cm.lineCount())
                    return cm.moveV(1, "line");

                cm = self.nextSibling.editor;
                cm.focus();
                if (cursor.ch == 0) {
                    var linesToMove = cm.getCursor().line;
                    for (let i = 0; i < linesToMove; ++i)
                        cm.moveV(-1, "line");
                }
                else
                    cm.setCursor(0, cursor.ch);
            },

            Up(cm) {
                var cursor = cm.getCursor();
                if (cursor.line > 0)
                    return cm.moveV(-1, "line");
                cm = self.previousSibling.editor;
				cm.focus();
				if (cursor.ch == 0) {
					var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
					for (let i = 0; i < linesToMove; ++i)
						cm.moveV(1, "line");
				} 
				else if (cm.lineCount)
					cm.setCursor(cm.lineCount() - 1, cursor.ch);
				else
					cm.selectionStart = cm.selectionEnd = cursor.ch;
            },

            Enter(cm) {
				var cur = cm.getCursor();
				var {ch, line} = cur;
				var line = cm.getLine(cur.line);
				var former = line.slice(0, cur.ch);
				var latter = line.slice(cur.ch);
				var space = space = former.match(/^ */)[0];
				if (latter.isspace()) {
					if (space.length >= latter.length)
						space = ' '.repeat(space.length - latter.length);
					else
						space = '';
				}
				cm.replaceSelection("\n" + space);
            },

            "Ctrl-Enter": cm => {
                CodeMirror.commands.newlineAndIndent(cm);
            },
            
            PageUp(cm) {
                var cursor = cm.getCursor();
                if (cursor.line >= 18)
                    return cm.moveV(-1, "page");
                
                cm = self.previousSibling.editor;
                cm.focus();
                if (cursor.ch == 0 || i == 0) {
                    var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
                    for (let i = 0; i < linesToMove; ++i)
                        cm.moveV(1, "line");
                }
                else
                    cm.setCursor(cm.lineCount() - 1, cursor.ch);
            },

            PageDown(cm) {
                var cursor = cm.getCursor();
                if (cursor.line + 18 < cm.lineCount())
                    return cm.moveV(1, "page");

                var cm = self.nextSibling.editor;
                cm.focus();

                if (cursor.ch == 0) {
                    var linesToMove = cm.getCursor().line;
                    for (let i = 0; i < linesToMove; ++i) {
                        cm.moveV(-1, "line");
                    }
                }
                else
                    cm.setCursor(0, cursor.ch);
            },
            
            F3(cm){
            	F3(cm, false);
            },

            'Ctrl-F3': cm => F3(cm, true),

            'Ctrl-End': cm => {
                cm = self.lastSibling.editor;
                cm.focus();
                cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
                // Editors grow to full height (`scrollbarStyle: null`), so the whole page
                // scrolls via the window; jump it to the document bottom as well.
                window.scrollTo(0, document.documentElement.scrollHeight);
            },

            'Ctrl-Home': cm => {
                cm = self.firstSibling.editor;
                cm.focus();
                cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
                // Return to the home of the entire page, not merely scroll the first editor into view.
                window.scrollTo(0, 0);
            },
            
			'Shift-Ctrl-B': function(cm) {
				var line = cm.getCursor().line;
				console.log('line = ', line);
				if (self.breakpoint[line]){
					cm.removeLineClass(line, "gutter", "breakpoint");
					self.clear_breakpoint(line);
				}
				else{
					cm.addLineClass(line, "gutter", "breakpoint");
					self.set_breakpoint(line);
				}
			},

			F8(cm) {
				self.resume();
			},

			Delete(cm) {
				cm.deleteH(1, "char");
			},
        };
        
        ensureCodeMirror().then(() => {
        if (typeof CodeMirror == 'undefined')
        	return console.error('[codeMirrorEditor] CodeMirror global missing after preload');
        
        this.editor = CodeMirror.fromTextArea(this.$el, {
            mode: {
                name: "lean",
                singleLineStringErrors: false
            },
            
            theme: this.theme,

            indentUnit: 2,

            matchBrackets: true,

            scrollbarStyle: null,

            extraKeys,
            
            lineNumbers: this.lineNumbers,
            
            styleActiveLine: this.styleActiveLine,

            hintOptions: { 
                hint(cm, options) {
                	var Pos = CodeMirror.Pos;
                	return new Promise(function(accept) {
                		var cur = cm.getCursor();
                		var token = cm.getTokenAt(cur);
                		var tokenString = token.string;
                		console.log('tokenString = ' + tokenString);

						var line = cm.getLine(cur.line);
						var text = line.slice(0, cur.ch);
						var prefix = text.match(/\\[\w.|<>=^~{} \\+\p{Script=Greek}-]+$|[\w.\p{Script=Greek}]+$/u)[0];

						var user = axiom_user();

						var m;
						var search_lemma = tokenString == '.' && prefix[0] != '\\' || prefix[0] =='.';
						if (search_lemma || (prefix.indexOf('.') >= 0 && prefix[0] != '\\')) {
							if (search_lemma) {
								++token.start;
								m = !(self.regexp_section && prefix.match(new RegExp(`^(${self.regexp_section.source})`, 'g')));
							} else {
								m = prefix.match(/([\w.]*\.)(\w*)$/);
								var [_, prefix, phrase] = m;
								m = prefix.match(/^(\w*)\.$/);
								m = !m || m && !m[1].fullmatch(self.regexp_section);
							}
							if (m)
								prefix = preppend(prefix);
							if (prefix != null && Array.isArray(prefix)) {
								var sql = `
select 
  distinct substring_index(substring(module from length(jt.prefix) + 1), '.', 1) as phrase
from 
  axiom.lemma 
  join 
    json_table(
      '${JSON.stringify(prefix)}', 
      '$[*]' columns(prefix varchar (${Math.max(...prefix.map(word => word.length))}) path '$')
    ) as jt
where 
  user = '${user}' and module like concat(jt.prefix, '%')`;
							} else if (prefix == '.' && (m = line.match(/^( *)\.( *)$/))) {
								--token.start;
								var constants = [`·\\n${m[1]}  sorry`];
								var sql = `
SELECT
  name
FROM
  json_table(
    '${JSON.stringify(constants)}',
    '$[*]' columns(name text path '$')
  ) as _t`;
							} else {
								var sql = `
select distinct substring_index(substring(module from length("${prefix}") + 1), '.', 1) as phrase
from 
  axiom.lemma 
where 
	user = '${user}' and module like concat("${prefix}", '%')`;
							}
							if (!search_lemma)
								sql += ` having phrase regexp '${phrase}' COLLATE utf8mb4_0900_bin order by phrase`;
						} else {
							token.start -= prefix.length - (tokenString.length - (token.end - cur.ch));
							token.end = cur.ch;
							var match_unicodedata_right_open = prefix.fullmatch(/\\N\{[A-Z\d -]+/i) && line[cur.ch] == '}';
							if (match_unicodedata_right_open || prefix.fullmatch(/\\N\{[A-Z\d -]+\}/i)) {
								if (match_unicodedata_right_open) {
									token.end += 1;
									var hint = prefix.slice(3);
									var sql = `
with _t as (
	select unicode, name from unicode where name like '%${hint}%'
)
SELECT
  CASE
    WHEN name = '${hint}' or (SELECT COUNT(*) FROM _t) = 1
      THEN unicode
    ELSE
      concat('\\\\N{', name, '}')
  END
FROM
  _t`;
								}
								else {
									var hint = prefix.slice(3, -1);
									var sql = `
SELECT
  unicode
FROM
  unicode
where name = '${hint}'`;
								}
							} else if (m = prefix.match(/^\\(.+)/)){
								var hint = m[1];
								var sql = `
with _t as (
  select 
    unicode, jt.latex
  from 
    unicode 
  cross join json_table(
    latex,
    '$[*]' COLUMNS (latex varchar(255) PATH '$')
  ) as jt
  where 
    jt.latex like binary "${hint}%"
)
select 
  CASE
    WHEN (SELECT COUNT(*) FROM _t) > 1 THEN 
      concat('\\\\', _t.latex)
    ELSE 
      unicode
  END as unicode
from 
  _t
where
  latex != "${hint}"
union
select 
  unicode
from 
  _t
where 
  latex = "${hint}"
order by char_length(unicode)`;
							} else if (m = prefix.match(/^[A-Za-z_]+$/)) {
								var {sections, typeclasses, tactics} = self.$parent.$parent;
								var constants = [...sections, ...typeclasses, ...tactics];
								var sql = `
SELECT
  name
FROM
  json_table(
    ${JSON.stringify(constants).mysqlStr()},
    '$[*]' columns(name text path '$')
  ) as _t
where name like binary '${prefix}%'`;

							} else {
								// transform an indexed variable into a human readable symbol with an integer subscript
								var sql = `
SELECT
  CONCAT(
    LEFT(name, 1),
    CHAR(CONV(hex(CONVERT('₀' USING utf16)), 16, 10) + (ASCII(RIGHT(name, 1)) - ASCII('0')) USING utf16)
  )
FROM 
  json_table(
    '["${prefix}"]',
	'$[*]' columns(name text path '$')
  ) as _t
where name REGEXP '^[\\\\p{Script=Greek}a-zA-Z][0-9]$'`;
							}
						}

						sql += "\nlimit 20";
						console.log(sql);
                		form_post(`php/request/execute.php`, {sql}).then(list => {
                			// Find the token at the cursor
							list = list.map(item => item[0]);
                			console.log('hint = ' + list);
                			return accept({
                				list,
                				from: Pos(cur.line, token.start),
                				to: Pos(cur.line, token.end)
                			});
                		});
                	});
                },  
            },
        });

        //this.editor.setSize('auto', 'auto');
        
        if (this.focus)
        	this.editor.focus();
        
		// Get the editor's wrapper element
		const wrapper = this.editor.getWrapperElement();

		// Add a capture-phase mousedown listener to intercept events early
		wrapper.addEventListener('mousedown', function(e) {
			if (e.button === 0) { // Left mouse button
				self.$parent.click_left(e);
				if (e.ctrlKey) {
					var title = e.target.title;
					if (title)
						window.open(title.slice(title.indexOf('👉') + 2), '_blank');
				}
			}
		}, { capture: true });

		wrapper.addEventListener('mouseover', async function(e) {
			let target = e.target;
			if (!target.classList.contains('cm-variable') && !target.classList.contains('cm-property') || target.title)
				return;
			try {
			await hoverLink(target);
			}
			catch (err) {
				console.log(err);
			}
		});

		async function hoverLink(target) {
			var parentElement = target.parentElement;
			// Build the URL based on the text content
			let tokens = [];
			let { children } = parentElement;
			let index = children.indexOf(target);
			var siblings = [];
			// Collect right-side properties
			for (let i = index + 1; i < children.length; ++i) {
				let sibling = children[i];
				if (sibling.classList.contains('cm-property')) {
					tokens.push(sibling.textContent);
					siblings.push(sibling);
				}
				else
					break;
			}

			// Collect left-side properties or variable
			for (let i = index; i >= 0; --i) {
				let sibling = children[i];
				if (sibling.classList.contains('cm-property')) {
					tokens.unshift(sibling.textContent);
					siblings.unshift(sibling);
				}
				else if (sibling.classList.contains('cm-variable')) {
					tokens.unshift(sibling.textContent);
					siblings.unshift(sibling);
					break;
				} else
					return;
			}
			var link = moduleLinkTarget(await get_table_of_module(tokens.join('.'), ''));
			if (!link)
				return;
			var url = "Ctrl+Click or F3👉\n" + location.origin + location.pathname + `?${link[0]}=${link[1]}`;
			for (let sibling of siblings)
				sibling.title = url;
			// the title is not shown up immediately, so we replace the target element to force the browser to refresh the tooltip
			target.replaceWith(target);
		}

        if (this.hash){
        	var line = null, col = 4;
        	if (typeof this.hash == 'number') {
        		line = this.hash;
            }
        	else {
        		var m = this.hash.match(/^(\d+)(?::(\d+))?/);
        		if (m){
        			var line = m[1];
        			line = parseInt(line) - 1;
        			if (m[2] != null)
        				col = parseInt(m[2]) - 1;
        		}
            }
            
        	if (line != null)
				return this.editor.setCursor(line, col);
			
            var regex = eval(`/((?:    )*def ${this.hash})\\([^()]+\\):\\s*$/`);

            var size = this.editor.lineCount();
            for (var index = 0; index < size; ++index) {
                var line = this.editor.getLine(index);
                //console.log(line);

                var m = line.match(regex);
                if (m) {
                	this.editor.setCursor(index, m[1].length - this.hash.length / 2);
                    break;
                }
            }
        }
        }).catch((err) => console.error('[codeMirrorEditor] mount failed', err));
}
