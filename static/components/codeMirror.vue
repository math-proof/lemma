<template>
    <textarea ref=textarea :name=name placeholder="">{{text}}</textarea>
</template>

<script>
console.log('import codeMirror.vue');
//import CodeMirror from "../codemirror/lib/codemirror.js"

export default {
    data() {
        return {
            editor: null,
        };
    },
    
    props: ['text', 'name', 'style', 'index', 'theme', 'focus', 'lineNumbers', 'styleActiveLine', 'breakpoint'],

    created() {
    	var codeMirror = this.$parent.codeMirror;
    	if (codeMirror)
        	codeMirror[this.index] = this;
    },
    
    computed: {
    	rows() {
    		console.log('rows = ', this.text.length);
    		return this.text.length;
    	},
    	
    	cols() {
    		console.log('cols = ', Math.max(...this.text.map(text => text.length)));
    		return Math.max(...this.text.map(text => text.length));
    	},
    	
    	breakpointArray() {
    		var array = [];
			for (let line = 0; line < this.breakpoint.length; ++line){
				if (this.breakpoint[line]){
					array.push(line);
				}
			}
    		return array;
    	},
    	
    	lastSibling() {
    		return this;	
    	},
    	
    	firstSibling() {
    		return this;	
    	},
    	
        user() {
            return axiom_user();
        },
        
        module() {
            return document.querySelector('title').textContent;
        },
        
        hash() {
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },
    },
    
	methods: {
		resume() {
			this.$parent.resume();
		},
		
		save() {
			this.$parent.save();
		},
		
		debug() {
			this.$parent.debug();
		},
		
		set_breakpoint(index){
			this.$parent.set_breakpoint(index);
		},

		clear_breakpoint(index){
			this.$parent.clear_breakpoint(index);
		},

		showBreakPoint() {
			if (!this.breakpoint)
				return;
				
			for (let line of this.breakpointArray){
				this.editor.addLineClass(line, "gutter", "breakpoint");
			}
		},		
		
		showExecutionPoint(previousPoint, currentPoint){
    		this.editor.setCursor(currentPoint, 4);
    		this.editor.addLineClass(currentPoint, "class", "executionPoint");
    		
    		if (previousPoint >= 0)
    			this.editor.removeLineClass(previousPoint, "class", "executionPoint");
		},
	},
	
    mounted() {
		var self = this;

		function preppend(prefix) {
			if (prefix == '.')
				return prefix;
			var section = self.open_lemma_sections;
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
			return list.length;
		}

		async function F3(cm, refresh) {
		    var cursor = cm.getCursor();
		    var text = cm.getLine(cursor.line);
			var prefix = text.slice(0, cursor.ch) + text.slice(cursor.ch).match(/^[\w'!₀-₉]*/)[0];
			var postfix = text.slice(prefix.length);
		    var m = prefix.match(/([\w'!₀-₉]+)(?:\.[\w'!₀-₉]+)*$/);
		    var module = m[0];
			m = module.match(/^Lemma\.(.+)/);
			if (m)
				module = m[1];
			var [table, module] = await get_table_of_module(module, postfix);
			var url = `?${table}=${module}`;
			if (refresh)
				location.href = url;
			else
				window.open(url);
		}
		
		async function get_table_of_module(module, postfix) {
			var symbol = null;
			var table = 'module';
			if (module.indexOf('.') < 0) {
				if (!module.fullmatch(self.regexp_section)) {
					var symbol = module;
					module = await disambiguate_module(symbol);
					if (module == null){
						if (await select_mathlib(symbol.replace('.', '\\.'), 'regexp'))
							return ['mathlib', symbol];
						module = self.module.split(/[./]/)[0] + '.' + symbol;
					}
					m = postfix.match(/\.([\w'!₀-₉]+)/);
					symbol = m? m[1]: null;
				}
			}
			else {
				m = module.match(/^([\w'!₀-₉]+)\.(.+)/);
				if (m[1].fullmatch(self.regexp_section)) {
					if (!await form_post('php/request/disambiguate.php', {module: m[2]}))
						table = (await select_mathlib(module))? 'mathlib': 'module';
				}
				else{
					if (await select_mathlib(module))
						table = 'mathlib';
					else {
						var char = postfix.match(/^\.[A-Z]/)? '\\.': '$|\\.';
						var regexp = `^([\\w''!₀-₉]+)\\.${module.replace(/\.[a-z][^.]+$/, '').replace('.', '\\.')}(?=${char})`;
						var regexp_mysql = regexp.replace(/\\/g, "\\\\");
						var sql = `
select 
	regexp_replace(module, "${regexp_mysql}.*", '$1')
from 
	axiom.lemma
where 
	module regexp "${regexp_mysql}"`;
						console.log('sql =', sql);
						var section = await form_post(`php/request/execute.php`, {sql});
						section = section.map(s => s[0]);
						section = [...new Set(section)];
						if (section.length > 1) {
							var root = self.$parent.$parent;
							var sectionIntersect = section.array_intersect(root.open_sections);
							if (sectionIntersect.length) {
								section = sectionIntersect;
								if (section.length > 1) {
									regexp = new RegExp(regexp);
									for (var $import of root.imports) {
										var m = $import.match(/^Lemma\.(.+)/);
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
						[section] = section;
						module = section + '.' + module;
					}
				}
			}
			if (symbol)
				module += `#${symbol}`;
			return [table, module];
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
						else
							hit = selectionStart;
						break;
					case ']':
						if (group_count['['])
							--group_count['[']
						else
							hit = selectionStart;
						break;
					case '}':
						if (group_count['}']) 
							--group_count['}'];
						else
							hit = selectionStart;
						break;
				}
				if (hit) {
					// replace the unmatch right parenthesis/bracket/brace with the current closing punctuation
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

			"Ctrl-I": function(cm) {
				var cursor = cm.getCursor();
    			var currentLine = cursor.line;
    			// // Start from the beginning of the document
    			// var from = { line: 0, ch: 0 };
    			// // End at the last character of the current line
    			// var to = { line: currentLine, ch: cm.getLine(currentLine).length };
    			// // Get all text in this range
    			// var text = cm.getRange(from, to);
				self.code_generation(currentLine);
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
                return cm.extendSelection(CodeMirror.Pos(cm.lastLine()));
            },

            'Ctrl-Home': cm => {
                cm = self.firstSibling.editor;
                cm.focus();
                return cm.extendSelection(CodeMirror.Pos(cm.firstLine(), 0));
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
        
        if (typeof CodeMirror == 'undefined')
        	return;
        
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
								m = !prefix.match(new RegExp(`^(${self.regexp_section.source})`, 'g'));
							} else {
								m = prefix.match(/([\w.]*\.)(\w*)$/);
								var [_, prefix, phrase] = m;
								m = prefix.match(/^(\w*)\.$/);
								m = !m || m && !m[1].fullmatch(self.regexp_section);
							}
							if (m)
								prefix = preppend(prefix);
							if (prefix.isArray) {
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
						window.open(title.replace('Ctrl/Click👉', ''), '_blank');
				}
			}
		}, { capture: true });

		wrapper.addEventListener('mouseover', async function(e) {
			let target = e.target;
			if (!target.classList.contains('cm-variable') && !target.classList.contains('cm-property') || target.title)
				return;
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
			var args = await get_table_of_module(tokens.join('.'), '');
			if (!args)
				return;
			var [table, module] = args;
			var url = "Ctrl/Click👉\n" + location.origin + location.pathname + `?${table}=${module}`;
			for (let sibling of siblings)
				sibling.title = url;
			// the title is not shown up immediately, so we replace the target element to force the browser to refresh the tooltip
			target.replaceWith(target);
		});

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
    },
}
</script>

<style>
.CodeMirror {
    /*overflow-y: visible; */
    height: auto !important;
    width: auto !important;
}

.CodeMirror-scroll {
	/* Set scrolling behaviour here */
	overflow: auto;
	max-height: 2000px;
}

.CodeMirror-focused .CodeMirror-selected {
	background: rgb(0, 120, 215);
}

.executionPoint > pre > span {
	background-color: #5a5;
}

</style>