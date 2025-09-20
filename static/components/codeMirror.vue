<template>
    <textarea ref=textarea :name=name placeholder="">{{text}}</textarea>
</template>

<script>
console.log('import codeMirror.vue');
//import CodeMirror from "../codemirror/lib/codemirror.js"

function this_phrases() {
	return ['apply', 'args', 'expr', 'lhs', 'rhs', 'find'];
}

export default {
    data() {
        return {
            editor: null,
        };
    },
    
    props: ['text', 'name', 'style', 'index', 'theme', 'focus', 'lineNumbers', 'styleActiveLine', 'breakpoint'],

    created(){
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
    	
    	breakpointArray(){
    		var array = [];
			for (let line = 0; line < this.breakpoint.length; ++line){
				if (this.breakpoint[line]){
					array.push(line);
				}
			}
    		return array;
    	},
    	
    	lastSibling(){
    		return this;	
    	},
    	
    	firstSibling(){
    		return this;	
    	},
    	
        user(){
            return axiom_user();
        },
        
        module(){
            return document.querySelector('title').textContent;
        },
        
        hash(){
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },
    },
    
	methods: {
		resume(){
			this.$parent.resume();
		},
		
		save(){
			this.$parent.save();
		},
		
		debug(){
			this.$parent.debug();
		},
		
		set_breakpoint(index){
			this.$parent.set_breakpoint(index);
		},

		clear_breakpoint(index){
			this.$parent.clear_breakpoint(index);
		},

		showBreakPoint(){
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
		
		EqVariables(phrase){
			var list = new Set();
			for (let editor of this.$parent.renderProve) {
				var text = editor.editor.getValue();
				for (var text of text.split("\n")) {
					console.log(text);
					for (let m of text.matchAll(/\bEq\.(\w+)/g)) {
						var word = m[1];
						if (phrase && !word.startsWith(phrase)){
							continue;
						}
						
						list.add(word);
					}
				}
			}

			list = Array.from(list);
			list.sort();
			console.log('list = ' + list);
			return list;			
		},
		
	},
	
    mounted() {
		var self = this;
		
		function locate_definition(cm, index, symbol) {
		    var regex = eval(`/(?:    )*from Lemma\\.(.+) import ${symbol}\\b/`);

		    for (; index >= 0; --index) {
		        var line = cm.getLine(index);
		        console.log(line);

		        var m = line.match(regex);
		        if (m) {
		            return m[1];
		        }
		    }
		}
		
		function F3(cm, refresh) {
		    var cursor = cm.getCursor();
		    console.log("cursor.ch = " + cursor.ch);

		    var text = cm.getLine(cursor.line);

		    var selectionStart = cursor.ch;
		    console.log("selectionStart = " + selectionStart);

		    for (; selectionStart < text.length; ++selectionStart) {
		        var char = text[selectionStart];
		        if (char >= 'a' && char <= 'z' ||
		            char >= 'A' && char <= 'Z' ||
		            char == '_' ||
		            char >= '0' && char <= '9') {
		            continue;
		        }
		        else {
		            break;
		        }
		    }

		    var textForFocus = text.slice(0, selectionStart);
		    var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
		    var module = m[0];
		    console.log('module = ' + module);
		    switch (module) {
		        case 'apply':
		        	self.$parent.open_apply();
		            break;

		        case 'prove':
		            break;

		        default:
		            var m = module.match(/(.+)\.apply$/);
		            if (m) {
		                module = m[1];
		                var apply = true;
		            }
		            else
		                var apply = false;

		            m = module.match(/^Lemma\.(.+)/);
		            if (m)
		                module = m[1];

		            var symbol = null;

		            if (module.indexOf('.') < 0) {
		                if (!sections.includes(module)) {
							var symbol = module;
							module = locate_definition(cm, cursor.line, symbol);
							if (module == null) {
								var href = `/axiom/?symbol=${symbol}`;
								if (refresh)
									location.href = href;
								else
									window.open(href);
								return;
							}
		                }
		            }
		            else {
		                m = module.match(/^(\w+)\.(.+)/);
		                if (!sections.includes(m[1]))
							return;
		            }

		            var user = axiom_user();
                    var href = user? `/${user}/?module=${module}`: location.href.replace(self.module.replace(/\./g, '/'), module.replace(/\./g, '/')).replace(/#\w+$/, '');

		            if (apply)
		                href += "#apply";
		            else if (symbol)
		                href += `#${symbol}`;
		            else if (!user && text.slice(selectionStart).match(/^\.(?!apply\b)\w+/))
	            		href = href.slice(0, -5);

		            if (refresh)
		                location.href = href;
		            else
		                window.open(href);

		            break;
		    }
		}
		
		function open(cm, ch) {
			var [first, second] = ch.split('');
			cm.replaceSelection(first);

			var cursor = cm.getCursor();
			console.log("cursor.ch = " + cursor.ch);

			var text = cm.getLine(cursor.line);

			var selectionStart = cursor.ch;
			console.log("selectionStart = " + selectionStart);

			var left_parenthesis_count = 0;
			var left_bracket_count = 0;
			var left_brace_count = 0;
			if (text[selectionStart] != '.') {
				for (; selectionStart < text.length; ++selectionStart) {
					var char = text[selectionStart];

					if (char >= 'a' && char <= 'z' || char >= 'A' && char <= 'Z') {
						continue;
					}

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
			cm.replaceSelection(second);
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

			".": function(cm) {
				cm.replaceSelection('.');
				return cm.showHint();
			},

            'Ctrl-O': function(cm) {
                console.log("'Ctrl-O' is pressed! self.module = ", self.module);
                var module = self.module;
                if (module.match(/\W$/))
                	module = module.slice(0, -1);
                
                var href = `/lean/?new=${module}`;
                window.open(href);
            },

            'Ctrl-S': function(cm) {
            	self.save();
            },

            'Ctrl-F5': function(cm) {
                form.submit();
            },

            'Shift-Alt-W': function(cm) {
                console.log('Shift-Alt-W');
                var search = location.search;
                var index = search.lastIndexOf('.') + 1;
                if (!index)
                    index = search.lastIndexOf('/') + 1;
                
                location.hash = search.substring(index);
                location.search = search.substring(0, index);
            },
            
            Left(cm) {
                cm.moveH(-1, "char");
                if (cm.getCursor().hitSide) {
                    if (i == 0) {
                        cm = self.$parent.$refs.apply;
                    }
                    cm = cm.editor;
                    
                    cm.focus();
                    CodeMirror.commands.goDocEnd(cm);
                }
            },

            Right(cm) {
                cm.moveH(1, "char");
            },

            Down(cm) {
                var cursor = cm.getCursor();
                if (cursor.line + 1 < cm.lineCount())
                    return cm.moveV(1, "line");

                cm = self.nextSibling.editor;
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

            Up(cm) {
                var cursor = cm.getCursor();
                if (cursor.line > 0)
                    return cm.moveV(-1, "line");
                
        		cm = self.previousSibling.editor;
        		cm.focus();
        		
       			cm = cm.editor;	
    	        
    	        if (cursor.ch == 0) {
    	            var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
    	            for (let i = 0; i < linesToMove; ++i) {
    	                cm.moveV(1, "line");
    	            }
    	        } else
    	            cm.setCursor(cm.lineCount() - 1, cursor.ch);
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
                    for (let i = 0; i < linesToMove; ++i) {
                        cm.moveV(1, "line");
                    }
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

            F5(cm) {
                self.debug();
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
        };
        
        if (typeof CodeMirror == 'undefined')
        	return;
        
        this.editor = CodeMirror.fromTextArea(this.$el, {
            mode: {
                name: "python",
                singleLineStringErrors: false
            },
            
            theme: this.theme,

            indentUnit: 4,

            matchBrackets: true,

            scrollbarStyle: null,

            extraKeys,
            
            lineNumbers: this.lineNumbers,
            
            styleActiveLine: this.styleActiveLine,

            hintOptions: { 
                hint(cm, options){                    
                	var Pos = CodeMirror.Pos;
                	return new Promise(function(accept) {
                		var cur = cm.getCursor();
                		var token = cm.getTokenAt(cur);
                		var tokenString = token.string;
                		console.log('tokenString = ' + tokenString);

                		var text = cm.getLine(cur.line);
                		text = text.slice(0, cur.ch);
                		var prefix = text.match(/[\w.]+$/)[0];

                		var sympy = axiom_user();
                		var url = `/${sympy}/php/request/`;

                		var kwargs;
                		if (tokenString == '.' || prefix.startsWith('.')) {
                			token.start += 1;

                			switch (prefix) {
                				case 'Eq.':
                					return accept({
                						list: self.EqVariables(),
                						from: Pos(cur.line, token.start),
                						to: Pos(cur.line, token.end)
                					});
                				case '.':
                					if (text.match(/\bEq\[-?\d+\]\.$/)) {
                						var list = ['this', 'subs', 'variable', 'reversed', 'lhs', 'rhs'];
                						return accept({
                							list: list,
                							from: Pos(cur.line, token.start),
                							to: Pos(cur.line, token.end)
                						});
                					}
                					else if (text.match(/\w+\.args\[-?\d+\]\.$/) || text.match(/\.find\(.+\)\.$/)) {
                						return accept({
                							list: this_phrases(),
                							from: Pos(cur.line, token.start),
                							to: Pos(cur.line, token.end)
                						});
                					}
                				case ".this.":
                					//if (text.match(/\bEq\[-?\d+\]\.this\.$/)) {}
               						return accept({
               							list: this_phrases(),
               							from: Pos(cur.line, token.start),
               							to: Pos(cur.line, token.end)
               						});

                				default:
                					var m = prefix.match(/^\.([\w.]*\.)(\w*)$/);
                					if (m) {
                						var phrase, _;
                						[_, prefix, phrase] = m;
                						switch (prefix) {
                							case "this.":
                								var list = [];
                								for (let word of this_phrases()) {
                									if (word.startsWith(phrase)) {
                										list.push(word);
                									}
                								}
                								token.start -= 1;
                								return accept({
                									list: list,
                									from: Pos(cur.line, token.start),
                									to: Pos(cur.line, token.end)
                								});
                							default:
                								if (!phrase) {
                									var list = prefix.split('.');
                									if (list[list.length - 2] == 'apply') {
                										break;
                									}
                									
                									return accept({
                										list: this_phrases(),
                										from: Pos(cur.line, token.start),
                										to: Pos(cur.line, token.end)
                									});
                								}
                								break;
                						}
                					}

                					break;
                			}

                			kwargs = { prefix: prefix, phrase: '' };
                			url += `suggest.php`;
                		}
                		else {
                			if (prefix.indexOf('.') >= 0) {
                				var m = prefix.match(/([\w.]*\.)(\w*)$/);
                				var phrase, _;
                				[_, prefix, phrase] = m;
                				kwargs = { prefix: prefix, phrase: phrase };
                				m = prefix.match(/^(\w*)\.$/);
                				if (m) {
                					if (sections.includes(m[1]))
										url += `suggest.php`;
									else if (m[1] == 'Eq') {
										return accept({
											list: self.EqVariables(phrase),
											from: Pos(cur.line, token.start),
											to: Pos(cur.line, token.end)
										});
									}
									else {
										kwargs = { prefix: phrase };
										url += `hint.php`;
                					}
                				}
                				else
                					url += `suggest.php`;
                			}
                			else {
                				kwargs = { prefix: prefix };
                				url += `hint.php`;
                			}
                		}

                		form_post(url, kwargs).then(list => {

                			// Find the token at the cursor
                			console.log('list = ' + list);
                			return accept({
                				list: list,
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
    //overflow-y: visible;
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

.breakpoint:before{
	width: 4px;
	height: 1.5px;
	position: absolute;
	left: 0px;
	top: 11.5px;
	content: "";
	transform: rotate(-45deg);
	background: #00FF00;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}
    
.breakpoint:after {
	width: 6px;
	height: 6px;
	position: absolute;
	left: 2.3px;
	top: 6px;
	content: "";
	background: #00FF00;
	border-radius: 50%;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}

.executionPoint > pre > span {
	background-color: #5a5;
}

</style>