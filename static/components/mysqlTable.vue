<template>
	<div tabindex=2>
		<mysql :host=host :user=user :token=token :sql=sql :kwargs=kwargs :rowcount=data.length ref=mysql v-mysql></mysql>
		<form tabindex=1 name=form :action=action method=post class=monospace-form @keydown=keydown>
			<template v-for="(data, index) of data">
				<div v-if="show[index] != false">
					<div v-if=api_url class=float :index=index v-torch>
						<template v-if="correct[index] == null"></template>
						<font v-else-if=correct[index] color=green>√</font>
						<table v-else class=report border=1>
							<tr>
								<th>\</th><th>precision</th><th>recall</th>
							</tr>
							<tr>
								<td align=middle :class=correct[index]>{{api_output}}</td>
								<fraction :numerator=true_positive[index] :denominator=sum_predicted[index] :operator="'='"></fraction>
								<fraction :numerator=true_positive[index] :denominator=sum_labelling[index] :operator="'='"></fraction>
							</tr>
						</table>
					</div>
					<table border=1 class=dictionary :index=index>
						<template v-for="{Field, Type, value} of detailed_values(data)" :class=Field>
							<input v-if="Field == 'training'" type=hidden :name="`${Field}[]`" :value=value />
							<template v-else-if="value && value.isArray">
								<template v-if=value.length>
									<tr>
										<td :rowspan=value.length>{{Field}}</td>
										<td>
											<mysqlObject :name="`${Field}[${index}][0]`" :value=value[0]></mysqlObject>
										</td>
									</tr>
									<tr v-for="i of value.length - 1">
										<td>
											<mysqlObject :name="`${Field}[${index}][${i}]`" :value=value[i]></mysqlObject>
										</td>
									</tr>
								</template>
								<tr v-else>
									<td>{{Field}}</td>
									<td></td>
								</tr>
							</template>
							<tr v-else>
								<td>{{Field}}</td>
								<td>
									<select v-if=dtype[Field].isArray :name="`${Field}[]`" :value=value @change="change($event, index)">
										<option v-for="value of dtype[Field]" :value=value>{{value}}</option>
									</select>
									<span v-else-if=is_primary_key[Field]>
										<a :href=primary_key_url(value) :target=PRI>{{value}}</a>
										<input type=hidden :name="`${Field}[]`" :value=value />
									</span>
									<mysqlObject v-else :name="`${Field}[]`" :value=value></mysqlObject>
								</td>
							</tr>
						</template>
					</table>
					<p v-for="feedback, i of data.__feedback" v-html=feedback :title=data.__prompt[i] @dblclick=dblclick_p></p>
				</div>
			</template>
			<input type=hidden name=table :value=table>
		</form>
		
		<div v-if=report.sum v-focus tabindex=4>
			<div style="float:right">
				number of testing cases: {{data.length}}<br>
				there {{report.err <= 1? 'is' : 'are'}} {{report.err}} {{report.err <= 1? 'error' : 'errors'}} in all, <button class=transparent @click=click_simplify>{{report.simplify? 'show all tables': 'show errors only'}}</button>
				{{report.simplify? 'to inspect in detail.': 'to simplify the report.'}}<br>
				remaining: {{data.length - report.sum}} to be evaluated...<br>
				remaining list:<br>
				<template v-if="data.length - report.sum < 10" v-for="id of remainingList">id = {{id}}<br></template>
			</div>
			<table class="report" border=1>
				<tr>
					<th colspan=2>testing synopsis</th>
				</tr>
				<tr>
					<th>\</th><th>accuracy</th>
				</tr>
				<tr>
					<td align=middle><font color=green>{{api_output}}</font></td>					
					<fraction :numerator="report.sum - report.err" :denominator="report.sum" :operator="'='"></fraction>
				</tr>
				<template v-for="type of dtype[api_output]">
					<tr v-if="report.sums[type]">
						<td>{{type}}</td>
						<fraction :numerator="report.sums[type] - report.errs[type]" :denominator="report.sums[type]" :operator="'='"></fraction>
					</tr>
				</template>
			</table>
		</div>
		<timer v-if=trigger :cond="!data.length || data.length - report.sum" :trigger=trigger style="float:right"></timer>
	</div>
</template>

<script>
console.log('import mysqlTable.vue');
import {props, piece_together} from "../js/mysql.js"
import {head_line_offset, last_line_offset} from "../js/textarea.js"

import {modify_training} from "../js/Command.js"
import fraction from "./fraction.vue"
import timer from "./timer.vue"
import mysql from "./mysql.vue"
import mysqlObject from "./mysqlObject.vue"

export default {
    components: {mysql, fraction, timer, mysqlObject},

	props,
	
    data() {
        return {
        	mounted: {},
        	_column_size: {},
        	dictionary: true,

        	correct: [],
        	show: [],
        	true_positive: [],
        	sum_predicted: [],
			sum_labelling: [],
			
        	report: {
           		sum: 0,
           		err: 0,
           		sums: {},
           		errs: {},
        	},
        	
        	label_prompted: null,
        };
    },
    
    computed: {
    	trigger() {
    		return this.is_torch? this.trigger_simplify: this.repeat? this.trigger_save: null;
    	},
    	
    	repeat() {
    		var {kwargs} = this;
    		return kwargs.kwargs && kwargs.kwargs.repeat;
    	},

    	action() {
    		var {action_insert} = this.mysql;
    		var url = [];
    		if (this.repeat)
    			url.push('kwargs[repeat]=true');
    		
    		var {kwargs} = this;
    		if (kwargs.kwargs) {
        		var {model} = kwargs.kwargs;
        		if (model)
        			url.push('kwargs[model]=' + model);
    		}

    		var {limit} = kwargs;
    		if (limit != null)
    			url.push('limit=' + limit);

    		if (kwargs.where) {
    			kwargs = {...kwargs};
    			kwargs.select = '*';
    			if (kwargs.into) {
        			kwargs.from = kwargs.into;
        			delete kwargs.into;
        			delete kwargs.set;
    			}
    			url.push(...piece_together(kwargs).slice(1));
    		}
    		return action_insert + '&' + url.join('&');
    	},
    	
    	is_primary_key() {
    		var is_primary_key = {};
    		var {Comment} = this;
    		for (var {Field, Key} of this.desc) {
    			if (Key == 'PRI')
    				is_primary_key[Field] = true;
    			else {
    				var comment = Comment[Field];
   					if (comment && comment.PRI)
       					is_primary_key[Field] = true;
    			}
    		}
    		return is_primary_key;
    	},
    	
    	database() {
    		return this.mysql.database;
    	},
    	
    	PRI() {
    		return this.mysql.PRI;
    	},
    	
    	mysql() {
    		return this.mounted.mysql? this.$refs.mysql: {};
    	},
    	
    	desc(){
    		var desc = this.mysql.desc;
    		if (desc)
    			return desc;
    		return [];
    	},
    	
    	api(){
    		var api = this.mysql.api;
    		if (api)
    			return api;
    		return {};
    	},
    	
    	Comment(){
    		var Comment = this.mysql.Comment;
    		if (Comment)
    			return Comment;
    		return {};
    	},
    	
    	api_parameters() {
    		var api = this.api;
    		for (var Field in api) {
    			var {url : api_url, inputs: api_inputs} = api[Field];
    			return {api_inputs, api_url, api_output: Field};
    		}

    		return {};
    	},
    	
    	api_url() {
    		return this.api_parameters.api_url;
    	},
    	
    	api_inputs() {
    		return this.api_parameters.api_inputs;
    	},
    	
    	api_output() {
    		return this.api_parameters.api_output;
    	},
    	
    	dtype(){
    		var dtype = this.mysql.dtype;
    		if (dtype)
    			return dtype;
    		return {};
    	},
    	
		is_torch(){
			return getParameterByName('torch') || this.kwargs.kwargs && this.kwargs.kwargs.torch;
		},
		
		is_mysql(){
			return getParameterByName('mysql') || getParameterByName('cmd') == 'select' || this.cmd == 'update';
		},

		compare(){
			if (this.is_torch)
				return 'torch';
		},
    },
    
    created() {
    	for (var json of this.data){
    		if (json.training == null){
    			json.training = 0;
    		}
    	}    	
    },
    
    methods: {
		dblclick_p() {
			if (this.repeat) {
				delete this.trigger;
				delete this.trigger_save;
				delete this.kwargs.kwargs.repeat;
			}
		},

    	detailed_values(value) {
    		var values = [];
    		for (var {Field, Type} of this.desc) {
    			values.push({Field, Type, value: value[Field]});
    		}
    		return values;
    	},
    	
    	async prompting(model, text, lang, labels) {
    		console.log('text = ', text);
    		console.log('model = ', model);
    		for (var i of range(10)) {
    			try {
    				var {bool, prompt, reply, label, error_code} = await json_post('http://localhost:5000/prompt/classify', {model, text, lang, label: labels});
    				if (error_code)
    					return {bool: false, prompt: '', reply, label: null, error_code};
    				if (prompt && reply)
    					return {bool, prompt, reply, label};
    				console.log('prompt or reply is empty, trying again!');
    			}
    			catch(err) {
    				console.log(err);
    			}
    			await sleep(3 + i);
    		}
    		
    		return {bool: null, prompt: '', reply: 'Erroneous result from prompting API!', label: null};
    	},
    	
    	primary_key_url(primary_key) {
    		var {host, user, database, table, PRI} = this;
    		var kwargs = {user, from: fromEntries(database, table)};
			if (primary_key)
    			kwargs[PRI] = primary_key.encodeURI();
    		if (host && host != 'localhost')
				kwargs.host = host;
    		return 'query.php?' + get_url(kwargs);
    	},
    	
    	column_size(name){
    		var column_size = this._column_size[name];
    		if (column_size == null) {
    			column_size = Math.max(...this.data.map(tr => {
    				if (tr[name] && tr[name].isString)
    					return strlen(tr[name]);
    				
    				switch (this.dtype[name]) {
    				case 'int':
    					return 4;
    				case 'float':
    					return 5;
    				default:
    					return 10;
    				}
    			}));
    			
    			this._column_size[name] = column_size;
    		}
    		
    		return column_size;
    	},
    	
    	coordinate(self){
    		var td = self.parentElement;
    		if (td.tagName == 'TD'){
    			var tr = td.parentElement;
    			var col = tr.children.indexOf(td);
    			var table = tr.parentElement;
    			var row = table.children.indexOf(tr);
    			return [row, col, table.children.length];
    		}
    		return [-1, -1];
    	},
    	
    	focus(row, col, offset, table){
    		table ||= this.$refs.table;
    		var tr = table.children[row];
    		var td = tr.children[col];
    		var input = td.firstElementChild;
    		input.focus();
    		if (input.tagName == 'INPUT' || input.tagName == 'TEXTAREA'){
    			if (offset < 0){
    				offset.value.length;
    			}
    			
    			input.selectionStart = offset;
    			input.selectionEnd = offset;
    		}
    	},
    	
    	keydown(event){
			var self = event.target;
			var key = event.key;
			switch (key){
			case 'S':
			case 's':
				if (!event.ctrlKey)
					break;
				event.preventDefault();
				
				document.mysql.querySelector('input[type=text]').focus();
				this.$nextTick(()=>{
					form.submit();
				});
			
				break;
				
			case 'Z':
			case 'z':
				if (!event.ctrlKey)
					break;
				
				this.undoer.undo();
				break;
				
			case 'ArrowUp':
				if (self.tagName == 'TEXTAREA') {
					var selectionStart = head_line_offset(self);
					if (selectionStart == null) {
						break;
					}
					var table = self.parentElement.parentElement.parentElement;
				}
				else {
					var {selectionStart} = self;
					var table = null;
				}
				
				event.preventDefault();
				var self = event.target;
				var [row, col] = this.coordinate(self);
				if (row > 0){
					--row;
					this.focus(row, col, selectionStart, table);
				}
				
				break;
			case 'ArrowDown':
				var self = event.target;
				if (self.tagName == 'TEXTAREA') {
					var selectionStart = last_line_offset(self);
					if (!selectionStart) {
						break;
					}
					var table = self.parentElement.parentElement.parentElement;
				}
				else {
					var {selectionStart} = self;
					var table = null;
				}
				
				event.preventDefault();
				var [row, col, rows] = this.coordinate(self);
				if (row + 1 < rows){
					++row;
					this.focus(row, col, selectionStart, table);
				}
				
				break;
			case 'ArrowLeft':
				
				var self = event.target;
				if (self.tagName == 'SELECT' || !self.selectionStart){
					event.preventDefault();
					var [row, col] = this.coordinate(self);
					if (col > 0){
						--col;
					}
					else{
						--row;
						col = self.parentElement.parentElement.children.length - 2;
					}
					this.focus(row, col, -1);
				}
				
				break;
			case 'ArrowRight':
				
				var self = event.target;
				if (self.tagName == 'SELECT' || self.selectionStart == self.value.length){
					event.preventDefault();
					var [row, col] = this.coordinate(self);
					if (col + 1 < self.parentElement.parentElement.children.length - 1){
						++col;
					}
					else{
						row++;
						col = 0;
					}
					this.focus(row, col, 0);
				}
				
				break;
			case 'PageDown':
				if (this.mysql.cmd == 'insert')
					this.forward_next();
				break;
			}
    	},
    	
		forward_next() {
			var {kwargs, user, host, database, table} = this;
			console.log(kwargs);

			kwargs.select = '*';
			var limit = getParameterByName('limit');
			if (limit == null)
				limit = 1;

			kwargs.limit = limit;
			kwargs.from = fromEntries(database, table);

			var url = [];
			url.push(`user=${user}`);
			if (host && host != 'localhost')
				url.push(`host=${host}`);

			url.push(...piece_together(kwargs));

			var {repeat, model} = kwargs.kwargs?? {};
			kwargs = {};
			if (model)
				kwargs.model = model;
			if (repeat)
				kwargs.repeat = repeat;
			
			location.search = '?' + get_url({kwargs}) + '&' + url.join('&');
		},
    	
        async process(name, data) {
    		var [name, ext] = split_filename(name);
    		var array = [];
    		switch (ext) {
    		case 'json':
    			if (data.isString)
                	array = JSON.parse(data);
    			else
    				array = data;
                if (!Array.isArray(array)){
                	array = [array];
                }
                break;

    		case 'txt':
    		case 'csv':
            	for (var line of data.split('\n')){
            		var obj = {};
            		for (var [{Field, Type}, value] of zip(this.desc, line.split('\t'))) {
            			obj[Field] = value;
            		}
            		array.push(obj);
            	}
            	break;
                
			case 'xlsx':
				var workbook = XLSX.read(data, {type: 'array'});
		        for (var sheet in workbook.Sheets) {
		            if (workbook.Sheets.hasOwnProperty(sheet)) {
		                for (var data of XLSX.utils.sheet_to_json(workbook.Sheets[sheet])) {
		                	for (var key in this.dtype) {
		                		if (data[key] == null) {
		                			var dtype = this.dtype[key];
		                			switch (dtype) {
		                			case 'float':
		                				data[key] = 0;
		                				break;
		                			case 'string':
		                				data[key] = '';
		                				break;
		                			case 'int':
		                				if (key == this.PRI) {

		                				}
		                				else if (key == 'training') {
		                					data[key] = ~1;
		                				}
		                				else {
		                					data[key] = 0;
		                				}
		                				break;
		                			default:
		                				if (dtype.isArray) {
		                					data[key] = dtype[0];
		                				}
		                				else {
		                					data[key] = '';
		                				}
		                				break;
		                			}
		                		}
		                	}
		                	array.push(data);
		                }
		            }
		        }
				break;
            }

    		this.insert(array);
        },
        
    	async insert(data) {
        	var database = this.database;
        	var table = this.table;
			var training = getParameterByName("training");
			if (training)
				training = ~training;
			else
				training = ~0;

			for (var obj of data) {
				if (obj.training == null)
					obj.training = training;
				else if (obj.training >= 0) {
					obj.training = ~obj.training;
				}
			}
			
			var {PRI} = this;
			if (this.dtype[PRI] == 'int') {
	        	var [ret] = await query(this.host, this.user, this.token, `select max(${PRI}) as id from ${database}.${table}`);
	        	var primary_key = ret[PRI];
	        	var primary_key = primary_key == null? 0: parseInt(primary_key);
	        	for (var obj of this.data) {
	        		if (obj[PRI] > primary_key)
	        			primary_key = obj[PRI];
	        	}

				for (var obj of data) {
					if (!obj[PRI])
						obj[PRI] = ++primary_key;
				}
			}

			this.data.push(...data);
    	},

        change(event, index){
        	var self = event.target;
        	var name = self.name.slice(0, -2);
        	if (self.value != this.data[index][name]){
        		this.data[index][name] = self.value;
        		var {training} = this.data[index];
        		this.data[index].training = modify_training(training, name != this.table);

        		console.assert(this.data[index].training < 0, "this.data[index].training < 0");
        	}
        },

        set_training(object) {
        	var el = object.$el;
        	var {name} = el;
        	if (name) {
        		if (name.fullmatch(/\w+\[\]/))
        			name = name.slice(0, -2);
        	}
        	var td = el.parentElement;
        	var tr = td.parentElement;
        	var table = tr.parentElement;
        	var index = table.getAttribute('index');
        	var {training} = this.data[index];
        	this.data[index].training = modify_training(training, name != this.table);
        },

    	trigger_save(event) {
    		form.submit();
    	},

    	trigger_simplify() {
    		if (this.report.simplify) {
    			this.report.simplify = false;
    			this.click_simplify();
    		}
    	},
    	
		click_simplify(event) {
    		var {show} = this;
			if (this.report.simplify){
				for (var index of range(this.data.length)){
					show[index] = true;
				}
				this.report.simplify = false;
			}
			else{
				var {correct} = this;
				for (var index of range(this.data.length)){
					show[index] = !correct[index];
				}
				this.report.simplify = true;
			}
		},
    },
    
    async mounted(){
    	++this.mounted.mysql;
		if (this.repeat && this.mysql.cmd == 'insert')
			this.forward_next();

		this.report.simplify = this.$refs.mysql.simplify;
    },
    
    unmounted(){
    	--this.mounted.mysql;
    },
    
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	el.focus();
		    },
		},
		
		mysql: {
		    // after dom is inserted into the document
		    async mounted(el, binding) {
		    	var {instance: self} = binding;
		    	var comment = await self.$refs.mysql.table_comment();
		    	if (comment) {
		    		var {prompt} = JSON.parse(comment);
		    		if (prompt) {
		    			self.label_prompted = prompt;
		    			console.log(prompt);
		    		}
		    	}
		    },
		},
		
		torch: {
		    // after dom is inserted into the document
		    async mounted(el, binding) {
		    	var {instance: self} = binding;
				if (self.mysql.cmd == 'insert')
					return;
		    	
	    		var {api_url, api_inputs} = self;
	    		//console.log({api_url, api_inputs});
	    		var index = el.getAttribute('index');
	    		var data = self.data[index];
	    		var inputs = {};
	    		for (var field of api_inputs) {
	    			inputs[field] = data[field];
	    		}

		    	if (self.is_torch) {
		    		var {api_url} = self;
		    		if (api_url.constructor == Object)
		    			api_url = api_url[data.lang];

		    		if (api_url.isArray)
		    			api_url = api_url[randrange(0, api_url.length)];

		    		var new_label = await json_post(api_url, inputs);
		    		var old_label = data[self.api_output];
		    		var judge = new_label == old_label;
	    			self.correct[index] = judge;
	    			
	    			self.sum_predicted[index] = 1;
	    			self.sum_labelling[index] = 1;
	    			++self.report.sum;
	    			if (old_label in self.report.sums)
	    				++self.report.sums[old_label];
	    			else {
	    				self.report.sums[old_label] = 1;
	    				if (self.report.errs[old_label] == null)
	    					self.report.errs[old_label] = 0;
	    			}

	    			if (judge) {
	    				self.true_positive[index] = 1;
	    				return;
	    			}

	   				self.true_positive[index] = 0;

	   				++self.report.err;
	    			if (old_label in self.report.errs)
	    				++self.report.errs[old_label];
	    			else
	    				self.report.errs[old_label] = 1;
	   				data[self.api_output] = new_label;

	    			var {label_prompted} = self;
	    			if (!label_prompted) {
	    				return;
	    			}

	    			label_prompted = label_prompted[data.lang];
	    			var model = getParameterByName('kwargs[model]');
	    			if (!model)
	    				return;

					var feedback = [];
					var prompts = [];

					data.__feedback = feedback;
					data.__prompt = prompts;

					delete inputs.lang;
					var lang = data.lang;
					var text = Object.values(inputs).join('\n');
					text = text.slice(0, 2330);

					feedback.push(`the labelled tag is ${old_label}; `);
					prompts.push('');

					var label = label_prompted[new_label];
	    			if (label) {
	   					var {bool, prompt, reply} = await self.prompting(model, text, lang, label);
	    				feedback.push(reply);
	    				prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);

	    				label = label_prompted[old_label];
	    				if (bool) {
	    					feedback[0] += `it is related to <font color=blue>${new_label}</font>; `;
	    					data.training = ~data.training;
	    					if (!label)
	    						return;

	   						var {bool, prompt, reply} = await self.prompting(model, text, lang, label);
	    					feedback.push(reply);
	    					prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);
	    					if (bool || bool == null)
	    						data.training = ~data.training;
	    					
	        				if (bool)
	        					feedback[0] += `it is related to <font color=blue>${old_label}</font>; `;
	        			    else if (bool == false)
	        			    	feedback[0] += `it is <font color=red>not</font> related to ${old_label}; `;
	    				}
	    				else if (bool == false) {
	    					feedback[0] += `it is <font color=red>not</font> related to ${new_label}; `;
	    					
	    					if (!label)
	    						return;

	   						var {bool, prompt, reply} = await self.prompting(model, text, lang, label);
	    					feedback.push(reply);
	    					prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);

	        				if (bool)
	        					feedback[0] += `it is related to <font color=blue>${old_label}</font>; `;
	        			    else if (bool == false)
	        			    	feedback[0] += `it is <font color=red>not</font> related to ${old_label}; `;
	    					
	    					if (bool == false) {
	    						for (var label of self.dtype[self.api_output]) {
	    							if (label == old_label || label == new_label)
	    								continue;

	    							if (label_prompted[label]) {
	   		    						var {bool, prompt, reply} = await self.prompting(model, text, lang, label_prompted[label]);
	    		    					feedback.push(reply);
	    		    					prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);

	    		        				if (bool)
	    		        					feedback[0] += `it is related to <font color=blue>${label}</font>; `;
	    		        			    else if (bool == false)
	    		        			    	feedback[0] += `it is <font color=red>not</font> related to ${label}; `;
	    		    					
	    		    					if (bool) {
	    		    						data[self.api_output] = label;
	    		    						if (data.training >= 0)
	        									data.training = ~data.training;
	        								break;
	    		    					}
	    							}
	    							else {
	    								data[self.api_output] = label;
	    								data.training = ~data.training;
	    							}
	    						}
	    					}
	    				}
	    			}
	    			else {
	    				label = label_prompted[old_label];
	   					if (!label)
	   						return;

						var {bool, prompt, reply} = await self.prompting(model, text, lang, label);
	   					feedback.push(reply);
	   					prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);
	   					if (bool == false) {
	   						data.training = ~data.training;
	   						feedback[0] += `it is <font color=red>not</font> related to ${old_label}; `;
	   					}
	   					else if (bool)
	    					feedback[0] += `it is related to <font color=blue>${old_label}</font>; `;
	    			}
		    	}
		    	else {
	    			var {label_prompted} = self;
	    			if (!label_prompted)
	    				return;

	    			label_prompted = label_prompted[data.lang];
	    			var model = getParameterByName('kwargs[model]');
	    			if (!model)
	    				return;

					var feedback = [];
					var prompts = [];

					data.__feedback = feedback;
					data.__prompt = prompts;

					delete inputs.lang;
					var lang = data.lang;
					var text = Object.values(inputs).join('\n');
					text = text.slice(0, 2330);
					
					feedback.push(`the labelled tag is ${data[self.api_output]}; `);
					prompts.push('');
					
					var old_label = data[self.api_output];
					var label = label_prompted[old_label];
	    			if (label) {
	   					var {bool, prompt, reply, error_code} = await self.prompting(model, text, lang, label);
	    				feedback.push(reply);
	    				prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);

	    				if (bool) {
	    					feedback[0] += `it is related to <font color=blue>${old_label}</font>; `;
	    					data.training = ~1;
	    					self.true_positive[index] = 1;
	    				}
	    				else if (bool == false) {
	    					feedback[0] += `it is <font color=red>not</font> related to ${old_label}; `;
	    					data.training = ~0;
	    					self.true_positive[index] = 0;
	    				}
	    				else if (error_code) {
	    					data.training = ~0;
	    				}
	    			}
	    			else {
	   					var {label, prompt, reply, error_code} = await self.prompting(model, text, lang, label_prompted);
	    				feedback.push(reply);
	    				prompts.push(prompt.length > 1000? "..." + prompt.slice(-1000): prompt);

	    				var bool = prompt? label == null: null;
	    				if (bool) {
	    					feedback[0] += `it is labelled <font color=blue>${old_label}</font>; `;
	    					data.training = ~1;
	    					self.true_positive[index] = 1;
	    				}
	    				else if (bool == false) {
	    					feedback[0] += `it is labelled <font color=red>${label}</font>; `;
	    					data[self.api_output] = label;
	    					data.training = ~data.training;
	    					self.true_positive[index] = 0;
	    				}
	    				else if (error_code) {
	    					data.training = ~0;
	    				}
	    			}

    				if (bool != null) {
	    				self.correct[index] = bool;
		    			self.sum_predicted[index] = 1;
		    			self.sum_labelling[index] = 1;
    				}
    				await sleep(3);
    				if (!bool) {
    					++self.report.err;
    	    			if (old_label in self.report.errs)
    	    				++self.report.errs[old_label];
    	    			else
    	    				self.report.errs[old_label] = 1;
    				}

					++self.report.sum;
	    			if (old_label in self.report.sums)
	    				++self.report.sums[old_label];
	    			else {
	    				self.report.sums[old_label] = 1;
	    				if (self.report.errs[old_label] == null)
	    					self.report.errs[old_label] = 0;
	    			}
		    	}

		    	feedback[0] += `below is the brief reason: `;
		    },
		},
	},
}
</script>

<style scoped>
table {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	background: transparent;
}

th.training, tr.training, td.training {
	display: none;
}

input {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;
	background: transparent;
	border: none;
	border-style: none;
	padding: 0px 0px 0px 0px;
}

input:focus {
	outline: none;
	caret-color: rgb(127, 0, 85);
}

input.float, input.int {
	color: red;
}

select {
	color: blue;
}

textarea {
	resize: none;
	overflow: hidden;
	border: none;
}

textarea:focus {
	color: red;
	outline: none;
	caret-color: rgb(127, 0, 85);
}

table.dictionary {
	margin-bottom: 1em;
}

div.float {
	float: right;
	z-index: 10000;
	opacity: 1;
}

td.false {
	color: red;
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

button.transparent:hover{
	background-color: red;
}

</style>
