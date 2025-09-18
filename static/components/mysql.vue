<template>
	<div>
		<form action="" method=post style="float:right">
			<p class=logout>
				<input type=submit name=logout value=Logout id=logout>
				<input type=hidden name=token :value=token />
			</p>
		</form>
		<form name=mysql :action=action method=post>
			<component :is="'mysql' + cmd.capitalize()" :ref=cmd v-cmd :kwargs=kwargs @keydown=keydown></component>
			<input id=submit_query type=submit value=query />
			<mysqlExecute v-if=sql :cmd=cmd :sql=sql :database=database :table=table></mysqlExecute>
			<input v-for="func, Field in transform" :name="`transform[${Field}]`" type=hidden :value=func /> <br>
			<input type=hidden name=token :value=token />
		</form>
	</div>
</template>

<script>
console.log('import mysql.vue');
// grant select on *.* to test;
// grant show databases on *.* to 'test'@'%';
// grant create on test.* to 'test'@'%';
// grant all privileges on test.* to test;
// revoke select on *.* from root;
// grant select on `corpus`.* to `root`@`%` with grant option
// grant select on `mysql`.* to `root`@`%` with grant option
// grant select on `sys`.* to `root`@`%` with grant option
import mysqlSelect from "./mysqlSelect.vue"
import mysqlInsert from "./mysqlInsert.vue"
import mysqlDelete from "./mysqlDelete.vue"
import mysqlUpdate from "./mysqlUpdate.vue"
import mysqlAlter from "./mysqlAlter.vue"
import mysqlShow from "./mysqlShow.vue"
import mysqlSet from "./mysqlSet.vue"
import mysqlUnion from "./mysqlUnion.vue"
import mysqlExecute from "./mysqlExecute.vue"

import mysqlExpr from "./mysqlExpr.vue"
import mysqlGroup from "./mysqlGroup.vue"
import mysqlOrder from "./mysqlOrder.vue"
import mysqlArgs from "./mysqlArgs.vue"
import {piece_together} from "../js/mysql.js"
for (var component of [mysqlArgs, mysqlOrder, mysqlGroup])
	component.components.mysqlExpr = mysqlExpr;

import {get_db_table, simplify_expression, show_full_columns, show_tables, is_numeric, is_enum, is_string, is_json, physic2logic, get_cmd, set_cmd} from "../js/mysql.js"
import { reset_training } from "../js/Command.js";

export default {
	components: {mysqlSelect, mysqlInsert, mysqlDelete, mysqlUpdate, mysqlExecute, mysqlAlter, mysqlShow, mysqlSet, mysqlUnion},

	props : ['host', 'user', 'token', 'kwargs', 'sql', 'rowcount', 'sample', 'focus'],

	data() {
		return {
			cmds: ['select', 'update', 'insert', 'delete', 'rename', 'revoke', 'grant', 'alter', 'show', 'drop', 'set'],
			databases: ['corpus', 'mysql'],
			tables: [],

			dtype: {},
			desc: [],
			style_entity: {},
			transform: {},
			api: {},
			Comment: {},

			json_extract: {},
			mounted: {},

			//functions that operate on numeric values;
			numeric_functions: ['sum', 'agv', 'max', 'min', 'ceiling', 'floor', 'round'],
			//functions that operate on textual values;
			textual_functions: ['substring', 'substring_index', 'regexp_substr', 'regexp_replace', 'replace', 'concat', 'group_concat', 'json_arrayagg', 'json_objectagg', 'json_quote', 'json_unquote', 'json_array', 'json_object', 'json_length', 'json_extract', 'json_valid', 'json_remove', 'json_set', 'json_type', 'json_search', 'cast', 'length', 'regexp_instr', 'char_length', 'regexp_like', 'not regexp_like', 'lower', 'upper', 'left', 'right', 'reverse', 'find_in_set'],
			//functions that operate on jsonobj values;
			jsonobj_functions: ['count', 'json_length', 'json_extract', 'json_keys', 'json_value', 'json_search', 'json_array_append', 'json_array_insert', 'json_array_replace', 'json_insert', 'json_remove', 'json_set', 'json_merge', 'json_replace', 'json_depth', 'json_merge', 'json_merge_patch', 'json_merge_preserve', 'json_type', 'json_search'],
			//operators that operate on numeric values;
			numeric_operators: ['+', '-', '*', '/', '%', '&', '^', '>>', '<<'],
			//operators that operate on jsonobj values;
			jsonobj_operators: ['->', '->>'],
			//relations that operate on numeric values;
			numeric_relations: ['=', '!=', '>', '<', '>=', '<='],
			//relations that operate on textual values;
			textual_relations: ['regexp', 'like', 'regexp binary', 'like binary', '=', 'not regexp', 'not like', 'not regexp binary', 'not like binary', '!=', 'in', 'not', 'not in'],
			//relations that operate on jsonobj values;
			jsonobj_relations: ['json_contains', 'json_contains_path', 'not json_contains', 'not json_contains_path', 'is', 'is not'],

			aggregate_functions: ['sum', 'agv', 'max', 'min', 'group_concat', 'json_arrayagg', 'json_objectagg'],
		};
	},

	computed: {
		descDict() {
			var desc = {};
			for (var description of this.desc) {
				var {Field} = description;
				desc[Field] = {dtype: this.dtype[Field], ...description};
			}
			return desc;
		},

		select() {
			return this.mounted.select? this.$refs.select : {};
		},

		update() {
			return this.mounted.update? this.$refs.update : {};
		},

		delete() {
			return this.mounted.delete? this.$refs.delete : {};
		},

		insert() {
			return this.mounted.insert? this.$refs.insert : {};
		},

		option() {
			var option = {
				fields: Object.keys(this.dtype),
				function: ['count', 'sum', 'agv', 'max', 'min', 'length', 'char_length', 'round', 'ceiling', 'floor', 'substring', 'substring_index', 'regexp_substr', 'regexp_replace', 'concat', 'group_concat', 'json_array_append', 'json_array_insert', 'json_arrayagg', 'json_remove', 'json_set', 'json_object', 'json_extract', 'json_length', 'json_valid', 'json_search', 'lower', 'upper', 'left', 'right', 'reverse'],
				operator: ['~', '+', '-', '*', '/', '%', '&', '^', '>>', '<<', '->', '->>'],
			};

			return ['*', 'distinct', option];
		},

		cmd: {
			get() {
				return get_cmd(this.kwargs);
			},

			set(cmd) {
				var {kwargs} = this;
				var old_cmd = this.cmd;
				set_cmd(kwargs, old_cmd, cmd);
				if (old_cmd == 'insert' && cmd.match(/select|update|delete/)) {
					if (kwargs.where == null)
						kwargs.where = {};
					this.initialize_kwargs();
				}
			},
		},

		cmdAttr() {
			switch (this.cmd) {
			case 'delete':
			case 'select':
				return 'from';

			case 'update':
				return 'update';

			case 'insert':
				return 'into';
			}
		},

		numeric_function_regexp() {
			return new RegExp(this.numeric_functions.join('|'));
		},

		jsonobj_function_regexp() {
			return new RegExp(this.jsonobj_functions.join('|'));
		},

		textual_function_regexp() {
			return new RegExp(this.textual_functions.join('|'));
		},

		aggregate_function_regexp() {
			return new RegExp(this.aggregate_functions.join('|'));
		},

		Fields() {
			return this.desc.map(obj => obj.Field);
		},

		numericFields() {
			var fields = [];
			for (var {Field, Type, Key} of this.desc) {
				if (is_numeric(Type))
					fields.push(Field);
			}

			return fields;
		},

		textualFields() {
			var fields = [];
			for (var {Field, Type, Key} of this.desc) {
				if (!is_numeric(Type))
					fields.push(Field);
			}

			return fields;
		},

		db_table() {
			var value = this.kwargs[this.cmdAttr];
			if (value)
				return get_db_table(value);
		},

		database: {
			get() {
				var {db_table} = this;
				if (db_table)
					return db_table.database;
			},

			set(database) {
				if (database) {
					var attr = this.cmdAttr;
					this.kwargs[attr] = fromEntries(database, this.table);
				}
			}
		},

		table: {
			get() {
				var {db_table} = this;
				if (db_table)
					return db_table.table;
			},

			set(table) {
				var attr = this.cmdAttr;
				var value = this.kwargs[attr];
				if (value.isString){
					this.kwargs[attr] = table;
				}
				else {
					this.kwargs[attr] = fromEntries(this.database, table);
				}
			}
		},

		action() {
			var {host, sample} = this;
			var kwargs = {};

			if (host && host != 'localhost')
				kwargs.host = host;

			if (sample)
				kwargs.sample = sample;

			return 'query.php?' + get_url(kwargs);
		},

		action_insert() {
			var {database, table, host} = this;
    		var kwargs = {into: fromEntries(database, table)};
			if (host && host != 'localhost')
				kwargs.host = host;

			var url_kwargs = get_url(kwargs);
    		var url = [];
    		var {kwargs} = this;

    		if (kwargs.where) {
    			kwargs = {...kwargs};
    			kwargs.select = '*';
    			if (kwargs.update) {
        			kwargs.from = kwargs.update;
        			delete kwargs.update;
        			delete kwargs.set;
    			}
				else if (kwargs.into) {
					kwargs.from = kwargs.into;
        			delete kwargs.into;
				}
				kwargs = piece_together(kwargs);
				kwargs = kwargs.filter(s => s != `from[${database}]=${table}`);
    			url.push(...kwargs);
    		}
			else {
				var {limit} = kwargs;
				if (limit != null)
    				url.push('limit=' + limit);
			}
			url.push(url_kwargs);
			return 'query.php?' + url.join('&');
		},

		style_select_table() {
			return this.style_select(this.table, 'green');
		},

		PRI() {
			for (var {Field, Key} of this.desc) {
				if (Key == 'PRI')
					return Field;
			}

			return '';
		},

		instanceName() {
			var self = this.$root.$refs[this.table.hump];
			for (var k in self._.components) {
				if (k == 'mysql')
					continue;

				if (self[k] && self[k].isArray)
					return k;
			}
		},

    	simplify() {
			var kwargs = this.kwargs.kwargs?? {};
			return kwargs.simplify;
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
	},

	methods: {
    	primary_key_url(primary_key) {
    		var {host, database, table, PRI} = this;
    		var kwargs = {from: fromEntries(database, table)};
			if (primary_key)
    			kwargs[PRI] = primary_key.encodeURI();
    		if (host && host != 'localhost')
				kwargs.host = host;
    		return 'query.php?' + get_url(kwargs);
    	},

		toggle_server() {
			var hostname = location.hostname == 'localhost'? '192.168.18.131': 'localhost';
			var port = location.hostname == 'localhost'? '8000': '80';
			var {pathname, search, hash, protocol} = location;
			location.href = `${protocol}\/\/${hostname}:${port}${pathname}${search}${hash}`;
		},

		href(PRI, source, kwargs, value, table) {
			value ||= true;
			var {host, database} = this;
			table ||= this.table;

			Object.assign(kwargs, {from: fromEntries(database, table)})
			if (host && host != 'localhost')
				kwargs.host = host;

			if (source)
				kwargs.kwargs = fromEntries(source, value);
			if (PRI)
				kwargs[this.PRI? this.PRI: 'id'] = PRI;

			var href = 'query.php?' + get_url(kwargs);
			switch (source) {
			case 'json':
				break;
			default:
				href += location.hash;
			}

			return href;
		},

		async delete_instance(self, physic) {
			var {host, token, database, table, PRI} = this;
			var ret = 0;
			var $PRI = self.$parent[PRI];
			console.log("$PRI = ", $PRI);
			switch (self.source) {
			case 'mysql':
				var sql = `delete from ${database}.${table} where ${PRI} = '${$PRI}'`;
				console.log(sql);
				ret = await query(host, token, sql);
				break;
			default:
				alert(`could not delete the table for source = ${self.source}`);
			}

			console.log("rowcount =", ret);
			if (ret){
				var self = self.$parent;
				var {index} = self;
				if (physic) {
					// delete physically
					self.$parent.data.delete(index);
				}
				else {
					// delete logically
					self.show = false;
					var {training} = self.$parent.data[index];
					self.$parent.data[index].training = reset_training(training);
				}
			}
		},

		async navigate(delta, PRI, training, lang, kwargs) {
			if (training < 0) {
				if (!confirm("there is unsaved changes in the current page, abandon modification?"))
					return;

				training = ~training;
				training &= ~64;
			}

			var {offset} = this.kwargs;
			if ('lang' in this.dtype && !lang)
	    		var [{lang}] = await query(this.host, this.token, `select lang from ${database}.${table} where ${this.PRI} = ${PRI}`);

			var {host, database, table} = this;
			if (offset == '' || offset == null) {
				PRI = PRI.mysqlStr();
				var and = [];
				if (!lang)
					and.push(`lang = '${lang}'`);
				and.push(`training = ${training}`);
				var where = and.join(' and ');
				var sql = [`select JSON_ARRAYAGG(cast(${this.PRI} as char)) into @PRI from ${database}.${table} where ${where}`, `select regexp_substr(json_search(@PRI, 'one', ${PRI}), '\\\\d+') as offset`];
				var [rowcount, [{offset}]] = await query(host, this.token, sql);
			}

			offset = parseInt(offset) + delta;
			Object.assign(kwargs, {mysql: true, from: fromEntries(database, table)});
			if (host && host != 'localhost')
				kwargs.host = host;

			if (lang) {
				kwargs.lang = lang;
			}

			kwargs.training = training;
			kwargs.limit = 1;
			kwargs.offset = offset;
			location.href = 'query.php?' + get_url(kwargs);
		},

		preprocess_kwargs() {
			var {kwargs} = this;

			var criteria = {};
			for (var key in kwargs) {
				if (key.fullmatch(/where|select|from|into|with|having|order|group|on|using|limit|order|offset|update|transform|sample|execute|repeat|mysql|keras|torch|regex/))
					continue;

				criteria[key] = kwargs[key];
			}

			var cond = [];
			for (var key in criteria) {
				if (!this.descDict[key])
					continue;

				delete kwargs[key];
				var eq = [key, criteria[key]];
				if (['string', 'json'].includes(this.descDict[key].dtype) && !this.descDict[key].Key) {
					if (kwargs.where && kwargs.where.and && kwargs.where.and.some(c => c.regexp && c.regexp.equals(eq)));
					else
						cond.push({eq});
				}
				else {
					if (kwargs.where && kwargs.where.and && kwargs.where.and.some(c => c.eq && c.eq.equals(eq)));
					else
						cond.push({eq});
				}
			}

			if (!cond.length)
				return;

			if (kwargs.where) {
				if (kwargs.where.and) {
					kwargs.where.and.push(...cond);
					return;
				}

				if (len(kwargs.where)) {
					kwargs.where = {and: [kwargs.where, ...cond]};
					return;
				}
			}

			if (cond.length > 1){
				kwargs.where = {and: cond};
			}
			else {
				[cond] = cond;
				kwargs.where = cond;
			}
		},

		initialize_kwargs() {
			var {kwargs} = this;
			var {where} = kwargs;
			if (where && len(this.dtype)) {
				var where_dict = {};
				if (where) {
					where_dict = this.where_dict(where);
				}
				var {and} = where;
				if (!and) {
					and = [];
					var [func] = Object.keys(where);
					if (func) {
						and.push(fromEntries(func, where[func]));
						delete where[func];
					}

					where.and = and;
				}

				for (var key in where_dict) {
					if (!this.dtype[key]) {
						deleteIndices(and, (key => (and, i) => {
							var [[operator, [lhs, rhs]]] = Object.entries(and[i]);
							return lhs == key;
						})(key));
					}
				}

				for (var {Field, Type, Key} of this.desc) {
					if (!where_dict[Field]) {
						if (Key || is_numeric(Type) || is_enum(Type)) {
							and.push({eq: [Field, '']});
						}
						else if (is_string(Type)){
							and.push({regexp: [Field, '']});
						}
						else if (is_json(Type)){
							if (this.style_entity[Field]) {
								and.push({eq: [Field, '']});
							}
							else {
								and.push({regexp: [Field, '']});
							}
						}
					}
				}
			}

			var {order, limit, offset} = kwargs;
			if (order == null) {
				kwargs.order = '';
			}

			if (limit == null) {
				kwargs.limit = '';
			}

			if (offset == null) {
				kwargs.offset = '';
			}
		},

		is_leaf(value) {
			return value == null || value.isString || value.isNumber;
		},

		is_numeric_function(value) {
			return value && value.fullmatch(this.numeric_function_regexp);
		},

		is_jsonobj_function(value) {
			return value && value.fullmatch(this.jsonobj_function_regexp);
		},

		is_textual_function(value) {
			return value && value.fullmatch(this.textual_function_regexp);
		},

		is_aggregate_function(value) {
			return value && value.fullmatch(this.aggregate_function_regexp);
		},

		postprocess() {
			var parent = this.$parent;
			if (parent.postprocess)
				parent.postprocess(...arguments);
		},

		async table_comment() {
			var {table, database} = this;
			var sql = `select table_comment from information_schema.tables where table_name = '${table}' and table_schema = '${database}'`;
			try {
				var [{TABLE_COMMENT}] = await query(this.host, this.token, sql);
				return TABLE_COMMENT;
			}
			catch(err) {
				return;
			}
		},

		async show_full_columns(table){
			table ||= this.table;
			if (!table.startsWith('_')) {
				Object.assign(this.$data, await show_full_columns(this.database?? 'corpus', table, this.host, this.token));
			}

			this.preprocess_kwargs();
			this.initialize_kwargs();
		},

		async change_table(event){
			var table = event.target.value;
			if (this.table != table)
				this.table = table;

			var root = this.$root;
			if (root.data)
				root.data.clear();

			this.show_full_columns(table);
		},

		change_database(event){
			var database = event.target.value;
			if (this.database != database)
				this.database = database;

			var root = this.$root;
			if (root.data)
				root.data.clear();

			if (!database) {
				database = 'mysql';

				this.kwargs.from = {select: '*', from: [database, 'help_topic']};
				this.kwargs.where = {};
			}

			this.show_tables(database);
		},

		change_input(event){
			var self = event.target;
			var value = self.value;
			var length = value ? value.strlen() / 2 + 1.5: 15;
			length = Math.max(5, length);
			self.style = `width: ${length}em`;
		},

		style_input(Field){
			var text = this.kwargs[Field];
			var length = text == null ? 3 : text.strlen() / 2 + 2;
			length = Math.max(5, length);
			return `width: ${length}em`;
		},

		style_select(text, color, min){
			text ||= '_';
			min ||= 0.5;
			var {length} = text;
			switch (length) {
			case 1:
			case 2:
			case 3:
			case 4:
				length = Math.max(length * 0.54 + 0.15, min);
				break;
			case 5:
				length = length * 0.55 + 0.15;
				break;
			default:
				length = Math.max(length * 0.54 + 0.15, min);
				break;
			}

			var css = `width: ${length}em;`;
			if (color)
				css += `color: ${color}`;
			return css;
		},

		input_kwargs(event){
			var {name, value} = event.target;
			input_kwargs(this.kwargs, name, value);
			if (name == 'limit') {
				var {sql} = this;
				sql = sql.replace(/(?<= limit )\d*(?!.* limit \d*)/, value);
				if (sql != this.sql) {
					console.log("old sql = ", this.sql);
					console.log("new sql = ", sql);
					setAttribute(this, 'sql', sql);
				}
			}
		},

		async show_tables(database) {
			if (!database) {
				simplify_expression(this.kwargs);
				database = null;
			}

			var tables = await show_tables(database?? 'corpus', this.host, this.token);
			this.tables = tables;
			if (database && !tables.contains(this.table))
				this.table = tables[0];

			this.show_full_columns();
		},

		where_dict(cond, filterRhs) {
			var func = Object.keys(cond)[0];
			if (!func)
				return {};

			if (func == 'and') {
				var result = {};
				for (var cond of cond.and) {
					Object.assign(result, this.where_dict(cond, filterRhs));
				}
				return result;
			}
			if (cond[func].isArray) {
				var [lhs, rhs] = cond[func];
				if (filterRhs && !rhs || !lhs.isString)
					return {};
				return fromEntries(lhs, cond);
			}
			return {};
		},

		parse_expression(cond, Field2Type){
		    if (cond.isString || cond.isNumber)
		        return cond;

		    if (! cond)
		        return '';

		    var [func] = Object.keys(cond);
		    if (!func)
		    	return '';

		    if (cond[func].isArray)
		        var args = cond[func].map(cond => this.parse_expression(cond, Field2Type));
		    else
		        var args = [this.parse_expression(cond[func], Field2Type)];

		    func = physic2logic[func] ?? func;
			var transform = Field2Type.__transform__;
		    switch (func) {
		    case 'and':
		        args.sort((lhs, rhs) => {
		            var cmp = lhs.length - rhs.length;
		            if (cmp) {
		                return cmp;
		            }

		            if (lhs.match(/^regexp_like|^\w+ (binary )?regexp/) && lhs.match(/^regexp_like|^\w+ (binary )?regexp/)) {
		                // chech if looking behind exists?
		                if (lhs.match(/\(\?<=/)) {
		                    if (rhs.match(/\(\?<=/)) {
		                        return 0;
		                    }
		                    return 1;
		                } else {
		                    if (rhs.match(/\(\?<=/)) {
		                        return - 1;
		                    }
		                    return 0;
		                }
		            }

		            return cmp;
		        });

		    case 'or':
		        return args.filter(cond => cond).join(` ${func} `);

		    case '>':
		    case '<':
		    case '>=':
		    case '<=':
		    case '+':
		    case '-':
		    case '*':
		    case '/':
		    case '%':
		    case '&':
		    case '^':
		    case '>>':
		    case '<<':
		        if (args.any(cond => ! cond)) {
		            return '';
		        }

		        return args.join(` ${func} `);

		    case '=':
		    case '!=':
		    case 'regexp binary':
		    case 'like binary':
		    case 'not regexp':
		    case 'not like':
		    case 'not regexp binary':
		    case 'not like binary':
		    case 'regexp':
		    case 'like':
		    case 'as':
		        if (args.any(cond => ! cond)) {
		            return '';
		        }

		        if (Field2Type){
		            var [lhs, rhs] = args;
		            if (transform && transform[lhs]) {
		                var fn = `transform_${transform[lhs]}`;
		                rhs = eval(fn)(rhs)[0];
		                args[1] = rhs;
		            }

		            args = args.map(arg => Field2Type[arg]? arg: arg.mysqlStr(Field2Type[arg]));
		        }

		        return args.join(` ${func} `);
		    case '->':
		    case '->>':
		        if (args.any(cond => ! cond))
		            return '';

		        return args.join(func);

		    // case '~':
		    case 'distinct':
		        return `distinct ${args[0]}`;

		    case 'order':
		        if (args.length == 2) {
		            return `order by ${args[0]} ${args[1]}`;
		        }

		        return `order by ${args[0]}`;

		    case 'group_concat':
		        if (args[2]) {
		            args[2] = `separator ${args[2]}`;
		        }

		        args = args.join(' ');
		        return `${func}(${args})`;

		    case 'path':
		    case 'separator':
		    case 'distinct':
		        return `${func} ${args[0]}`;

			case 'find_in_set':
		        return `${func}(${args[0]}, ${args[1]})`;

		    case 'regexp_like':
		    case 'not regexp_like':
		        if (Field2Type){
		            var [lhs, rhs] = args;
		            if (transform && transform[lhs]) {
		                var fn = `transform_${transform[lhs]}`;
		                rhs = eval(fn)(rhs)[0];
		                args[1] = rhs;
		            }

		            args = args.map(arg => Field2Type[arg]? arg: arg.mysqlStr(Field2Type[arg]));
		        }

		    case 'json_object':
		        for (var i of range(0, args.length, 2)) {
	            	args[i] = args[i].mysqlStr();
	        	}

	        	args = args.join(', ');
	        	return `${func}(${args})`;
		    default:
		        args = args.map(cond => cond ? cond : (cond == 0? cond: "''"));
		        args = args.join(', ');
		        return `${func}(${args})`;
		    }
		},

		json_decode(data, Field) {
            for (var dict of data) {
                var value = dict[Field];
                if (value != null && value.isString) {
                	dict[Field] = JSON.parse(value);
                }
            }
		},

		json_decode_by_field_to_type(data) {
			var {dtype} = this;
		    for (var Field in dtype) {
		    	var Type = dtype[Field]
		        if (Type == 'json') {
		        	this.json_decode(data, Field);
		        }
		    }
		},

		keydown(event) {
			switch (event.key) {
			case 'Enter':
				var select = event.target;
				if (event.ctrlKey && select.tagName == 'SELECT') {
					event.preventDefault();
					document.mysql.submit();
				}
			}
		},

		toggle_training(self, update, value, index){
			if (value == null) {
				var {old_training: training} = self;
				if (training == null) {
					var {set} = self.kwargs;
					if (set) {
						if (index != null && index.isInteger && set[index] != null) {
							set = set[index];
							var {training} = set;
							if (training == null)
								return;
						}
						else
							return;
					}
					else
						return;
				}
				value = training;
			}

			if (update == null)
				update = true;

			var {training} = self;
			var old_training = training;
			var is_changed = !update;
			if (training < 0 || value != null){
				training = ~training;
				is_changed = true;
			}

			var text_is_changed = false;
			if (training & 64){
				training &= -65;
				text_is_changed = true;
			}

			training = value == null? (training == 1? 0: 1): value;
			if (training < 0)
				value = reset_training(training);
			else {
				value = training;
				if (text_is_changed)
					training |= 64;
				if (is_changed)
					training = ~training;
			}
			self.$parent.data[self.index].training = training;
			self.old_training = old_training;
			var {database, table, PRI} = this;
			var sql = `update ${database}.${table} set training = ${value} where id = '${self[PRI]}'`;
			console.log("sql =", sql);
			if (update && self[PRI]) {
				query(this.host, this.token, sql).then(rowcount => {
					console.log("rowcount =", rowcount);
				});
			}
		},
	},

	async created() {
		for (var [key, value] of Object.entries(this.kwargs)) {
			if (key.contains('.')) {
				delete this.kwargs[key];

				var kwargs = this.kwargs;
				var keys = key.split('.');
				var last_key = keys.pop();
				for (var key of keys) {
					if (kwargs[key] == null || kwargs[key].isString) {
						kwargs[key] = {};
					}
					kwargs = kwargs[key];
				}
				kwargs[last_key] = value;
			}
		}

		this.databases = (await query(this.host, this.token, 'show databases')).map(obj => obj.Database);
		//console.log(this.databases);
		var {database} = this;
		if (database)
			this.show_tables(database);
		//console.log(this.kwargs);
	},

	mounted() {
		var {mounted} = this.$parent;
		if (mounted)
			mounted.mysql = 1;

		var {body} = document;
		body.addEventListener("keydown", event => {
			switch (event.key) {
			case 'Home':
				if (!event.ctrlKey)
					break;

				var {activeElement, mysql} = document;
				if (mysql.contains(activeElement)) {
					mysql.querySelector('select.cmd').focus();
					return;
				}

				mysql.querySelector('input[type=text]').focus();
				break;

			case 'ArrowRight':
				var select = event.target;
				if (event.ctrlKey) {

				}
				else if (select.tagName == 'SELECT') {
					event.preventDefault();
					select.nextElementSibling.focus();
				}
				break;
			}
		});
	},

	unmounted() {
		var {mounted} = this.$parent;
		if (mounted && 'mysql' in mounted)
			mounted.mysql = 0;
	},

	directives: {
		cmd: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	var {className} = el;
		    	var {instance} = binding
		    	var {mounted} = instance;
		    	if (!mounted[className]) {
		    		mounted[className] = 0;
		    	}

		    	++mounted[className];
		    },

		    unmounted(el, binding) {
		    	var {className} = el;
		    	var {mounted} = binding.instance;
		    	--mounted[className];
		    },
		},
	},
}
</script>

<style>
body {
	background-color: rgb(199, 237, 204);
	margin-left: 1.5em;
}

select, button {
	-webkit-appearance: none;
	-moz-appearance: none;
	background-color: rgb(199, 237, 204);
	border: 0;
	font-size: 1em;
}

form, select, input, button {
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas, NSimsun, SimSun, "Courier New";
}

#submit_query {
	display: none;
}

.logout { margin-top: .5em; position: absolute; top: 25px; right: 10px; }

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

button.transparent:hover{
	background-color: red;
}

button.navigate {
	background-color: pink;
	border-style: none;
	outline: none;
}

button.navigate:hover{
	background-color: red;
}
</style>