<template>
	<div tabindex=2 @keydown.stop=keydown>

		<div v-if=self.edit>
			<textarea v-focus :rows=self.rows :cols=self.cols @input=input_textarea>{{sql}}</textarea>
		</div>
		<div v-else>
			<span class=hover>
				{{self.hint}}
			</span>
			<p v-click v-clipboard :class=cmd @dblclick.prevent=dblclick :style=self.style_p @mouseover=mouseover_p @mouseout=mouseout_p>
				{{sql.isArray? sql.join(';\n'): sql}}
			</p>
		</div>
		<template v-if=self.rowcount.length>
			rowcount = {{self.rowcount.back()}}<template v-if="self.rowcount.length > 1">, cumulative rowcount = {{self.rowcount.sum()}}</template>
		</template>
		<template v-else>
			{{self.mysql_result_hint}}
		</template>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
console.log('import mysqlExecute.vue');

const props = defineProps({
	cmd : String,
	database : String,
	table : String,
	sql : Object, // String | Array
	kwargs: Object,
});
const $emit = defineEmits(['update:sql']);
const self = new Vue({
	$emit,
	props,
    data: {
		hint: 'right click to copy the text, double click to execute the mysql statement',
		edit: false,
		rows: 0,
		cols: 0,

		wait: false,

		rowcount: [],
		errors: 0,
    },

    computed: {
		next() {
			return self.$parent.next;
		},

		cmds() {
			return self.$parent.cmds;
		},

		host() {
			return self.$parent.host;
		},

		user() {
			return self.$parent.user;
		},

		token() {
			return self.$parent.token;
		},

    	mysql_result_hint() {
    		var {rowcount} = self.$parent;
    		if (rowcount == null)
    			return 'Empty Set';

    		var hint;
    		switch (rowcount) {
    		case 0:
    			hint = 'Empty';
    			break;
    		case 1:
    			hint = '1 row in';
    			break;
    		default:
    			hint = `${rowcount} rows in`;
    			break;
    		}

    		return hint + ' set';
    	},

    	execute: {
			get() {
				var {kwargs} = self.kwargs;
				return kwargs? kwargs.execute: false;
			},

			set(execute) {
				var {kwargs} = self.kwargs;
				if (kwargs)
					kwargs.execute = execute;
				else
					self.kwargs.kwargs = {execute};
			}
    	},

    	repeat() {
			return self.execute == 'repeat';
    	},

    	rowsOfSQL() {
    		var {sql} = self;
    		if (sql.isArray)
    			return sql.length;

			return sql.split(/\n/).length;
    	},

    	style_p() {
    		var css = [];
    		if (self.rowsOfSQL > 12)
    			css.push("overflow-y: scroll");

    		if (self.rowsOfSQL > 1) {
    			css.push("white-space: pre");
        		var height = 20 * self.rowsOfSQL.clip(6, 12);
        		css.push(`height: ${height}px`);
    		}

    		if (self.wait)
    			css.push(`cursor: wait`);

    		return css.join("; ");
    	},

    	query() {
    		var {host} = self;
    		if (host && (self.$parent.from || self.$parent.from == 0))
       			host = null;
   			return sql => query(host, self.token, sql);
    	},
    },

	directives: {
		focus: {
			mounted(textarea) {
				textarea.scrollTop = textarea.scrollHeight;
				textarea.focus();
			},
		},

		click: {
			mounted(target, binding) {
				var self = binding.instance;
				if (self.execute)
					dblclick({target});
			},
		},

		clipboard,
	}
});

async function dblclick(event) {
	var {sql} = self;

	if (sql.isArray)
		sql.forEach(sql => {
			console.log(sql + ';');
		});
	else
		console.log(sql + ';');

	if (Array.isArray(sql)) {
		self.hint = 'right click to copy the text';
		self.wait = true;
		var rowcount = await self.query(sql);
		console.log("rowcount = ", rowcount);
		if (!rowcount.isArray) {
			alert(rowcount);
			return;
		}
		for (var [i, count] of enumerate(rowcount)) {
			if (count.isString) {
				alert(count);
				rowcount[i] = 0;
			}
		}

		self.rowcount.push(...rowcount);
		self.wait = false;
		rowcount = rowcount.sum();
		if (rowcount && self.repeat) {
			dblclick(event);
		}
		else {
			sql.clear();
			if (self.next)
				self.next();
		}
	}
	else{
		sql = sql.trim();
		if (sql.startsWith('replace'))
			return;

		if (sql.match(/^(select|with|show|with) /)){
			self.wait = true;
			var result = await self.query(sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">"));
			self.wait = false;

			var match = /^select \* from (\w+(\.\w+)?)/.exec(sql);
			if (match) {
				var tableName = match[1];
				sql = "replace into %s (%s) values ";
				if (result.length){
					var array = [];
					for (let dict of result) {
						console.log(dict);
						var values = [];
						for (let value of Object.values(dict)){
							var string = JSON.stringify(value);
							//string.match(/\\u[\da-f]+/)
							if (string.match(/\\u/)) {
								string = [...value].map(ch => {
									var hex = ord(ch).toString(16);
									if (hex.length & 1)
										hex = '0' + hex;
									return hex;
								});

								var maxLength = Math.max(...string.map(ch => ch.length));
								if (maxLength == 2) {
									string = string.join('');
									string = `x'${string}'`;
								}
								else {
									string = string.map(ch => ch.length == 4? ch: '00' + ch).join('');
									string = `_ucs2 0x${string}`;
								}
							}

							values.push(string);
						}
						array.push("(%s)".format(values.join(', ')));
					}

					sql = sql.format(tableName, Object.keys(result[0]).join(', '));

					self.hint = 'right click to copy the text or press Insert to edit the content';
					self.sql = sql + array.join(', ');
				}
				else
					self.sql = '[]';
			}
			else {
				var rowcount = result;
				if (rowcount && self.repeat) {
					self.rowcount.push(rowcount);
					self.hint = `execution of sql statement has succeeded, rowcount = ${rowcount}`;
					if (self.rowcount.length > 1) {
						self.hint += `, cumulative rowcount = ${self.rowcount.sum()}`;
					}
					dblclick(event);
				}
				else
					self.sql = JSON.stringify(result);
			}
		}
		else{
			sql = sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">");
			// var {database, table} = self.$parent;
			var {database, table} = self;
			if (table.match(/\W/)) {
				table = '`' + table + '`';
				if (table.match(/\//))
					table = table.replace(/\//g, '\\/');
			}

			var sqls = sql.split(new RegExp(`;\\n(?=update ${database}.${table} set \\w+ = .*)`));
			if (sqls.length > 1)
				sql = sqls;

			self.wait = true;
			try {
				var yields = await self.query(sql);
			}
			catch (err) {
				var yields = err;
			}

			if (yields && yields.isArray) {
				var rowcount = yields.sum();
			}
			else {
				var rowcount = parseInt(yields);
			}

			if (rowcount.isNaN) {
				++self.errors;

				var sleepPeriod = self.errors < 6? `${self.errors * 10} seconds`: `${self.errors / 6} minutes`;
				self.hint = `execution of sql has failed, sleeping for ${sleepPeriod}`;
				if (self.rowcount.length) {
					self.hint += `, previous rowcount = ${self.rowcount.back()}`;
					if (self.rowcount.length > 1)
						self.hint += `, cumulative rowcount = ${self.rowcount.sum()}`;
				}

				console.log(yields);
				if (self.repeat || confirm("error occurred during processing, retry?")) {
					setTimeout(()=>{
						dblclick(event);
					}, self.errors * 10000);
					return;
				}
			}
			else {
				if (self.errors) {
					self.errors >>= 1;
				}

				self.rowcount.push(rowcount);
				self.hint = `execution of sql statement has succeeded, rowcount = ${rowcount}`;
				if (self.rowcount.length > 1)
					self.hint += `, cumulative rowcount = ${self.rowcount.sum()}`;
				console.log(self.hint);
				if (rowcount && self.repeat) {
					if (self.rowsOfSQL > 1) {
						$parent.offset[0] = $parent.offset[1];
						self.execute = true;
						location.href = $parent.$refs.update.href_update;
					}
					else
						dblclick(event);
					return;
				}
				else
					self.sql = `rowcount = ${rowcount}`;
			}

			self.wait = false;
		}
	}
}

function mouseout_p(event){
	var self = event.target;
	var hover = self.parentElement.querySelector('.hover');
	hover.style.display = 'none';
}

function mouseover_p(event){
	var self = event.target;
	var hover = self.parentElement.querySelector('.hover');
	hover.style.display = "block";
	hover.style.left = event.pageX || event.clientX + document.body.scroolLeft;
	hover.style.top = event.pageY || event.clientY + document.body.scrollTop;
}

async function keydown(event){
	if (event.target.tagName == 'TEXTAREA'){
		switch (event.key){
		case 'S':
		case 's':
			if (!event.ctrlKey)
				break;
			event.preventDefault();

			var sql = event.target.value;
			var rowcount = await self.query(sql.replace(/&amp;/g, "&").replace(/&lt;/g, "<").replace(/&gt;/g, ">"));
			self.hint = 'right click to copy the text or press Insert to edit the content';
			self.edit = false;
			self.sql = sql;
			console.log(`rowcount of ${sql} = ${rowcount}`);
			break;
		}
	}
	else{
		switch (event.key){
		case 'Insert':
			event.preventDefault();

			self.edit = true;
			self.rows = 10;
			self.cols = 128;
			break;
		}
	}
}

function input_textarea(event){
	var sql = event.target.value;
	//console.log(sql);
	var text = JSON.parse(eval("[" + sql.match(/replace into (?:\._\w+)+ *\(\w+(?:, \w+)*\) *values *\((.*)\);$/)[1] + "]")[1]);
	$parent.data[0].text = text;
}

</script>

<style>
span.hover {
	display: none;
	color: red;
	transform: translate(4em, -100%);
	position: absolute;
	z-index: 10;
}

p.update {
	overflow-x: hidden;
}

</style>