<template>
	<div @keydown=keydown>
		<lemma v-for="row, index in self.lemma" :name=row.name :instImplicit=row.instImplicit :strictImplicit=row.strictImplicit :implicit=row.implicit :explicit=row.explicit :given=row.given :default=row.default :imply=row.imply :index=index />
	</div>
</template>

<script setup>
import lemma from "./lemma.vue"
import Vue from "../js/vue.js"
import { mounted, click_left } from "../js/lemma.js"

console.log('import mathlib.vue');

const props = defineProps(['lemma']);

const self = new Vue({
	props,

	data() {
		return {
			open_sections: [],
			sections: [],
			renderLean: {},
			selectedIndex: [],
		};
	},

	methods: {
		leanSourceCode(index) {
			return this.lemma[index].type;
		},

		lemmaName(index) {
			return this.lemma[index].name;
		},

		new_file() {
			var {lemma} = this;
			var module = lemma[0].name;
			window.open(`?new=${module}`);
		},

		openContainingFolder() {
			var search = location.search;
			var m = search.match(/\?mathlib=(.*)/)
			var mathlib = m[1];
			location.search = `?q=${mathlib}&fullText=on`;
		},

		click_left,

		async keydown(event) {
			switch (event.key) {
			case 'F5':
				console.log('F5 is pressed, refreshing');
				for (var row of this.lemma)
					delete row.type;
				await this.build();
				event.preventDefault();
				break;
			}
		},

		has_remaining() {
			for (var row of this.lemma) {
				var {type, imply} = row;
				if (!type || !imply || !imply.lean || !imply.latex)
					return true;
			}
		},

		async build(lemma) {
			if (!lemma) {
				for (var row of this.lemma) {
					var {type, imply} = row;
					if (!type || !imply || !imply.lean || !imply.latex)
						this.build(row);
				}
				return;
			}
			var {name} = lemma;
			var {type, instImplicit, strictImplicit, implicit, given, default: explicit, imply} = await form_post('php/request/mathlib.php', {name});
			if (!type || !imply) {
	            var sql = `
delete from
    axiom.mathlib
where name = ${name.mysqlStr()};
`;
				if (!imply)
					lemma.imply = {lean: '?', latex: '?'};
			}
			else {
            	var sql = `
replace into 
    axiom.mathlib
    (name, type, instImplicit, strictImplicit, implicit, given, \`default\`, imply) 
    values (
        ${name.mysqlStr()},
		${type.mysqlStr()},
        ${instImplicit? instImplicit.mysqlStr(): null},
        ${strictImplicit? strictImplicit.mysqlStr(): null},
        ${implicit? implicit.mysqlStr(): null},
        ${given? JSON.stringify(given).mysqlStr(): null},
        ${explicit? explicit.mysqlStr(): null},
        ${JSON.stringify(imply).mysqlStr()}
    )
`;
				Object.assign(lemma, {type, instImplicit, strictImplicit, implicit, given, explicit, imply});
			}
            console.log(sql);
            var rowcount = await form_post('php/request/execute.php', {sql});
            console.log("rowcount =", rowcount);
		},
	},

	async mounted() {
		this.build();
		mounted(this);
		if (!getParameterByName('mathlib')) {
			var count = 0;
			while (this.has_remaining() && count++ < 30) {
				await sleep(10, `waiting ${count * 10} seconds for all lemmas to be built`);
			}
			location.search = `?mathlib=`;
		}
	},
});

const { keydown } = self.globals;
</script>

<style>
</style>