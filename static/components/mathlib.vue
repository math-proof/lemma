<template>
	<div @keydown=keydown>
		<lemma v-for="lemma, index of lemma" :name=lemma.name :instImplicit=lemma.instImplicit :strictImplicit=lemma.strictImplicit :implicit=lemma.implicit :given=lemma.given :explicit=lemma.explicit :imply=lemma.imply :index=index></lemma>
	</div>
</template>

<script>
import lemma from "./lemma.vue"
import { mounted, click_left } from "../js/lemma.js"

console.log('import mathlib.vue');

export default {
	components: {
		lemma
	},
	props : [ 'lemma' ],
	
	created() {
	},

	data() {
		return {
			open_sections: [],
			sections: [],
			renderLean : {},
			selectedIndex: [],
		};
	},

	computed: {
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
				for (var lemma of this.lemma)
					delete lemma.type;
				await this.build();
				event.preventDefault();
				break;
			}
		},

		has_remaining() {
			for (var lemma of this.lemma) {
				var {type, imply} = lemma;
				if (!type || !imply || !imply.lean || !imply.latex)
					return true;
			}
		},

		async build(lemma) {
			if (!lemma) {
				for (var lemma of this.lemma) {
					var {type, imply} = lemma;
					if (!type || !imply || !imply.lean || !imply.latex)
						this.build(lemma);
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
					this.imply = {lean: '?', latex: '?'};
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
			while (this.has_remaining()) {
				// wait until all lemmas are built
				await sleep(10, 'waiting for all lemmas to be built');
			}
			// refresh the current page with ?mathlib=
			location.search = `?mathlib=`;
		}
	},
}
</script>

<style>
</style>