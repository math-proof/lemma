<template>
	<div tabindex=1 @keydown=keydown>
		the whole math repertoire is composed of the following sections:
		<searchForm v-if="issearch" :keyword=keyword :caseSensitive=caseSensitive :wholeWord=wholeWord :regularExpression=regularExpression :latex=latex></searchForm>		
		<ul>
			<li v-for="(content, section) in repertoire">
				<a :href=href_section(section)>
					{{section}}
				</a>
				<ul>
					<li v-for="(axioms, state) in content">
						<font :class=state>
							lemmas {{state}}:
						</font>
						<ul>
							<li v-for="axiom in axioms">
								<a :href=href_module(axiom)>
									{{axiom}}
								</a>
							</li>
						</ul>
					</li>
				</ul>
			</li>
		</ul>
		<br>
		in summary, the following is the total count of each state for all lemmas:
		<br>
		<table tabindex=0 align=left border=1>
			<tr>
				<th>state</th>
				<th>count</th>
			</tr>
			<tr v-for="tuple of state_count_pairs">
				<td><a :href="href_state(tuple.state)">{{tuple.state}}</a></td>
				<td>{{tuple.count}}</td>
			</tr>
		</table>
		<table tabindex=0 align=left border=1>
			<tr>
				<th colspan="2">formalization status of lemmas</th>
			</tr>
			<tr>
				<th>state</th>
				<th>count</th>
			</tr>
			<tr>
				<td>unformalized</td>
				<td>{{count[0]}}</td>
			</tr>
			<tr>
				<td>formalized</td>
				<td>{{count[1]}}</td>
			</tr>
			<tr>
				<td>total</td>
				<td>{{count[0] + count[1]}}</td>
			</tr>
		</table><br>
		<div class=clear>
			most wanted <input size=2 v-model=topk @change=change_input />of {{count[0]}} unformalized lemmas (topological order, basic &rarr; complex): <br>
			<table tabindex=0 align=left border=1>
				<tr>
					<th>#</th>
					<th>lemma</th>
					<th>dependents</th>
				</tr>
				<tr v-for="(data, index) of wantedLemma">
					<td>{{index + 1}}</td>
					<td><a :href=href_module(data.module) target="_blank">{{data.module}}</a></td>
					<td>{{data.depth}}</td>
				</tr>
			</table>
		</div>
		<br>
	</div>
</template>

<script>
console.log('import axiomSummary.vue');

import searchForm from "./searchForm.vue"

export default {
	components: {searchForm},

	props : ['state_count_pairs', 'repertoire'],
	
	computed: {
		user(){
			return axiom_user();
		},
	},
	
	data(){
		return {
			issearch: false,
			wantedLemma: [],
			topk: 10,
			
			keyword: '',
			caseSensitive: false,
			wholeWord: false, 
			regularExpression: false,
			latex: null,
			count: [],
		};
	},

	methods: {
		href_section(section) {
			var {user} = this;
			return `/${user}/?module=${section}`;
		},

		href_module(axiom) {
			var {user} = this;
			return `/${user}/?module=${axiom}`;
		},

		href_state(state){
			if (state == 'total'){
				return `/${this.user}/run.py`;
			}
			var {user} = this;
			return `/${user}/?state=${state}`;
		},
	
		keydown(event){
			switch(event.key){
			case 'f':
			case 'F':
				if (event.ctrlKey){
					this.issearch = true;
					event.preventDefault();
				}
			}
		},
		
		// path normalization: given→of, Is→is, In→in (py↔lean case of section tokens)
		normPath(name) {
			return name
				.replace(/\.given\./g, '.of.')
				.replace(/\.Is\./g, '.is.')
				.replace(/\.In\./g, '.in.');
		},

		// axiom is formalized iff some lean module equals the normalized axiom,
		// or equals it minus its last lowercase component (lean @[path] / tag suffix)
		formalizedSet(module_rows) {
			var strip = (name) => name.replace(/\.[a-z_0-9]+$/, '');
			var formalized = new Set();
			for (var {module} of module_rows) {
				module = this.normPath(module.replace(/'/g, ''));
				formalized.add(module);
				formalized.add(strip(module));
			}
			return formalized;
		},

		isFormalized(axiom, formalized) {
			var strip = (name) => name.replace(/\.[a-z_0-9]+$/, '');
			var norm = this.normPath(axiom);
			return formalized.has(norm) || formalized.has(strip(norm));
		},

		async updateUnformalizedLemma() {
			// unformalized = no matching lean lemma (independent of py proved/unproved)
			var user = this.user;
			var [hierarchy, axiom_rows, module_rows] = await Promise.all([
				form_post('php/request/execute.php', {sql: `select caller, callee from axiom.hierarchy where user = '${user}'`, resultType: 1}),
				form_post('php/request/execute.php', {sql: `select axiom from axiom.axiom where user = '${user}'`, resultType: 1}),
				form_post('php/request/execute.php', {sql: `select module from axiom.lemma where user = 'lean'`, resultType: 1}),
			]);
			var formalized = this.formalizedSet(module_rows);
			var unformalized = new Set();
			this.count = [0, 0];
			for (var {axiom} of axiom_rows) {
				var ok = this.isFormalized(axiom, formalized);
				++this.count[ok ? 1 : 0];
				if (!ok) unformalized.add(axiom);
			}

			// build dependency graph: caller depends on callee
			var deps = {}, dependents = {}, nodes = new Set();
			for (var {caller, callee} of hierarchy){
				(deps[caller] ??= new Set()).add(callee);
				(dependents[callee] ??= new Set()).add(caller);
				nodes.add(caller);
				nodes.add(callee);
			}

			// include isolated unformalized axioms (no recorded dependency edges)
			for (var a of unformalized)
				nodes.add(a);

			// transitive dependent count (wantedness), cycle-safe
			var tdep = {};
			function countDependents(n, stack){
				if (n in tdep) return tdep[n];
				if (stack.has(n)) return new Set();
				stack.add(n);
				var s = new Set();
				for (var c of dependents[n] ?? []){
					s.add(c);
					for (var d of countDependents(c, stack)) s.add(d);
				}
				stack.delete(n);
				tdep[n] = s;
				return s;
			}

			// Kahn topological order; tie-break: most dependents first
			var indeg = {};
			for (var n of nodes) indeg[n] = (deps[n] ?? new Set()).size;
			var heap = [];
			for (var n of nodes) if (indeg[n] === 0) heap.push(n);
			heap.sort((a, b) => countDependents(b, new Set()).size - countDependents(a, new Set()).size);
			var order = [];
			while (heap.length){
				var n = heap.shift();
				order.push(n);
				for (var c of dependents[n] ?? []){
					if (--indeg[c] === 0){
						heap.push(c);
						heap.sort((a, b) => countDependents(b, new Set()).size - countDependents(a, new Set()).size);
					}
				}
			}

			// first `topk` unformalized lemmas in topological order (basic → complex)
			var wanted = order.filter(a => unformalized.has(a)).slice(0, this.topk);
			this.wantedLemma = wanted.map(a => ({module: this.normPath(a), depth: countDependents(a, new Set()).size}));
			console.log(this.wantedLemma);
		},

		change_input(event){
			this.updateUnformalizedLemma();
		},
	},
	
	mounted(){
		var failed = document.querySelector('a[href$=failed]') || 
		document.querySelector('a[href$=plausible]')  || 
		document.querySelector('a[href$=unproved]') || 
		document.querySelector('a[href$=unprovable]') || 
		document.querySelector('a[href$=slow]');
		if (failed)
			failed.focus();
		this.updateUnformalizedLemma();
	},
}
</script>

<style scoped>
table{
	margin-left: 4em;
}

div:focus{
	outline: none;
}

font.slow{
	color: yellow;
}

font.failed{
	color: red;
}

font.unprovable{
	color: green;
}

font.plausible{
	color: red;
}

font.unproved{
	color: purple;
}

div.clear{
	clear: both;
}
</style>