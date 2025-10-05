<template>
	<div tabindex=1 @keydown=keydown>
		the whole math repertoire is composed of the following sections:
		<searchForm v-if="issearch" :q=q :caseSensitive=caseSensitive :wholeWord=wholeWord :regularExpression=regularExpression :latex=latex :fullText=fullText></searchForm>		
		<ul>
			<li v-for="(content, section) in repertoire">
				<a :href=href_section(section)>
					{{section}}
				</a>
				<ul>
					<li v-for="(axioms, type) in content">
						<font :class=type>
							{{type}}:
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
		in summary, the following is the total count of each type for all lemmas:
		<br>
		<table tabindex=2 align=left border=1>
			<tr>
				<th>type</th>
				<th>count</th>
			</tr>
			<tr v-for="tuple of state_count_pairs">
				<td><a :href="href_state(tuple.type)">{{tuple.type}}</a></td>
				<td>{{tuple.count}}</td>
			</tr>
		</table>
		<table tabindex=2 align=left border=1>
			<tr>
				<th>section</th>
				<th>count</th>
			</tr>
			<tr v-for="tuple of sectionStatistics">
				<td><a :href="`?module=${tuple.section}`">{{tuple.section}}</a></td>
				<td>{{tuple.count}}</td>
			</tr>
		</table><br>
		<div class=clear>
			most recent <input size=2 v-model=topk @change=change_input>axioms updated:
			<a v-for="axiom of recentAxioms" :href=href_module(axiom)>
				<p>{{axiom}}</p>
			</a>
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
		user() {
			return axiom_user();
		},	
	},
	
	data() {
		return {
			issearch: false,
			sectionStatistics: [],
			recentAxioms: [],
			topk: 10,
			q: '',
			caseSensitive: false,
			wholeWord: false, 
			regularExpression: false,
			latex: null,
			fullText: false
		};
	},

	created() {
		this.updateRecentAxioms();
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

		href_state(type){
			if (type == 'total')
				return `/${this.user}/run.py`;
			var {user} = this;
			return `/${user}/?type=${type}`;
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
		
		async updateRecentAxioms() {
			this.recentAxioms = await get(`php/request/recent.php?top=${this.topk}`);;
		},
		
		change_input(event){
			this.updateRecentAxioms();
		},

		async updateSectionStatistics() {
			var sql = `
select
	SUBSTRING_INDEX(module, '.', 1) as section,
	count(*) as count
from axiom.lemma
where
	user = 'lean' and json_length(imports) > 0 
group by
	section
WITH ROLLUP;`;
			console.log(sql);
			this.sectionStatistics = await form_post('php/request/execute.php', {sql, resultType: 1});
			console.log(this.sectionStatistics);
		},
	},
	
	mounted() {
		var error = document.querySelector('a[href$=error]') || 
			document.querySelector('a[href$=warning]') || 
			document.querySelector('a[href$=unprovable]');
		if (error)
			error.focus();
		this.updateSectionStatistics();
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

font.error{
	color: red;
}

font.unprovable{
	color: green;
}

font.warning{
	color: yellow;
}

div.clear{
	clear: both;
}

</style>