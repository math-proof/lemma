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
				<td>{{count[0] - whitelist.length}}</td>
			</tr>
			<tr>
				<td>whitelist</td>
				<td>{{whitelist.length}}</td>
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
			most wanted <input size=2 v-model=topk @change=change_input />of {{count[0] - whitelist.length}} unformalized lemmas: <br>
			<table tabindex=0 align=left border=1>
				<tr>
					<th>lemma</th>
					<th>depth</th>
				</tr>
				<tr v-for="data of wantedLemma">
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
			whitelist : [
				'Bool.Cond.of.Eq.Cond.subst',
				'Bool.Cond.of.Iff.Cond.subst',
				'Bool.All_In_Insert.Is.And_All', // Bool.AllIn_Insert.Is.And_All
				'Bool.Cond.of.All_Imp', 
				'Bool.All.of.Given', // plausible
				'Bool.All.of.Cond', // plausible
				'Bool.Imp.Is.All', // plausible

				'Set.Eq.of.ImpIn.ImpIn', // plausible
				
				'Algebra.Eq.of.Ge.squeeze',
				'Algebra.Ge.Is.Eq.squeeze',
				'Algebra.EqSumS.of.Eq', // Algebra.EqSumS.of.All_Eq
				'Algebra.GeSqrt_0.of.Ge_0', // Algebra.GeSqrt_0

				'Tensor.Ne_0.Ne_0.of.Mul.ne.Zero', // Algebra.Ne_0.Ne_0.of.Mul.ne.Zero
				'Tensor.EqStackS.of.Eq', // Tensor.EqStackS.of.All_Eq
			],
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
		
		async updateUnformalizedLemma() {
			// select the top level lemmas;
			var sql = `
select
	distinct h_left.caller
from
	axiom.hierarchy as h_left
	left join 
		axiom.hierarchy as h_right 
		on 
			h_left.user = h_right.user and 
			h_left.caller = h_right.callee
where
	h_right.callee is null and 
	h_left.user = 'py' 
limit 1`;
			console.log(sql);
			var data = await form_post('php/request/execute.php', {sql, resultType: 1});
			// var caller = 'Tensor.LogSoftmax.eq.Sub_LogSumExpSub_Max';
			var caller = 'Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate';
			data = [{caller}];
			console.log(data);
			data = data.map(row => row.caller);
			var sql = `
with _t as (
	WITH RECURSIVE dependencies AS (
		SELECT
			caller,
			0 AS depth
		from json_table(
			${JSON.stringify(data).mysqlStr()},
			'$[*]' columns (caller varchar(256) path '$')
		) as jt
		UNION ALL
		SELECT
			callee,
			depth + 1
		FROM
			dependencies
		JOIN
			axiom.hierarchy using (caller)
	)
	SELECT REPLACE(caller, '.given.', '.of.') as module, max(depth) as depth FROM dependencies
	group by caller
)
select 
	_t.module, _t.depth
from 
	_t
	left join 
		axiom.lemma as _s 
		on 
			_s.module = regexp_replace(_t.module, '\\\\.[a-z]+$', '', 1, 0, 'c')
where 
	_s.module is null and 
	not json_contains(${JSON.stringify(this.whitelist).mysqlStr()}, json_quote(_t.module))
order by depth desc
limit ${this.topk}`;
			console.log(sql);
			this.wantedLemma = await form_post('php/request/execute.php', {sql, resultType: 1});
			console.log(this.wantedLemma);
		},

		change_input(event){
			this.updateUnformalizedLemma();
		},

		async fetchFormalizationStatus() {
			var sql = `
with statistic as (
	select 
		_t.axiom, 
		if (_s.module is null, 0, 1) as status
	from 
		axiom.axiom as _t
		left join 
			axiom.lemma as _s 
			on 
				_s.module = regexp_replace(_t.axiom, '\\\\.[a-z]+$', '', 1, 0, 'c')
)
select 
	count(*) as count,
	status 
from 
	statistic 
group by status`;
			console.log(sql);
			var list = await form_post('php/request/execute.php', {sql, resultType: 1});
			for (var {count, status} of list)
				this.count[status] = parseInt(count);
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
		this.fetchFormalizationStatus();
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