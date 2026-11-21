<template>
	<searchForm :keyword=latex :latex=true :regularExpression=false :wholeWord=false :caseSensitive=false :limit=limit :offset=offset></searchForm>
	latex in search:
	<p v-text="`\\[${latex}\\]`"></p>
	<a :href=href>search</a> results:
	<br>
	in all, there are {{list.length}} hits:
	<br>
	<ul>
    	<li v-for="result of list">
    		similarity = {{result.similarity}}, id = <a :href="`query.php?user=user&from[axiom]=MathIR&id=${result.id}`" target="searchResult">{{result.id}}</a>
			<p v-text="`\\[${result.latex}\\]`"></p>
    	</li>
	</ul>
</template>

<script>
console.log('import searchLatexResult.vue');
import searchForm from "./searchForm.vue"
//import searchLink from "./searchLink.vue"

export default {
	components: {searchForm},

	props : ['list', 'latex', 'limit', 'offset'],

	async created() {
		console.log(this.list);
		console.log(this.latex);
		for (var obj of this.list) {
			var {id} = obj;
			var [{latex}] = await query('localhost', 'user', null, `select latex from axiom.MathIR where id = ${id}`);
			obj.latex = latex;
		}
	},

	computed: {
		href() {
			var {latex, limit, offset} = this;
			var kwargs = {};
			if (latex)
				kwargs.keyword = latex.encodeURI();
			kwargs.latex = 'on';
			if (limit)
				kwargs.limit = limit;
			if (offset)
				kwargs.offset = offset;
			return '?' + get_url(kwargs);
		},
	},

	methods: {
	},		
}

</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>