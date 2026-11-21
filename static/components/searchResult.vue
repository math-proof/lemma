<template>
	<searchForm ref=searchForm :keyword=keyword :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive :replacement=replacement :limit=limit :offset=offset @keydown=keydown></searchForm>
	<a :href=href>search</a> results:
	<br>
	in all, there are {{list.length}} hits:
	<br>
	<ul>
    	<li v-for="module, i of list">
    		<searchLink :module=module :ref="el => searchLink[i] = el"></searchLink>
    	</li>
	</ul>
</template>

<script>
console.log('import searchResult.vue');
import searchForm from "./searchForm.vue"
import searchLink from "./searchLink.vue"

export default {
	components: {searchForm, searchLink},

	props : ['list', 'keyword', 'state', 'caseSensitive', 'wholeWord', 'regularExpression', 'latex', 'replacement', 'limit', 'offset'],

	data(){
		return {
			searchLink: [],
		};
	},

	computed: {
		href() {
			var {keyword, state, replacement, limit, offset} = this;
			var kwargs = {};
			if (keyword != null)
				kwargs.keyword = keyword.encodeURI();
			else if (state != null)
				kwargs.state = state.encodeURI();
			if (this.caseSensitive)
				kwargs.caseSensitive = 'on';
			if (this.wholeWord)
				kwargs.wholeWord = 'on';
			if (this.regularExpression)
				kwargs.regularExpression = 'on';
			if (this.latex)
				kwargs.latex = 'on';
			if (replacement)
				kwargs.replacement = replacement.encodeURI();
			if (limit)
				kwargs.limit = limit;
			if (offset)
				kwargs.offset = offset;
			return '?' + get_url(kwargs);
		},
	},

	methods: {
		keydown(event) {
			switch (event.key) {
			case 'h':
				if (!event.ctrlKey)
					break;
				
				console.log('ctrl+H for replacement');
				setAttribute(this, 'replacement', this.replacement == null? '' : null);
				event.preventDefault();
				break;
			}
		},

		async replace(event) {
			var {searchLink: [searchLink]} = this;
			await searchLink.replace();
			this.list.shift();
			this.$nextTick(() => {
				if (this.list.length)
					this.searchLink[0].focus();
			});
		},

		async replaceAll(event) {
			while (this.list.length)
				await this.replace();
		},
	},		
}

</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>