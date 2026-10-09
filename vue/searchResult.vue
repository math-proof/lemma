<template>
	<div @keydown=keydown>
		<searchForm :ref="$refs.searchForm" :q=q :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive :fullText=fullText :replacement=replacement :limit=limit></searchForm>
		<a :href=href>search</a> results:
		<br>
		in all, there are {{data.length}} hits:
		<br>
		<ul>
			<li v-for="data, i of data">
				<searchLink :data=data :ref="el => self.searchLink[i] = el"></searchLink>
			</li>
		</ul>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js";
import searchForm from "./searchForm.vue";
import searchLink from "./searchLink.vue";

console.log('import searchResult.vue');

const props = defineProps(['data', 'q', 'caseSensitive', 'wholeWord', 'regularExpression', 'fullText', 'replacement', 'limit']);

const self = new Vue({
	props,

	$refs: {
		searchForm: null,
	},

	data() {
		return {
			searchLink: [],
		};
	},

	computed: {
		href() {
			var {q, replacement, limit} = this;
			var kwargs = {};
			if (q)
				kwargs.q = q.encodeURI();
			if (this.caseSensitive)
				kwargs.caseSensitive = 'on';
			if (this.wholeWord)
				kwargs.wholeWord = 'on';
			if (this.regularExpression)
				kwargs.regularExpression = 'on';
			if (this.fullText)
				kwargs.fullText = 'on';
			if (replacement)
				kwargs.replacement = replacement.encodeURI();
			if (limit)
				kwargs.limit = limit;
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
				this.setAttribute('replacement', this.replacement == null? '' : null);
				event.preventDefault();
				break;
			case 'f':
				if (!event.ctrlKey)
					break;
				console.log('ctrl+F for search');
				this.searchForm.focus();
				event.preventDefault();
				break;
			}
		},

		async replace(event) {
			var {searchLink: [searchLink]} = this;
			await searchLink.replace();
			this.data.shift();
			this.$nextTick(() => {
				if (this.data.length)
					this.searchLink[0].focus();
			});
		},

		async replaceAll(event) {
			while (this.data.length)
				await this.replace();
		},

		window_open(module) {
			setTimeout(async seconds => {
				await sleep(seconds);
				window.open(
					location.origin + location.pathname + `?module=${module}#window.close`,
					'_blank'
				);
			}, 1000, 1);
		},
	},

	async mounted() {
		var {hash} = location;
		if (hash == '#window.close') {
			var count = 0;
			for (var {module} of this.data) {
				this.window_open(module);
				await sleep(1);
				console.log(`count = ${++count}
module = ${module}`);
			}
		}
	},
});

const { $refs, href, keydown } = self.globals;
</script>

<style scoped>
li {
	margin-top: 1em;
}
</style>
