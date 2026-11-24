<template>
	<div class="page" :class="{ 'has-query': !!q }" @keydown=keydown>
		<header class="search-header">
			<a class="brand" :class="{ small: !!q }" href=".">Lean<span class="accent">2</span>Latex</a>
			<div class="search-slot">
				<searchForm variant="google" :ref="$refs.searchForm" :q=q :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive :fullText=fullText :lean=lean :section=section :replacement=replacement :limit=limit></searchForm>
			</div>
		</header>
		<main class="results">
			<p class="stats" v-if="data.length">
				<span v-if="shownLabel">{{shownLabel}} · </span>{{data.length}} result{{data.length == 1 ? '' : 's'}}
			</p>
			<ol v-if="data.length">
				<li v-for="data, i of data">
					<searchLink :data=data :ref="el => self.searchLink[i] = el"></searchLink>
				</li>
			</ol>
			<p class="empty" v-else-if="q">No results for “{{q}}”.</p>
		</main>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js";
import searchForm from "./searchForm.vue";
import searchLink from "./searchLink.vue";

console.log('import searchResult.vue');

const props = defineProps(['data', 'q', 'caseSensitive', 'wholeWord', 'regularExpression', 'fullText', 'lean', 'section', 'replacement', 'limit', 'exact', 'similar']);

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
		// `data` is already `exact` when it has hits, otherwise `similar`
		// (mjs/lean/buildSearchPayload.mjs); only the heading differs.
		shownLabel() {
			if (!this.lean)
				return null;
			if (this.exact && this.exact.length)
				return 'exact matches';
			if (this.similar && this.similar.length)
				return 'similarity matches';
			return null;
		},

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
			if (this.lean)
				kwargs.lean = 'on';
			if (this.lean && this.section)
				kwargs.section = this.section;
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

const { $refs, href, keydown, shownLabel } = self.globals;
</script>

<style scoped>
:global(body) {
	margin: 0;
	background-color: #fff;
}

.page {
	box-sizing: border-box;
	min-height: 100vh;
	padding: 0 20px 60px;
	background: #fff;
	font-family: Arial, sans-serif;
	color: #202124;
}

.search-header {
	display: flex;
	flex-direction: column;
	align-items: center;
	padding: 22px 0 10px;
	background: #fff;
}

.page:not(.has-query) .search-header {
	justify-content: center;
	min-height: 46vh;
	padding-top: 0;
}

.page:not(.has-query) .search-slot {
	flex: none;
	width: 100%;
}

/* Results page: logo left, search bar and results sharing the same column. */
.page.has-query {
	display: grid;
	grid-template-columns: max-content minmax(0, 652px);
	column-gap: 20px;
	row-gap: 6px;
	align-items: start;
	padding-top: 22px;
}

.page.has-query .search-header {
	display: contents;
}

.page.has-query .brand {
	padding-top: 10px;
}

.page.has-query .results {
	grid-column: 2;
	max-width: none;
	margin: 6px 0 0;
}

.brand {
	flex: none;
	font-size: 30px;
	font-weight: 500;
	letter-spacing: -1.5px;
	color: #5f6368;
	text-decoration: none;
	white-space: nowrap;
}

.brand.small {
	font-size: 26px;
	letter-spacing: -1.2px;
}

.brand .accent {
	color: #4285f4;
}

.page:not(.has-query) .brand {
	margin-bottom: 20px;
	font-size: 34px;
}

.search-slot {
	flex: 1;
	min-width: 0;
	max-width: 634px;
}

.results {
	max-width: 652px;
	margin: 8px 0 0;
}

.stats {
	margin: 6px 0 22px;
	font-size: 13px;
	color: #70757a;
}

ol {
	margin: 0;
	padding: 0;
	list-style: none;
}

li {
	margin: 0 0 28px;
}

.empty {
	margin: 40px 0;
	font-size: 14px;
	color: #5f6368;
	text-align: center;
}
</style>
