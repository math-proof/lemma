<template>
	<div class="page" :class="{ 'has-query': !!q }" @keydown=keydown>
		<header class="search-header">
			<div class="brand" :class="{ small: !!q }">
				<select class="mode" name="mode" form="search" aria-label="search mode" :value="mode" @change="onMode">
					<option value="lean">lean</option>
					<option value="word">word</option>
					<option value="path">path</option>
				</select><a href="."><span class="accent">2</span>latex</a>
			</div>
			<div class="search-slot">
				<searchForm variant="google" :ref="$refs.searchForm" :q=q :mode=mode :regularExpression=regularExpression :wholeWord=wholeWord :caseSensitive=caseSensitive :docstring=docstring :lean=lean :section=section :replacement=replacement :limit=limit></searchForm>
			</div>
		</header>
		<main class="results">
			<template v-if="q">
				<ol v-if="data.length">
					<li v-for="data, i of data">
						<searchLink :data=data :ref="el => self.searchLink[i] = el"></searchLink>
					</li>
				</ol>
				<p class="empty" v-else>No results for “{{q}}”.</p>
				<nav class="pager" v-if="more || offset > 0">
					<a v-if="offset > 0" class="prev" :href="prevHref">Previous</a>
					<a v-if="more" class="next" :href="nextHref" rel="next">Next</a>
				</nav>
			</template>
			<article v-else-if="home" class="home" v-html="home"></article>
		</main>
		<footer v-if="!q && footer" class="beian" v-html="footer"></footer>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js";
import searchForm from "./searchForm.vue";
import searchLink from "./searchLink.vue";

console.log('import searchResult.vue');

const props = defineProps(['data', 'q', 'mode', 'caseSensitive', 'wholeWord', 'regularExpression', 'docstring', 'lean', 'section', 'replacement', 'limit', 'offset', 'more', 'exact', 'similar', 'home', 'footer']);

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
			return searchQuery(this, Number(this.offset) || 0);
		},

		nextHref() {
			var limit = Number(this.limit) || 100;
			return searchQuery(this, (Number(this.offset) || 0) + limit);
		},

		prevHref() {
			var limit = Number(this.limit) || 100;
			return searchQuery(this, Math.max(0, (Number(this.offset) || 0) - limit));
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

		onMode(event) {
			var mode = event.target.value;
			this.setAttribute('mode', mode);
			if (this.q)
				location.search = searchQuery(this, 0, mode);
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

const { $refs, href, nextHref, prevHref, keydown, onMode } = self.globals;

function searchQuery(vm, offset, mode) {
	var {q, replacement, limit} = vm;
	var kwargs = {};
	if (q)
		kwargs.q = q.encodeURI();
	if (vm.caseSensitive)
		kwargs.caseSensitive = 'on';
	if (vm.wholeWord)
		kwargs.wholeWord = 'on';
	if (vm.regularExpression)
		kwargs.regularExpression = 'on';
	kwargs.mode = mode || vm.mode || 'lean';
	if (kwargs.mode == 'lean' && vm.section)
		kwargs.section = vm.section;
	if (replacement)
		kwargs.replacement = replacement.encodeURI();
	if (limit)
		kwargs.limit = limit;
	if (offset > 0)
		kwargs.offset = offset;
	return '?' + get_url(kwargs);
}
</script>

<style scoped>
:global(html:has(.page)),
:global(body:has(.page)) {
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

.page:not(.has-query) {
	display: flex;
	flex-direction: column;
}

.page:not(.has-query) .search-header {
	justify-content: center;
	padding-top: 8vh;
}

.page:not(.has-query) .results {
	flex: 1;
	width: 100%;
	max-width: none;
	margin: 12px 0 0;
}

.page:not(.has-query) .search-slot {
	flex: none;
	width: 100%;
}

/* Results page: logo left, search bar and results sharing the same column. */
.page.has-query {
	display: grid;
	grid-template-columns: max-content minmax(0, 1fr);
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
	width: 100%;
	min-width: 0;
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

.brand a {
	color: inherit;
	text-decoration: none;
}

.brand .mode {
	margin: 0;
	padding: 0 0.55em 0 0;
	border: none;
	border-radius: 4px;
	background-color: transparent;
	background-image: url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 12 8'><path fill='none' stroke='%235f6368' stroke-width='1.6' stroke-linecap='round' stroke-linejoin='round' d='M1.2 1.4 6 6.2 10.8 1.4'/></svg>");
	background-repeat: no-repeat;
	background-position: right center;
	background-size: 0.42em;
	font: inherit;
	letter-spacing: inherit;
	color: inherit;
	cursor: pointer;
	appearance: none;
	field-sizing: content;
	vertical-align: baseline;
}

.brand .mode:hover,
.brand .mode:focus {
	background: #f1f3f4;
	outline: none;
}

.page:not(.has-query) .brand {
	margin-bottom: 20px;
	font-size: 34px;
}

.search-slot {
	flex: 1;
	min-width: 0;
	max-width: 820px;
}

.results {
	max-width: 652px;
	margin: 8px 0 0;
}

ol {
	margin: 0;
	padding: 0;
	list-style: none;
	min-width: 0;
	max-width: 100%;
}

li {
	margin: 0 0 28px;
	min-width: 0;
	max-width: 100%;
}

.empty {
	margin: 40px 0;
	font-size: 14px;
	color: #5f6368;
	text-align: center;
}

.pager {
	display: flex;
	align-items: center;
	justify-content: center;
	gap: 32px;
	margin: 12px 0 28px;
	font-size: 18px;
}

.pager a {
	color: #1a0dab;
	text-decoration: none;
}

.pager a:hover {
	text-decoration: underline;
}

.pager .prev::before {
	content: "‹ ";
}

.pager .next::after {
	content: " ›";
}

.home {
	font-size: 14px;
	line-height: 1.55;
	color: #202124;
}

.home :deep(h1) {
	font-size: 20px;
	font-weight: 500;
	margin: 0 0 12px;
}

.home :deep(h2) {
	font-size: 16px;
	font-weight: 500;
	margin: 18px 0 8px;
}

.home :deep(a) {
	color: #1a0dab;
}

.home :deep(hr) {
	border: none;
	border-top: 1px solid #dadce0;
	margin: 18px 0;
}

.beian {
	margin-top: auto;
	padding: 28px 0 16px;
	text-align: center;
	font-size: 12px;
	color: #5f6368;
}

.beian :deep(img) {
	height: 18px;
	vertical-align: middle;
	margin-right: 6px;
}

.beian :deep(a) {
	color: #5f6368;
	text-decoration: none;
	margin: 0 8px;
}

.beian :deep(a:hover) {
	text-decoration: underline;
}
</style>
