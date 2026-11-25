<template>
	<form v-if="variant == 'google'" id="search" name=search class="google" method=get :action=action @keydown=keydown>
		<div class="bar-row">
			<div class="bar">
				<svg class="icon" viewBox="0 0 24 24" aria-hidden="true">
					<path d="M15.5 14h-.79l-.28-.27a6.471 6.471 0 0 0 1.48-4.24A6.5 6.5 0 1 0 9.5 16c1.61 0 3.09-.59 4.24-1.48l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/>
				</svg>
				<input v-focus tabindex=1 type=text spellcheck=false name=q :value=q :placeholder=placeholder title="a space commits the latex command" @input=input>
				<button tabindex=1 class="submit" type=submit>Search</button>
			</div>
			<details class="options">
				<summary title="Tools" aria-label="Tools">
					<svg viewBox="0 0 24 24" width="20" height="20" aria-hidden="true">
						<path d="M19.14 12.94c.04-.3.06-.61.06-.94 0-.32-.02-.64-.07-.94l2.03-1.58a.49.49 0 0 0 .12-.61l-1.92-3.32a.488.488 0 0 0-.59-.22l-2.39.96c-.5-.38-1.03-.7-1.62-.94l-.36-2.54a.484.484 0 0 0-.48-.41h-3.84c-.24 0-.43.17-.47.41l-.36 2.54c-.59.24-1.13.57-1.62.94l-2.39-.96c-.22-.08-.47 0-.59.22L2.74 8.87c-.12.21-.08.47.12.61l2.03 1.58c-.05.3-.09.63-.09.94s.02.64.07.94l-2.03 1.58a.49.49 0 0 0-.12.61l1.92 3.32c.12.22.37.29.59.22l2.39-.96c.5.38 1.03.7 1.62.94l.36 2.54c.05.24.24.41.48.41h3.84c.24 0 .44-.17.47-.41l.36-2.54c.59-.24 1.13-.56 1.62-.94l2.39.96c.22.08.47 0 .59-.22l1.92-3.32c.12-.22.07-.47-.12-.61l-2.01-1.58zM12 15.6c-1.98 0-3.6-1.62-3.6-3.6s1.62-3.6 3.6-3.6 3.6 1.62 3.6 3.6-1.62 3.6-3.6 3.6z"/>
					</svg>
				</summary>
				<div class="panel">
					<div class="option-row" v-if="mode == 'lean'">
						<span class="option-title">Section</span>
						<label><input tabindex=-1 type=checkbox name=section value=given :checked="sectionList.includes('given')">Given</label>
						<label><input tabindex=-1 type=checkbox name=section value=imply :checked="sectionList.includes('imply')">Imply</label>
						<label><input tabindex=-1 type=checkbox name=section value=proof :checked="sectionList.includes('proof')">Proof</label>
					</div>
					<div class="option-row" v-if="mode == 'path'">
						<label><input tabindex=-1 type=checkbox name=caseSensitive :checked=caseSensitive>Case</label>
						<label><input tabindex=-1 type=checkbox name=wholeWord :checked=wholeWord>WholeWord</label>
						<label><input tabindex=-1 type=checkbox name=regularExpression :checked=regularExpression>Regex</label>
					</div>
					<div class="option-row" v-if="replacement != null">
						<input tabindex=1 name=replacement :value=replacement placeholder='input the replacement word' @input=input />
						Replace <button tabindex=1 type=button @click=replace>One</button>/<button tabindex=1 type=button @click=replaceAll>All</button>
					</div>
					<div class="option-row">
						limit: <input tabindex=1 name=limit :value=limit placeholder='100' @input=input />
					</div>
				</div>
			</details>
		</div>
		<input id=submit_query type=submit value=query style="display: none;" />
	</form>
	<form v-else name=search method=post :action=action @keydown=keydown>
		<input v-focus tabindex=1 type=text spellcheck=false name=q size=48 :value=q placeholder='input a hint in search of a formula/theorem/axiom' @input=input>
		<br>
		<template v-if="replacement != null" >
			<input v-focus tabindex=1 name=replacement :value=replacement placeholder='input the replacement word' @input=input />
			Replace <button tabindex=1 type=button @click=replace>One</button>/<button tabindex=1 type=button @click=replaceAll>All</button>
			<br>
		</template>

		<input tabindex=-1 type=checkbox name=caseSensitive :checked=caseSensitive><u>C</u>ase
			
		<input tabindex=-1 type=checkbox name=wholeWord :checked=wholeWord><u>W</u>holeWord
		
		<input tabindex=-1 type=checkbox name=regularExpression :checked=regularExpression><u>R</u>egex
		
		<input tabindex=-1 type=checkbox name=lean :checked=lean @change=change><u>L</u>ean

		<input tabindex=-1 type=checkbox name=docstring :checked=docstring><u>d</u>ocstring
		<br>
		limit: <input tabindex=1 name=limit :value=limit placeholder='100' @input=input />
		<input id=submit_query type=submit value=query style="display: none;" />
	</form>
</template>

<script setup>
import Vue from "../js/vue.js";

console.log('import searchForm.vue');

const props = defineProps(['q', 'mode', 'caseSensitive', 'wholeWord', 'regularExpression', 'docstring', 'lean', 'section', 'replacement', 'limit', 'variant']);

const self = new Vue({
	props,

	computed: {
		user() {
			return axiom_user();
		},

		sectionList() {
			var raw = String(this.section || 'imply');
			return raw.split(',').map((name) => name.trim()).filter(Boolean);
		},

		placeholder() {
			if (this.mode == 'word')
				return 'search a sentence, e.g. 悬链线';
			if (this.mode == 'path')
				return 'search a path token, e.g. Cosh';
			return 'type latex command: \\sqrt,\\sum,\\int,\\prod,\\McB,\\bbP,\\pi,\\in,\\ge,\\le,\\ne,\\subset,\\^2,\\^m';
		},

		action() {
			return `/${this.user}/`;
		},
	},

	methods: {
		input(event) {
			const el = event.target;
			const value = el.value;
			this.setAttribute(el.name, value);
			if (el.name != 'q')
				return;
			const caret = el.selectionStart ?? value.length;
			if (caret < 1 || value[caret - 1] != ' ')
				return;
			const head = value.slice(0, caret - 1);
			const matched = head.match(/\\([^\s\\]+)$/);
			if (!matched)
				return;
			const latex = matched[1];
			const start = caret - 1 - matched[0].length;
			const snapshot = value;
			fetch(`request/unicode?latex=${encodeURIComponent(latex)}`)
				.then((response) => response.ok ? response.json() : null)
				.then((body) => {
					const ch = body && body.unicode;
					if (!ch || typeof ch != 'string')
						return;
					const input = this.$el?.querySelector('input[name=q]');
					if (!input || input.value != snapshot)
						return;
					const next = snapshot.slice(0, start) + ch + snapshot.slice(caret);
					const pos = start + ch.length;
					this.setAttribute('q', next);
					input.value = next;
					input.setSelectionRange(pos, pos);
				})
				.catch(() => {});
		},

		change(event) {
			var {name, checked} = event.target;
			this.setAttribute(name, checked);
			if (name == 'lean' && checked)
				this.clearSearchOptions();
		},

		clearSearchOptions() {
			for (var name of ['caseSensitive', 'wholeWord', 'regularExpression', 'docstring'])
				this.setAttribute(name, false);
		},

		keydown(event) {
			if (event.altKey){
				switch(event.key){
				case 'c':
					this.setAttribute('caseSensitive', !this.caseSensitive);
					break;
				case 'w':
					this.setAttribute('wholeWord', !this.wholeWord);
					break;
				case 'r':
					this.setAttribute('regularExpression', !this.regularExpression);
					break;
				case 'l': {
					var lean = !this.lean;
					this.setAttribute('lean', lean);
					if (lean)
						this.clearSearchOptions();
					break;
				}
				case 'd':
					this.setAttribute('docstring', !this.docstring);
					break;
				}
			}
		},

		replace(event) {
			const proxy = this.$$instance?.parent?.proxy;
			(this.$parent.replace || proxy?.replace)?.call(proxy ?? this.$parent, event);
			event.preventDefault();
		},

		replaceAll(event) {
			const proxy = this.$$instance?.parent?.proxy;
			(this.$parent.replaceAll || proxy?.replaceAll)?.call(proxy ?? this.$parent, event);
			event.preventDefault();
		},

		focus() {
			this.$el.querySelector('input[name=q]').focus();
		},
	},

	directives: {
		focus: {
			mounted(el) {
				el.focus();
			},
		},
	},
});

const { action, keydown, input, change, replace, replaceAll, sectionList, placeholder } = self.globals;
</script>

<style scoped>
form[name=search]:not(.google) {
	float: right;
}

form.google {
	width: 100%;
	margin-left: 0;
}

form.google .bar-row {
	display: flex;
	align-items: center;
	gap: 10px;
}

form.google .bar {
	flex: 1;
	min-width: 0;
	display: flex;
	align-items: center;
	gap: 8px;
	height: 46px;
	padding: 0 8px 0 14px;
	border: 1px solid #dfe1e5;
	border-radius: 24px;
	background: #fff;
	transition: box-shadow .15s, border-color .15s;
}

form.google .bar:hover,
form.google .bar:focus-within {
	border-color: rgba(223, 225, 229, 0);
	box-shadow: 0 1px 6px rgba(32, 33, 36, .28);
}

form.google .icon {
	width: 20px;
	height: 20px;
	flex: none;
	fill: #9aa0a6;
}

form.google input[name=q] {
	flex: 1;
	min-width: 0;
	border: 0;
	outline: 0;
	background: transparent;
	font: 16px/1.4 Arial, sans-serif;
	color: #202124;
}

form.google .submit {
	flex: none;
	padding: 8px 18px;
	border: 1px solid #f8f9fa;
	border-radius: 18px;
	background: #f8f9fa;
	color: #3c4043;
	font: 14px Arial, sans-serif;
	cursor: pointer;
}

form.google .submit:hover {
	border-color: #dadce0;
	box-shadow: 0 1px 1px rgba(0, 0, 0, .1);
}

form.google .options {
	position: relative;
	flex: none;
}

form.google .options summary {
	display: flex;
	align-items: center;
	justify-content: center;
	width: 40px;
	height: 40px;
	border-radius: 50%;
	color: #5f6368;
	cursor: pointer;
	list-style: none;
}

form.google .options summary::-webkit-details-marker {
	display: none;
}

form.google .options summary:hover {
	background: #f1f3f4;
}

form.google .options[open] summary {
	background: #e8f0fe;
	color: #1a73e8;
}

form.google .panel {
	position: absolute;
	top: 48px;
	right: 0;
	z-index: 20;
	width: 280px;
	max-width: calc(100vw - 40px);
	padding: 12px 14px;
	border: 1px solid #dadce0;
	border-radius: 8px;
	background: #fff;
	box-shadow: 0 4px 16px rgba(32, 33, 36, .2);
	font: 12px Arial, sans-serif;
	color: #5f6368;
}

form.google .option-row {
	display: flex;
	flex-wrap: wrap;
	align-items: center;
	gap: 12px;
	margin-top: 8px;
}

form.google .option-row:first-child {
	margin-top: 0;
}

form.google .option-title {
	font-weight: 500;
	color: #202124;
}

form.google label {
	display: inline-flex;
	align-items: center;
	gap: 4px;
}

form.google input[name=limit] {
	width: 64px;
}
</style>