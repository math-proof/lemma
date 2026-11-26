<template>
	<template v-if="mode == 'a'">
		<a v-focus v-clipboard tabindex=2 class="result-title" :data-clipboard-text=module :href=href @keydown=keydown_a :target="data.target?? '_blank'">
			{{data.replacement ?? data.text?? module}}
		</a>
		<div v-if="data.snippet" class="snippet">{{data.snippet}}</div>
		<div v-if="data.latex" class="formula" v-katex="data.latex"></div>
		<div v-if="data.match" class="meta">
			<span v-if="data.lemmaName" class="lemma">{{data.lemmaName}}</span>
			{{data.lemmaName ? ' · ' : ''}}<span v-if="data.section" class="section">{{data.section}}</span>
			{{(data.lemmaName || data.section) ? ' · ' : ''}}{{data.match}} match
		</div>
	</template>
	<span v-else-if="mode == 'span'">
       	{{module}}
    </span>
    <input v-else v-focus spellcheck=false :size='module.length + 1' :value=module @blur=blur @keydown=keydown>
    
</template>

<script setup>
import Vue from "../js/vue.js";

console.log('import searchLink.vue');

// KaTeX is a deferred classic script; retry briefly until it is available.
function renderLatex(el, latex, attempt = 0) {
	if (!latex) {
		el.textContent = '';
		return;
	}
	if (typeof window.katex === 'undefined') {
		if (attempt < 100)
			setTimeout(() => renderLatex(el, latex, attempt + 1), 50);
		return;
	}
	try {
		window.katex.render(String(latex), el, {
			displayMode: false,
			throwOnError: false,
			trust: true,
			strict: false,
		});
	} catch {
		el.textContent = String(latex);
	}
}

// script setup re-runs per instance; keep one gate so only the first <a> auto-focuses.
const focusGate = Vue.searchLinkFocus ??= { already: false };

const props = defineProps(['data']);

const self = new Vue({
	props,

	data() {
		return {
			mode: 'a',
		};
	},

	computed: {
		module() {
			return this.data.module;
		},

		user() {
			return axiom_user();
		},

		href() {
			var {line, module, section, lemmaId, latexId} = this.data;
			var href = `?module=${module}`;
			if (section && lemmaId != null && latexId != null)
				href += `#${lemmaId}:${section}:${latexId}`;
			else if (line)
				href += `#${line}`;
			return href;
		},
	},

	methods: {
		async delete_folder(error_msg) {
			if (typeof error_msg !== 'string' || !/rmdir\s*\(/i.test(error_msg)) return;
			while (error_msg) {
				console.log('error_msg = ', error_msg);
				var m = error_msg.matchAll(/rmdir\((\S+)\)/g);
				error_msg = '';
				for (var m of m){
					var folder = m[1];
					var names = folder.split(/[\/\\]/);
					var index = names.indexOf('Lemma');
					names = names.slice(index + 1);
				}
			}
		},

		async set_module(module){
			var undeletables = '';
			if (this.module != module){
				console.log('oldText = ' + this.module);
				console.log('newText = ' + module);

				undeletables = await form_post(`request/rename`, { old: this.module.replace(/\//g, '.'), new: module.replace(/\//g, '.')});
				console.log('undeletables = ' + undeletables);

				var modules = this.$root.data;
				if (!modules){
					console.assert(this.module == this.$root.module, "this.module == this.$root.module");
					this.$root.graph[module] = this.$root.graph[this.module];
					delete this.$root.graph[this.module];
					this.$root.module = module;
				}
				else
					modules[modules.findIndex(arg => arg.module == this.module)].module = module;
			}

			this.mode = 'a';
			return undeletables;
		},

		blur(event){
			if (this.mode == 'F3'){
				this.mode = 'input';
			}
			else{
				this.mode = 'span';
				focusGate.already = false;
				this.$nextTick(async () => {
					var undeletables = await this.set_module(event.target.value);
					console.log("undeletable files = ", undeletables);

					this.delete_folder(undeletables);
				});
			}
		},

		async keydown(event){
			switch(event.key){
			case 'Enter':
				var undeletables = await this.set_module(event.target.value);
				console.log("undeletable files = ", undeletables);
				this.delete_folder(undeletables);

				break;
			case 'F3':
				console.log("F3 is pressed");
				this.mode = 'F3';
				find_and_jump(event, await form_post('request/sections'));
				break;
			}
		},

		keydown_a(event){
			switch(event.key) {
			case 'F2':
				this.mode = 'input';
				focusGate.already = false;
				break;
			case 'Delete':
				var self = this.$parent;
				var {data} = self;
				if (data) {
					var index = data.indexOf(this.module);
					data.delete(index);
					if (data.length)
						self.$nextTick(()=>{
							self.searchLink[index % data.length].focus();
						});
				}
				break;
			}
		},

		async replace() {
			var old = this.module;
			var $new = this.data.replacement;
			var undeletables = '';
			if (old != $new){
				console.log('oldText = ' + old);
				console.log('newText = ' + $new);

				undeletables = await form_post(`request/rename`, { old, new: $new});
				console.log('undeletables = ' + undeletables);
				this.delete_folder(undeletables);
				await sleep(0.5);
			}
		},

		focus() {
			this.$el.focus();
		},
	},

	directives: {
		katex: {
			mounted(el, binding) {
				renderLatex(el, binding.value);
			},
			updated(el, binding) {
				renderLatex(el, binding.value);
			},
		},

		focus: {
			mounted(el) {
				if (!focusGate.already || el.tagName.toLowerCase() == 'input') {
					el.focus();
					focusGate.already = true;
				}
			},

			updated(el) {
				if (el.tagName.toLowerCase() == 'input')
					el.focus();
			}
		},

		clipboard,
	},
});

const { mode, module, href, keydown_a, blur, keydown } = self.globals;
</script>

<style scoped>
.result-title {
	display: inline-block;
	font: 20px/1.3 Arial, sans-serif;
	color: #1a0dab;
	text-decoration: none;
}

.result-title:hover {
	text-decoration: underline;
}

.snippet {
	margin-top: 4px;
	font: 14px/1.4 Arial, sans-serif;
	color: #4d5156;
}

.formula {
	display: block;
	box-sizing: border-box;
	width: 100%;
	max-width: 100%;
	min-width: 0;
	margin-top: 6px;
	font-size: 16px;
	line-height: 1.6;
	color: #202124;
	overflow-x: auto;
	overflow-y: hidden;
}

.formula :deep(.katex) {
	white-space: nowrap;
}

.formula :deep(.lean-hit) {
	background: #fff3b0;
	border-radius: 3px;
}

.meta {
	margin-top: 4px;
	font: 12px Arial, sans-serif;
	color: #70757a;
}

.meta .lemma {
	display: inline-block;
	padding: 0 6px;
	margin-right: 2px;
	border-radius: 8px;
	background: #fce8e6;
	color: #c5221f;
	font-weight: 600;
}

.meta .section {
	display: inline-block;
	padding: 0 6px;
	margin-right: 2px;
	border-radius: 8px;
	background: #e8f0fe;
	color: #1a73e8;
	font-weight: 600;
}
</style>