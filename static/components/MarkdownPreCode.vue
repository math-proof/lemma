<template>
	<div :title=self.title tabindex="8">
		<pre :class=self.className><code :class=self.className v-clipboard v-prism=self.arg.text @contextmenu.stop.prevent="contextmenu"></code></pre>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownPreCode.vue');

const props = defineProps({
	args : Array,
	kwargs : Object
});

const self = new Vue({
	components : ['MarkdownText'],
	props,

    data: {
    },

    computed: {
		title() {
			return `right click to copy the ${self.lang} code`;
		},

		lang() {
			return self.kwargs.lang;
		},

		arg() {
			return self.args[0];
		},

		className() {
			return 'language-' + self.lang;
		},
    },

	directives: {
		prism : {
			mounted(el, binding) {
				highlight(el, binding);
			},

			updated(el, binding) {
				if (binding.oldValue === binding.value)
					return;
				highlight(el, binding);
			},
		},
		clipboard
	},

	mounted() {
	}
});

function highlight(el, binding) {
	var {value : code} = binding;
	var {lang} = self;
	var setting;
	if (Prism.languages[lang]) {
		setting = Prism.languages[lang];
	}
	else {
		if (lang)
			console.warn(`Language ${lang} not supported by Prism.js`);
		setting = {
			keyword: /\b(if|else|function)\b/,
			string: /".*?"/,
		};
	}
	el.innerHTML = Prism.highlight(code, setting, lang);
}

var contextmenu = clipboard.contextmenu;
</script>