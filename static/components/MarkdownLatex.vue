<template>
	<span v-if=self.block v-latex.block=self.arg.text></span>
	<span v-else v-latex.inline=self.arg.text></span>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownLatex.vue');
const latex = {
	// usage:
	// block latex:
	// <p v-latex>{{ "'\\[' + latex + '\\]'" }}</p>
	// <p v-latex="'\\[' + latex + '\\]'"></p>
	// <p v-latex.block="latex"></p>

	// inline latex:
	// <p v-latex>{{ "'\\(' + latex + '\\)'" }}</p>
	// <p v-latex="'\\(' + latex + '\\)'"></p>
	// <p v-latex.inline="latex"></p>
	mounted(el, binding) {
		var {value : latex} = binding;
		if (latex) {
			var {block, inline} = binding.modifiers;
			var displayMode = null;
			if (block)
				displayMode = true;
			else if (inline)
				displayMode = false;
			if (displayMode === null) {
				var {displayMode, latex} = getDisplayMode(latex);
				if (displayMode === null)
					return;
			}
			katex.render(latex, el, {
				displayMode,
				throwOnError: false,
				errorColor: "#ff0000"
			});
		}
		else {
			renderMathInElement(el, {
				delimiters: [
					{ left: "$$", right: "$$", display: true },
					{ left: "\\[", right: "\\]", display: true },
					{ left: "$", right: "$", display: false },
					{ left: "\\(", right: "\\)", display: false }
				],
				throwOnError: false,
				errorColor: "#ff0000"
			});
		}
	},
};

latex.updated = function(el, binding) {
	if (binding.oldValue === binding.value)
		return;
	latex.mounted(el, binding);
}

const props = defineProps({
	args : Array,
	kwargs : Object
});

const self = new Vue({
	props,

    data: {
    },

    computed: {
		block() {
			return ['\\[', '$$'].includes(self.kwargs.block[0]);
		},
		arg() {
			return self.args[0];
		},
    },

	directives: {
		latex
	}
});
</script>