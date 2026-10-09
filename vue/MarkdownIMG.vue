<template>
	<img :src=self.src :alt=self.alt :title=self.title />
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownIMG.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
		src() {
			var href = self.args[1].toString();
			if (href.startsWith('http://') || href.startsWith('https://'))
				return href;
			return `http://${href}`;
		},
		alt() {
			return self.args[0].toString();
		},
		title() {
			return self.args[2]?.toString();
		},
    },

	directives: {
	}
});
</script>