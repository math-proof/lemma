<template>
	<a :href=self.href>
		<component :is=self.components[self.text.func] v-bind=self.text.bind />
	</a>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownA.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
		href() {
			var href = self.args[1].toString();
			if (href.startsWith('http://') || href.startsWith('https://')) {
				return href;
			}
			return `http://${href}`;
		},

		text() {
			return self.args[0];
		},
    },

	directives: {
	}
});
</script>