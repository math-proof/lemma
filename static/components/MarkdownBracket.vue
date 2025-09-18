<template>[<component :is=self.components[self.text.func] v-bind=self.text.bind />]</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownBracket.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
		text() {
			return self.args[0];
		},
    },

	directives: {
	}
});
</script>