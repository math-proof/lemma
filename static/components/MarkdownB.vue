<template>
	<b>
		<component :is=self.components[self.arg.func] v-bind=self.arg.bind />
	</b>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownB.vue');

const props = defineProps({
	args : Array,
	kwargs : Object
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
		arg() {
			return self.args[0];
		}
    },

	directives: {
	}
});
</script>