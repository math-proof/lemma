<template>
	<li>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</li>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownLI.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
    },

	directives: {
	}
});


</script>