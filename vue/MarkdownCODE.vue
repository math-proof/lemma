<template>
	<code>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</code>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownCODE.vue');

const props = defineProps({
	args: Array,
	kwargs: Object
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
    },

	mounted() {
	}
});
</script>
<style scoped>
code {
    color: #c00;               /* Dark red color */
    background: #f8f8f8;       /* Light gray background */
    padding: 0.2em 0.4em;       /* Vertical and horizontal padding */
    font-family: monospace;     /* Monospace font for code */
    border-radius: 3px;         /* Slightly rounded corners */
	font-size: 0.9em;           /* Slightly smaller font size */
	background: #fff0f0; /* Light red background */
}
</style>
