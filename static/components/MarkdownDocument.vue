<template>
	<div :class=self.kwargs.class>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownDocument.vue');

const props = defineProps({
	args : Array,
	kwargs: Object,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
    },

	directives: {
	},

	mounted() {
	},
});
</script>
<style scoped>
div.think {
    /* Grey text */
    color: #666;
    /* Smaller font */
    font-size: 0.9em;
    /* Optional background */
    background: #f5f5f5;
    /* Optional spacing */
    padding: 8px;
    /* Optional rounded corners */
    border-radius: 4px;
    display: inline-block;
	/* display: block; */
    margin: 4px 0;
}

div.think > p:first-of-type {
  margin-top: 0;
}
</style>