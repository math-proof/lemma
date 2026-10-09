<template>
	<ol :start=self.start>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</ol>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownOL.vue');

const props = defineProps({
	args : Array,
	kwargs : Object,
});

const self = new Vue({
	components : [
		'MarkdownLI'
	],
	props,

    data: {
    },

    computed: {
		start() {
			return props.kwargs.start;
		}
    },

	directives: {
	}
});
</script>