<template>
	<ul>
		<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
	</ul>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownUL.vue');

const props = defineProps({
	args : Array,
});

const self = new Vue({
	components : [
		'MarkdownLI'
	],
	props,

    data: {
    },

    computed: {
    },

	directives: {
	}
});
</script>