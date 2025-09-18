<template>
	<div>
		<MarkdownDocument v-bind=root.bind />
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownDocument from "./MarkdownDocument.vue"
// console.log('import markdown.vue');

const props = defineProps({
	root : Object,
});

const self = new Vue({
	props,

    data: {
    },

	computed : {
	},

	directives: {
	},

	mounted() {
	}
});

</script>
