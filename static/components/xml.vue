<template>
	<div>
		<XMLDocument :args=root.args />
	</div>
</template>

<script setup>
import Vue from "../js/vue.js"
import XMLDocument from "./XMLDocument.vue"
// console.log('import xml.vue');

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
