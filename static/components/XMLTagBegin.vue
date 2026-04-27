<template>
	<component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
</template>

<script setup>
import Vue from "../js/vue.js"
import XMLParser from "../js/parser/xml.js"
const {components} = XMLParser;
// console.log('import XMLTagBegin.vue');

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
	},

	mounted() {
	},
});
</script>