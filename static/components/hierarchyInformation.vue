<template>
	<div>
		the lemma in question is a
		<a :href="'?' + keyInput + '=' + self.$parent.module + (deep ? '#deep': '')" :title="'show ' + (deep?'deep':'only first-layer') + ' hierarchy'">{{keyInput}}</a>
		in the following hierarchy, would you switch to
		<a :href=href>{{key}}</a> hierarchy?	
	</div>
</template>

<script setup>
import Vue from "../js/vue.js";

console.log('import hierarchyInformation.vue');

const props = defineProps(['keyInput', 'deep']);

const self = new Vue({
	props,

	computed:{
		key() {
			return this.keyInput == 'callee'? 'caller': 'callee';
		},

		href() {
			return '?' + this.key + '=' + this.$parent.module;
		},
	},
});

const { key, href } = self.globals;
</script>

<style>
</style>