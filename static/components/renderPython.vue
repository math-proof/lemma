<template>
    <textarea name=python[]>{{text}}</textarea>
</template>

<script setup>
import Vue from "../js/vue.js";
import { codeMirrorMounted, cmComputedUser, cmComputedModule } from "../js/codeMirrorEditor.js";

console.log('import renderPython.vue');

const props = defineProps(['text']);

const self = new Vue({
	props,

	data() {
		return {
			editor: null,
			theme: 'eclipse',
			focus: true,
			hash: null,
		};
	},

	created() {
		var hash = location.hash;
		if (hash) {
			this.hash = hash.slice(1);
		}
	},

	computed: {
		user: cmComputedUser,
		module: cmComputedModule,

		firstSibling() {
			return this;
		},
	},

	methods: {},

	mounted: codeMirrorMounted,
});
</script>

<style>
</style>
