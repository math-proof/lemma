<template>
	<button type=button class=transparent @click=self.click :title="self.show? 'click to collapse' : 'click to expand'">{{self.buttonText}}<br></button>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import buttonExpand.vue');

const props = defineProps(['initial_show', 'callback']);

const self = new Vue({
	props,

	data() {
		return {
			show: this.initial_show,
		};
	},

	computed: {
		buttonText() {
			return this.show? '«««' : '»»»';
		},
	},

	methods: {
		click() {
			this.show = !this.show;

			if (this.callback)
				this.callback();
		},
	},
});
</script>

<style>

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

button.transparent:hover{
	background-color: red;
}

</style>
