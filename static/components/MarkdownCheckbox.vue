<template>
    <input type=checkbox disabled :value=self.checked />
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownCheckbox.vue');
const props = defineProps({
	kwargs : Object
});

const self = new Vue({
    props, 
    computed: {
		checked() {
			return self.kwargs.checked;
		}
    },
});
</script>