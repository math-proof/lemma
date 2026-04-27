<template>
    <th :style=self.style>
        <component :is=self.components[self.arg.func] v-bind=self.arg.bind />
    </th>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownTH.vue');

const props = defineProps({
	args: Array,
    kwargs: Object,
});

const self = new Vue({
    components,
	props,

    data: {
    },

    computed: {
        arg() {
            return self.args[0];
        },

        style() {
            var textAlign = self.kwargs.textAlign?? 'center';
            return `text-align : ${textAlign}`;
        },
    },

	mounted() {
	},
});
</script>