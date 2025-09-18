<template>
    <template v-for="arg, i of self.args">
        <component :is=self.components[arg.func] v-bind=arg.bind />
        <template v-if="i < self.args.length - 1">|</template>
    </template>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownArgsBarSeparated.vue');

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
    },

    mounted() {
    },
});
</script>