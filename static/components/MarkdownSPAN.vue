<template>
    <span>
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </span>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownSPAN.vue');

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