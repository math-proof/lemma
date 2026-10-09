<template>
    {{self.text}}
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownText.vue');

const props = defineProps({
    kwargs: Object,
});

const self = new Vue({
	props,

    data: {
    },

    computed: {
        text() {
            let {text} = props.kwargs;
            return text.replace(/\\_/g, '_');
        },
    },

    mounted() {
    },
});
</script>