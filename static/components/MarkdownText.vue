<template>
    {{kwargs.text}}
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
    },

    mounted() {
    },
});
</script>