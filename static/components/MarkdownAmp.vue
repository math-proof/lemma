<template>
    <span v-html=kwargs.text></span>
</template>

<script setup>
import Vue from "../js/vue.js"
// console.log('import MarkdownAmp.vue');

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