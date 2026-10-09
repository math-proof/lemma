<template>
    {{ text }}
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
            // Prefer this.kwargs (Vue wrapper props); setup `props` can be
            // briefly incomplete for async markdown leaves, which left lemma
            // docstrings blank between `/--` and `-/`.
            const kwargs = this.kwargs || props.kwargs || {};
            const raw = kwargs.text;
            if (raw == null)
                return '';
            return String(raw).replace(/\\_/g, '_');
        },
    },

    mounted() {
    },
});

const { text } = self.globals;
</script>
