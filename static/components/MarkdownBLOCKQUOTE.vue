<template>
    <blockquote>
        <component v-for="arg of self.args" :is=self.components[arg.func] v-bind=arg.bind />
    </blockquote>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
// console.log('import MarkdownBLOCKQUOTE.vue');

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
<style scoped>
/* Core Blockquote Styling */
blockquote {
    background-color: #ffffff; /* optional subtle background */
    border-left: 4px solid #e5e5e5; /* Light gray left border */
    padding: 12px 20px;             /* Vertical and horizontal padding */
    margin: 16px 0;                 /* Top/bottom margin */
    border-radius: 0 4px 4px 0;    /* Rounded corners on the right side */
}

blockquote:hover {
    background-color: #f6f6f6;
    border-left-color: #68a;
}

/* Optional: Inherit standard text styles */
blockquote p {
    margin: 0;          /* Remove default paragraph margins */
}
</style>