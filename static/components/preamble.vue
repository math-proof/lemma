<template>
    <div class=preamble>
        <renderLean :text=lean :index="[index]"></renderLean>
    </div>
</template>

<script setup>
import Vue from "../js/vue.js";
import renderLean from "./renderLean.vue";

console.log('import preamble.vue');

const props = defineProps(['lean', 'index']);

const self = new Vue({
    props,

    data() {
        return {
            postname: 'preamble',
        };
    },

    computed: {
        renderLean() {
            return this.$parent.renderLean;
        },
    },

    methods: {
        click_left() {
        },
    },
});
</script>

<style>
div.preamble .cm-s-indent {
	margin-left: -0.2em;
}

div.preamble {
    margin-bottom: 1em;
}
</style>
