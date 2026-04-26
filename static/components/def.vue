<template>
    <div class=def>
        <renderLean :text=lean :index="[index]"></renderLean>
    </div>
</template>

<script setup>
import Vue from "../js/vue.js";
import renderLean from "./renderLean.vue";

console.log('import def.vue');

const props = defineProps(['lean', 'index']);

const self = new Vue({
    props,

    data() {
        return {
            postname: 'def',
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

defineExpose(self.$expose);
</script>

<style>
div.def .cm-s-indent {
	margin-left: -0.2em;
}

div.def {
    margin-bottom: 1em;
}
</style>