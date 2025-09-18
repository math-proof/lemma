<template>
	<component :is=self.tagName>
		<component v-for="arg of self.children" :is=self.components[arg.func] v-bind=arg.bind />
	</component>
</template>

<script setup>
import Vue from "../js/vue.js"
import XMLParser from "../js/parser/xml.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = XMLParser;
components.push(...MarkdownParser.components);
// console.log('import XMLContainerTag.vue');
const props = defineProps({
	args : Array,
});

const self = new Vue({
	components,
	props,

    data: {
    },

    computed: {
		tagName() {
			return self.args[0].tagName.text;
		},
		children() {
			return self.args.slice(1, -1);
		},
    },

	directives: {
	},

	mounted() {
	},
});
</script>

<style>
think {
    /* Grey text */
    color: #666;
    /* Smaller font */
    font-size: 0.9em;
    /* Optional background */
    background: #f5f5f5;
    /* Optional spacing */
    padding: 8px;
    /* Optional rounded corners */
    border-radius: 4px;
    display: inline-block;
	/* display: block; */
    margin: 4px 0;
	position: relative; /* Needed for pseudo-element positioning */
}

think > p:first-child {
  margin-top: 0;
}

/* Create the horizontal rule effect */
think::after {
    content: ""; /* Required for pseudo-element */
    display: block;
	width: 100%; /* full width of the think block */
    height: 1px; /* Line thickness */
    background: #ccc; /* Line color */
    margin-top: 16px;
    margin-bottom: -16px; /* Compensate for bottom spacing */
}

</style>
