<template>
	<component :is=self.headerType>
		<component :is=self.components[self.header.func] v-bind=self.header.bind />
		<buttonExpand :ref=self.$refs.buttonExpand :initial_show=true></buttonExpand>
	</component>
	<template v-if=self.buttonExpand?.show v-for="arg of self.hanging">
		<component :is=self.components[arg.func] v-bind=arg.bind />
	</template>
</template>

<script setup>
import Vue from "../js/vue.js"
import MarkdownParser from "../js/parser/markdown.js"
const {components} = MarkdownParser;
import buttonExpand from "./buttonExpand.vue"
// console.log('import MarkdownH.vue');

const props = defineProps({
	args: Array,
	kwargs: Object,
});

const self = new Vue({
	components,
	props,

	refs: {
		buttonExpand: null,
	},

    data: {
    },

    computed: {
		headerType() {
			var {level} = self.kwargs;
			return 'h' + level;
		},

		header() {
			return self.args[0];
		},

		hanging() {
			return self.args.slice(1);
		},
    },

	mounted() {
	}
});
</script>