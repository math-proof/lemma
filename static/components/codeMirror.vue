<template>
    <textarea :ref="$refs.textarea" :name=name placeholder="">{{text}}</textarea>
</template>

<script setup>
import Vue from "../js/vue.js";
import { codeMirrorMounted, cmComputedUser, cmComputedModule } from "../js/codeMirrorEditor.js";

console.log('import codeMirror.vue');

const props = defineProps(['text', 'name', 'style', 'index', 'theme', 'focus', 'lineNumbers', 'styleActiveLine', 'breakpoint']);

const self = new Vue({
	$refs: {
		textarea: null,
	},

	data() {
		return {
			editor: null,
		};
	},

	props,

	created() {
		var codeMirror = this.$parent.codeMirror;
		if (codeMirror)
			codeMirror[this.index] = this;
	},

	computed: {
		rows() {
			console.log('rows = ', this.text.length);
			return this.text.length;
		},

		cols() {
			console.log('cols = ', Math.max(...this.text.map(text => text.length)));
			return Math.max(...this.text.map(text => text.length));
		},

		breakpointArray() {
			var array = [];
			for (let line = 0; line < this.breakpoint.length; ++line) {
				if (this.breakpoint[line]) {
					array.push(line);
				}
			}
			return array;
		},

		lastSibling() {
			return this;
		},

		firstSibling() {
			return this;
		},

		user: cmComputedUser,

		module: cmComputedModule,

		hash() {
			var hash = location.hash;
			if (hash) {
				return hash.slice(1);
			}
		},
	},

	methods: {
		resume() {
			this.$parent.resume();
		},

		save() {
			this.$parent.save();
		},

		debug() {
			this.$parent.debug();
		},

		set_breakpoint(index) {
			this.$parent.set_breakpoint(index);
		},

		clear_breakpoint(index) {
			this.$parent.clear_breakpoint(index);
		},

		showBreakPoint() {
			if (!this.breakpoint)
				return;

			for (let line of this.breakpointArray) {
				this.editor.addLineClass(line, "gutter", "breakpoint");
			}
		},

		showExecutionPoint(previousPoint, currentPoint) {
			this.editor.setCursor(currentPoint, 4);
			this.editor.addLineClass(currentPoint, "class", "executionPoint");

			if (previousPoint >= 0)
				this.editor.removeLineClass(previousPoint, "class", "executionPoint");
		},
	},

	mounted: codeMirrorMounted,
});
</script>

<style>
.CodeMirror {
    /*overflow-y: visible; */
    height: auto !important;
    width: auto !important;
}

.CodeMirror-scroll {
	/* Set scrolling behaviour here */
	overflow: auto;
	max-height: 2000px;
}

.CodeMirror-focused .CodeMirror-selected {
	background: rgb(0, 120, 215);
}

.executionPoint > pre > span {
	background-color: #5a5;
}

</style>
