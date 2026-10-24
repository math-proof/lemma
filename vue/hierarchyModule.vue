<template>
	<li :style=li_style>
   		<searchLink :data=data></searchLink>
   		<template v-if=modules>
   			<button class=transparent @click=click :title=buttonTitle>{{buttonText}}</button>
   		 	<ul v-if=show>
   	 			<hierarchyModule v-for="module, i of modules" :module=module :ref="el => children[i] = el"></hierarchyModule>
   			</ul>
		</template>
    </li>
</template>

<script setup>
import Vue from "../js/vue.js";
import searchLink from "./searchLink.vue";

console.log('import hierarchyModule.vue');

const props = defineProps(['module']);

const self = new Vue({
	props,

	data() {
		return {
			backgroundColor: 'inherit',
			show: false,
			children: [],
			isRepeat: false,
		};
	},

	created() {
		// $root is createApp Root (page JSON only). _hierarchySeen lives on
		// hierarchy.vue — walk $parent to reach it (nested modules skip siblings).
		var seen = null;
		for (var p = this.$parent; p; p = p.$parent) {
			if (p._hierarchySeen) {
				seen = p._hierarchySeen;
				break;
			}
		}
		if (!seen) {
			console.warn('hierarchyModule: _hierarchySeen missing; dedupe disabled');
			seen = new Set();
		}
		if (seen.has(this.module)) {
			this.isRepeat = true;
			return;
		}
		seen.add(this.module);

		var root = this.$root;
		if (root.deep){
			this.show = true;
		}
		else if (root.traceback){
			if (this.module == root.traceback.back()){
				this.show = false;
				this.backgroundColor = 'yellow';
			}
			else {
				if (this.module == root.traceback[this.depth]){
					this.show = true;
				}
			}
		}
	},

	computed: {
		keyInput() {
			return this.$parent.keyInput;
		},

		data() {
			var data = {module: this.module};
			if (this.keyInput == 'callee' && !this.$parent.graph) {
				var {module} = this.$parent;
				data.line = module.slice(module.indexOf('.') + 1);
			}
			data.target = '';
			return data;
		},

		deep: {
			get() {
				return this.show;
			},
			set(deep){
				if (deep && !this.isRepeat){
					this.show = true;
					this.$nextTick(()=>{
						for (var child of this.children){
							child.deep = true;
						}
					})
				}
			},
		},

		li_style() {
			return `background-color:${this.backgroundColor}`;
		},

		depth() {
			var depth = -1;
			var root = this.$root;
			var parent = this.$parent;
			for (;;){
				if (parent === root)
					break;

				++depth;
				parent = parent.$parent;
			}

			return depth;
		},

		buttonText() {
			return this.show? '«««' : '»»»';
		},

		buttonTitle() {
			return this.show? 'click to collapse' : 'click to expand';
		},

		// Repeats keep a »»» button (not plain text) so the user can expand in place;
		// children still dedupe via _hierarchySeen when they mount.
		modules() {
			var kids = this.$root.graph && this.$root.graph[this.module];
			return kids && kids.length ? kids : null;
		},
	},

	methods: {
		click(event) {
			this.show = !this.show;
		},
	},
});

const { li_style, data, modules, show, children, buttonTitle, buttonText, click } = self.globals;
</script>

<style scoped>

button.transparent:hover{
	background-color: red;
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
}

ul li {
	margin-top: 0.5em;
}

</style>
