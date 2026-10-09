<template>
	<div>
		<hierarchyInformation :key-input=keyInput :deep=!deep></hierarchyInformation>
		<br>
		<hierarchyModule :ref="$refs.hierarchyModule" :module=module></hierarchyModule>
	</div>
</template>

<script setup>
import Vue from "../js/vue.js";
import hierarchyInformation from "./hierarchyInformation.vue";
import hierarchyModule from "./hierarchyModule.vue";

console.log('import hierarchy.vue');

const props = defineProps(['module', 'graph', 'traceback', 'keyInput']);

const self = new Vue({
	props,

	$refs: {
		hierarchyModule: null,
	},

	computed: {
		deep() {
			var hash = location.hash;
			if (hash){
				hash = hash.slice(1);
				if (hash == 'deep')
					return true;
			}
			return false;
		},
	},

	mounted() {
		var hierarchyModule = this.hierarchyModule;
		if (this.deep){
			hierarchyModule.deep = true;
		}
		else{
			hierarchyModule.show = true;
		}
	},
});

const { $refs, deep } = self.globals;
</script>

<style>
</style>