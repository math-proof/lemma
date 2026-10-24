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

const props = defineProps(['module', 'graph', 'traceback', 'keyInput', 'deep']);

const self = new Vue({
	props,

	data() {
		return {
			// Shared across all hierarchyModule nodes (via $parent walk); first mention can
			// auto-expand; later mentions start collapsed but »»» still expands in place;
			// leaf dups stay plain link.
			_hierarchySeen: new Set(),
		};
	},

	$refs: {
		hierarchyModule: null,
	},

	computed: {
		deep() {
			// Prefer createApp prop (PHP $_GET['deep'] / Node query.deep).
			var p = this.$props && this.$props.deep;
			if (p === true || p === 1 || p === '1' || p === 'true')
				return true;
			// Query string (same shape links emit: &deep=1).
			var q = new URLSearchParams(location.search).get('deep');
			if (q === '1' || q === 'true')
				return true;
			// Transitional fallback for old #deep bookmarks.
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
