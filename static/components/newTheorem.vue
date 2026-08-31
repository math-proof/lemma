<template>
	module :
	<newInput :ref="$refs.newInput" :module=module></newInput>
	<render :ref="$refs.render" :imports=imports :open=open :lemma=lemma :error=error :module=module :date=date></render>
</template>

<script setup>
import Vue from "../js/vue.js";
import render from "./render.vue";
import newInput from "./newInput.vue";

console.log('import newTheorem.vue');

const props = defineProps(['name', 'imports', 'open', 'lemma', 'error', 'date']);

const self = new Vue({
	props,

	$refs: {
		newInput: null,
		render: null,
	},

	data() {
		var module = this.name;
		var module = module.replace(/[/\\]/g, '.');
		return {
			module
		};
	},

	computed: {
		renderLean() {
			var proof = [];
			proof.push(this.$refs.proof);
			return proof;
		},

		user() {
			return axiom_user();
		},

		action() {
			var module = this.module.replace(/\./g, '/');
			return `/${this.user}/?module=${module}`;
		},
	},

	methods: {
		async save() {
			var {module} = this;
			var sql = `
select * from lemma where module = "${module}";
`
			var lemma = await form_post('php/request/execute.php', {sql});
			if (lemma.length)
				alert(`Lemma ${module} already exists!`);
			else
				form.submit();
		},

		update_action() {
			this.render.action = this.action;
		},
	},

	mounted() {
		this.update_action();
	},
});

const { $refs, module } = self.globals;
</script>

<style>
</style>
