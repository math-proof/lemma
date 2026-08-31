<template>
	<a v-if="mode == 'a'" v-focus v-clipboard tabindex=2 :data-clipboard-text=module :href=href @keydown=keydown_a :target="data.target?? '_blank'">
        {{data.replacement ?? data.text?? module}}
    </a>
	<span v-else-if="mode == 'span'">
       	{{module}}
    </span>
    <input v-else v-focus spellcheck=false :size='module.length + 1' :value=module @blur=blur @keydown=keydown>
    
</template>

<script setup>
import Vue from "../js/vue.js";

console.log('import searchLink.vue');

var focusedAlready = false;

const props = defineProps(['data']);

const self = new Vue({
	props,

	data() {
		return {
			mode: 'a',
		};
	},

	computed: {
		module() {
			return this.data.module;
		},

		user() {
			return axiom_user();
		},

		href() {
			var {line, module} = this.data;
			var href = `?module=${module}`;
			if (line)
				href += `#${line}`;
			return href;
		},
	},

	methods: {
		async delete_folder(error_msg) {
			if (typeof error_msg !== 'string' || !/rmdir\s*\(/i.test(error_msg)) return;
			while (error_msg) {
				console.log('error_msg = ', error_msg);
				var m = error_msg.matchAll(/rmdir\((\S+)\)/g);
				error_msg = '';
				for (var m of m){
					var folder = m[1];
					var names = folder.split(/[\/\\]/);
					var index = names.indexOf('Lemma');
					names = names.slice(index + 1);
				}
			}
		},

		async set_module(module){
			var undeletables = '';
			if (this.module != module){
				console.log('oldText = ' + this.module);
				console.log('newText = ' + module);

				undeletables = await form_post(`php/request/rename.php`, { old: this.module.replace(/\//g, '.'), new: module.replace(/\//g, '.')});
				console.log('undeletables = ' + undeletables);

				var modules = this.$root.data;
				if (!modules){
					console.assert(this.module == this.$root.module, "this.module == this.$root.module");
					this.$root.graph[module] = this.$root.graph[this.module];
					delete this.$root.graph[this.module];
					this.$root.module = module;
				}
				else
					modules[modules.findIndex(arg => arg.module == this.module)].module = module;
			}

			this.mode = 'a';
			return undeletables;
		},

		blur(event){
			if (this.mode == 'F3'){
				this.mode = 'input';
			}
			else{
				this.mode = 'span';
				focusedAlready = false;
				this.$nextTick(async () => {
					var undeletables = await this.set_module(event.target.value);
					console.log("undeletable files = ", undeletables);

					this.delete_folder(undeletables);
				});
			}
		},

		async keydown(event){
			switch(event.key){
			case 'Enter':
				var undeletables = await this.set_module(event.target.value);
				console.log("undeletable files = ", undeletables);
				this.delete_folder(undeletables);

				break;
			case 'F3':
				console.log("F3 is pressed");
				this.mode = 'F3';
				find_and_jump(event, await form_post('php/request/sections.php'));
				break;
			}
		},

		keydown_a(event){
			switch(event.key) {
			case 'F2':
				this.mode = 'input';
				focusedAlready = false;
				break;
			case 'Delete':
				var self = this.$parent;
				var {data} = self;
				if (data) {
					var index = data.indexOf(this.module);
					data.delete(index);
					if (data.length)
						self.$nextTick(()=>{
							self.searchLink[index % data.length].focus();
						});
				}
				break;
			}
		},

		async replace() {
			var old = this.module;
			var $new = this.data.replacement;
			var undeletables = '';
			if (old != $new){
				console.log('oldText = ' + old);
				console.log('newText = ' + $new);

				undeletables = await form_post(`php/request/rename.php`, { old, new: $new});
				console.log('undeletables = ' + undeletables);
				this.delete_folder(undeletables);
				await sleep(0.5);
			}
		},

		focus() {
			this.$el.focus();
		},
	},

	directives: {
		focus: {
			mounted(el) {
				if (!focusedAlready || el.tagName == 'input'){
					el.focus();
					focusedAlready = true;
				}
			},

			updated(el){
				el.focus();
			}
		},

		clipboard,
	},
});

const { mode, module, href, keydown_a, blur, keydown } = self.globals;
</script>

<style scoped>
</style>