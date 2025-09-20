<template>
	<a v-if="mode == 'a'" v-focus tabindex=2 :href=href @contextmenu.prevent=contextmenu @keydown=keydown_a target="module">
        {{module.isArray? module[1]: module}}
       	<searchContextmenu v-if='showContextmenu' :left=left :top=top></searchContextmenu>
    </a>
	<span v-else-if="mode == 'span'">
       	{{module}}
    </span>
    <input v-else v-focus spellcheck=false :size='module.length + 1' :value=module @blur=blur @keydown=keydown>
    
</template>

<script>
console.log('import searchLink.vue');
import searchContextmenu from "./searchContextmenu.vue"

var focusedAlready = false;
export default {
	components: {searchContextmenu},
	
	data(){
		return {
			mode: 'a',
			showContextmenu: false,
			left: -1,
			top: -1,
		};
	},
	
	props: ['module'],
	
	computed: {
		user(){
			return axiom_user();
		},
		
		href(){
			var {module} = this;
			if (module.isArray)
				module = module[0];
			return `/${this.user}/?module=${module}`;
		},			
	},
	
	methods: {
		async delete_folder(error_msg){
			while (error_msg){
				console.log('error_msg = ', error_msg);				
				var m = error_msg.matchAll(/rmdir\((\S+)\)/g);
				error_msg = '';
				for (var m of m){
					var folder = m[1];
					var names = folder.split(/[\/\\]/);
					var index = names.indexOf('Lemma');
					names = names.slice(index + 1);
					var section = names.pop();
					var parentFolder = names.join('.');
				}
			}
		},
		
		async set_module(module){
			var undeletables = '';
			if (this.module != module){
				console.log('oldText = ' + this.module);
				console.log('newText = ' + module);
				var $new = module.replace(/\//g, '.')
				$new = $new.replace(/\bis\b/, 'Is');
				undeletables = await form_post(`php/request/rename.php`, {old: this.module.replace(/\//g, '.'), new: $new});
				console.log('undeletables = ' + undeletables);
				
				var modules = this.$root.list;
				if (!modules){
					console.assert(this.module == this.$root.module, "this.module == this.$root.module");
					this.$root.graph[module] = this.$root.graph[this.module];
					delete this.$root.graph[this.module];
					this.$root.module = module;
				}
				else{
					modules[modules.indexOf(this.module)] = module;	
				}
			}

			this.mode = 'a';
			return undeletables;
		},
		
		contextmenu(event) {
			//console.log("contextmenu: function(event)");
			var self = event.target;				
			
			this.left = event.x + self.getScrollLeft();
			this.top = event.y + self.getScrollTop();
			
			this.showContextmenu = true;
			
			setTimeout(()=>{
				var contextmenu = self.lastElementChild;
				contextmenu.focus();				
			}, 100);				
		},
		
		blur(event){
			if (this.mode == 'F3'){
				this.mode = 'input';
			}
			else{
				this.mode = 'span';
				focusedAlready = false;
				this.$nextTick(async ()=>{
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
				find_and_jump(event);
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
				var {list} = self;
				if (list) {
					var index = list.indexOf(this.module);
					list.delete(index);
					if (list.length)
						self.$nextTick(()=>{
							self.searchLink[index % list.length].focus();
						});
				}
				break;
			}				
		},

		async replace() {
			var [old, $new] = this.module;
			var undeletables = '';
			if (old != $new){
				console.log('oldText = ' + old);
				console.log('newText = ' + $new);
				$new = $new.replace(/\bis\b/, 'Is');
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
		    // after dom is inserted into the document
		    mounted(el, binding) {
		    	if (!focusedAlready || el.tagName == 'input'){
		    		el.focus();
		    		focusedAlready = true;
		    	}
		    },

		    updated(el, binding){
		    	el.focus();
		    }
		},
	},
}
</script>

<style scoped>
</style>