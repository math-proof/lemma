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

<script>
console.log('import hierarchyModule.vue');

import searchLink from "./searchLink.vue"

export default {
	components : {searchLink},
	
	props : ['module'],
	
	data() {
		return {
			backgroundColor: 'inherit',
			show: false,
			children: [],
		};
	},

	created() {
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
			/*get() {
				return 0;	
			},*/
			
			set(deep){
				if (deep){
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

		modules() {
			return this.$root.graph[this.module];
		},
	},
	
	methods: {
		click(event) {
			this.show = !this.show;
		},	
		
	},
};
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