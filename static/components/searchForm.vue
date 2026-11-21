<template>
	<form name=search enctype="multipart/form-data" method=post :action=action @keydown=keydown>
		<input v-focus tabindex=1 type=text spellcheck=false name=keyword size=48 :value=keyword placeholder='input a hint in search of a formula/theorem/axiom' @input=input>
		<br>
		<template v-if="replacement != null" >
			<input v-focus tabindex=1 name=replacement :value=replacement placeholder='input the replacement word' @input=input />
			Replace <button tabindex=1 type=button @click=replace>One</button>/<button tabindex=1 type=button @click=replaceAll>All</button>
			<br>
		</template>

		<input tabindex=-1 type=checkbox name=caseSensitive :checked=caseSensitive><u>C</u>ase
			
		<input tabindex=-1 type=checkbox name=wholeWord :checked=wholeWord><u>W</u>holeWord
		
		<input tabindex=-1 type=checkbox name=regularExpression :checked=regularExpression>Rege<u>x</u>
		
		<input tabindex=-1 type=checkbox name=latex :checked=latex><u>L</u>aTex<br>
		limit: <input tabindex=1 name=limit :value=limit placeholder='100' @input=input /> offset: <input tabindex=1 name=offset :value=offset placeholder='0' @input=input />
		<input id=submit_query type=submit value=query style="display: none;" />
	</form>
</template>

<script>
console.log('import searchForm.vue');
export default {
	props : ['keyword', 'caseSensitive', 'wholeWord', 'regularExpression', 'latex', 'replacement', 'limit', 'offset'],

	computed: {
		user(){
			return axiom_user();	
		}, 
		
		action(){
			return `/${this.user}/index.php`;
		},
	},
	
	methods: {
		input(event){
			setAttribute(this, event.target.name, event.target.value);
		},
		
		keydown(event){
			if (event.altKey){
				switch(event.key){
				case 'c':
					setAttribute(this, 'caseSensitive', !this.caseSensitive);
					break;
				case 'w':
					setAttribute(this, 'wholeWord', !this.wholeWord);
					break;
				case 'x':
					setAttribute(this, 'regularExpression', !this.regularExpression);
					break;
				case 'l':
					setAttribute(this, 'latex', !this.latex);
					break;
				}
			}
		},

		replace(event) {
			this.$parent.replace(event);
			event.preventDefault();
		},

		replaceAll(event) {
			this.$parent.replaceAll(event);
			event.preventDefault();
		},
	},	
	
	directives: {
		focus: {
		    // after dom is inserted into the document
		    mounted(el, binding) {
				el.focus();
		    },
		},
	},
};
</script>

<style scoped>
form[name=search] {
	float: right;
}
</style>