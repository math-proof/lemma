<template>
	<div>
		<select v-if=phrases v-focus name=suggest class='non-arrowed' :style=select_style :size=select_size @keydown=keydown_select @blur=blur>
			<option v-for="phrase in phrases" :value=phrase>{{phrase}}</option>
		</select>
		<input v-focus spellcheck=false ref=input name=module v-model=module :size=input_size @keydown=keydown @change=change >
	</div>
</template>

<script>
function getTextWidth(str) {
	let result = 0;
	let div = document.createElement("div");
	div.setAttribute('class', "Consolas");
	div.style.backgroundColor = 'inherit';
	div.style.borderStyle = 'none';
	div.style.outline = 'none';

	div.style.opacity = 0;
	div.style.position = "absolute";
	div.style.whiteSpace = "nowrap";

	div.innerText = str;
	document.body.append(div);
	result = div.getBoundingClientRect().width;
	div.remove();
	return result;
}

console.log('import newInput.vue');
export default {
	props : [],
	
	created() {
	},
	
	updated() {
	},
	
	data() {
		return {
			phrases: null,
			start: -1,
		};
	},
	
	computed: {
		module: {
			get() {
				return this.$parent.module;
			},
			set(module){
				var self = this.$parent;
				self.module = module;
				self.update_action();
			},
		},

		input_size() {
			return this.module.length;
		},
		
		select_size() {
			return Math.min(this.phrases.length, 10);
		},
		
		char_width() {
			return getTextWidth("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") / 52;	
		},
		
		select_style() {
			var offset = this.start * this.char_width;
			return `transform: translate(${offset}px, 20px)`;
		},
		
		editor() {
			return this.$refs.input;
		},
		
		input() {
			return this.$refs.input;
		},
	},
	
	methods: {
		get_next_input() {
			var self = this.$parent.$refs.render.renderLean[0];
			if (self.instImplicit)
				return self.instImplicit;
			
			if (self.strictImplicit)
				return self.strictImplicit;

			if (self.implicit)
				return self.implicit;

			if (self.given) {
				for (var i of range(0, self.given.length)) {
					if (self.given[i].insert)
						return self.given[i];
				}
			}
			
			if (self.explicit)
				return self.explicit;

			cm = self.proof[0];
			return cm.by ?? cm.calc?? cm;
		},

		keydown(event){
			var self = event.target; 
			var text = self.value;
			if (self.size <= text.length)
				self.size = text.length * 1.5;
			var key = event.key;
			switch (key) {
				case '/':
					if (!event.altKey)
						break;
					key = '';
					var start = self.selectionStart;
					var text = text.slice(0, start);
					var prefix = text.match(/([\w.]+)$/)[1] + key;
					console.log(`perform code suggestion on ${prefix}`);
					break;
				case '.':
					var start = self.selectionStart;
					var text = text.slice(0, start);
					var prefix = text.match(/([\w.]+)$/)[1] + key;
					console.log(`perform code suggestion on ${prefix}`);
					break;
				case 'ArrowDown':
					var start = self.selectionStart;
					var cm = this.get_next_input().editor;
					cm.focus();
					if (start == 0) {
						var linesToMove = cm.getCursor().line;
						for (let i = 0; i < linesToMove; ++i)
							cm.moveV(-1, "line");
					}
					else 
						cm.setCursor(0, start);
					break;
				case 'F3':
					console.log("F3 is pressed");
					find_and_jump(event, this.$parent.sections);
					break;
				case 'F5':
					if (event.ctrlKey){
						event.preventDefault();
						form.submit();
					}
					break;
				case 's':
					if (event.ctrlKey){
						event.preventDefault();
						this.$parent.save();
					}
					break;
				default:
					break;
			}
		},	
		blur(event){
			this.phrases = null;	
		},
		keydown_select(event){
			var self = event.target;
			switch (event.key) {
			case 'Enter':
				var phrase = self.options[self.selectedIndex].value;

				var input = self.nextElementSibling;
				//var selectionStart = input.selectionStart;
				var selectionStart = this.start;
				var value = input.value;
				var pos;
				if (value[selectionStart - 1] == '.'){
					pos = selectionStart;
				}
				else{
					pos = value.slice(0, selectionStart).search(/\w+$/);
				}
				
				value = value.slice(0, pos) + phrase + value.slice(selectionStart);
				input.value = value;
				this.module = value;
				
				this.phrases = null;
				
				selectionStart += phrase.length;
				break;
			case 'Escape':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;
				
				this.phrases = null;					
				break;
			case 'Backspace':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				var value = input.value;
				value = text.slice(0, selectionStart - 1) + text.slice(selectionStart);
				input.value = value;
				this.module = value;

				this.phrases = null;
				--selectionStart;
				break;
			case 'Delete':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;
				var value = input.value;
				value = text.slice(0, selectionStart) + text.slice(selectionStart + 1);
				input.value = value;
				this.module = value;
				break;
			case 'ArrowLeft':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				// console.log("selectionStart = " + selectionStart);
				this.phrases = null;
				
				--selectionStart;
				break;
			case 'ArrowRight':
				var input = self.nextElementSibling;
				var selectionStart = input.selectionStart;

				this.phrases = null;
				
				++selectionStart;
				break;
			default:
				return;
			}
			
			this.$nextTick(()=>{
				var input = this.input;
				input.focus();
				input.selectionStart = selectionStart;
				input.selectionEnd = selectionStart;
			});
		},
		
		change(event){
			document.title = event.target.value;	
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

	mounted() {
		this.$parent.update_action();
	}
};
</script>

<style>

select.non-arrowed {	
	width: auto;
	z-index: 10;
	position: absolute;
	outline: none;
}

.non-arrowed {
	-webkit-appearance: none;
	-moz-appearance: none;
	border: 0;
	font-size: inherit;
}

</style>