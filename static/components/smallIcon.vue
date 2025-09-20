<template>
	<div @click=click @dblclick=dblclick @focus=focus @blur=blur @keydown=keydown>
		<br v-for="i of lines" /> 
		<font v-if="tagName == 'FONT'">{{text}}</font> 
		<input v-else-if="tagName == 'INPUT'" :size='text.length + 1' :value=text @blur=blur_input />
		<template v-else>{{text}}</template>
	</div>
</template>

<script>
console.log('import smallIcon.vue');
var previousKey = '';
var previousTime = null;	

export default {		
	props : [ 'text', 'lines'],
	
	data(){
		return {
			tagName: '',				
		};
	},
	
	methods : {
		dblclick(event) {
			this.$parent.dblclick(event);
		},			
		
		click(event) {
			this.focus(event);
		},
		
		focus(event) {
			this.tagName = 'FONT';
		},

		blur(event) {				
			if (this.tagName == 'FONT')
				this.tagName = '';				
		},
		
		blur_input(event) {
			
			var self = event.target;
			var parent = self.parentElement;
			var text = self.value;
			
			var index = this.indexFocused();
			console.log('in blur_input, index = ' + index);
			
			var theorems = this.$root.theorems;
											
			if (text.indexOf('.') >= 0){
				var texts = text.split('.');
				theorems.delete(index);	
				var packages = this.$root.packages;
				packages.push(texts[0]);
				
				this.$root.packages = packages;
			}
			else{
				theorems[index] = text;
			}
			
			console.log('theorems = ' + theorems);
			
			this.$root.theorems = theorems;
			//console.log('this.$root.theorems = ' + this.$root.theorems);
			
			this.tagName = '';

			var href = location.href;

			var folder = href.slice(href.indexOf('.php/') + 5);
			console.log('folder = ' + folder);
			console.log('text = ' + text);
			var className = parent.className;

			console.log('rename args = ' + [className, folder, text]);

			var texts = [];
			for (let div of parent.parentElement.children) {
				if (div.tagName != 'DIV') 
					continue;
				
				var lastChild = div.lastChild;
				
				if (lastChild.nodeName == '#text')
					texts.push(lastChild.textContent.trim());
			}

			texts.push(text);
			
			console.log('texts = ' + texts);
			
			form_post("php/request/rename.php", { type: className, package: folder, files: texts }).then(res => {
				console.log('res = ' + res);
			});
		},
		
		keydown(event) {
			var self = event.target;
			var key = event.key;

			switch (key) {
				case 'ArrowLeft':
					var previousElementSibling = self.previousElementSibling;
					if (previousElementSibling == null || previousElementSibling.tagName == 'BR'){
						if (self.className == 'theorem') {
							previousElementSibling = self.parentElement.parentElement.querySelector('.package:last-of-type');
						}							
					}

					previousElementSibling.focus();
					break;
				case 'ArrowRight':
					var nextElementSibling = self.nextElementSibling;
					if (nextElementSibling == null && self.className == 'package') {
						nextElementSibling = self.parentElement.parentElement.querySelector('.theorem');
					}
					nextElementSibling.focus();
					break;
				case 'ArrowDown':
					var offsetTop = self.offsetTop;
					var current = self;						
					for(;;){
						var current = current.nextElementSibling;
						if (current == null){
							if (self.className == 'package'){
								current = self.parentElement.parentElement.querySelector('.theorem'); 
								break;
							}
							return;
						}
						
						if (current.offsetTop > offsetTop){								
							break;
						}
					}
					
					var offsetLeft = self.offsetLeft;
					for(;;){
						if (current.offsetLeft < offsetLeft){
							var nextElementSibling = current.nextElementSibling;
							if (nextElementSibling == null){
								break;
							}
							current = nextElementSibling;
						}
						else
							break;
					}
					
					current.focus();
					event.preventDefault();
					break;
				case 'ArrowUp':
					var offsetTop = self.offsetTop;						
					var current = self;						
					for(;;){
						var current = current.previousElementSibling;
						if (current.tagName == 'BR'){
							if (self.className == 'theorem'){
								current = self.parentElement.parentElement.querySelector('.package:last-of-type'); 
								break;
							}								
							return;
						}								
						
						if (current.offsetTop < offsetTop){								
							break;
						}
					}
					
					var offsetLeft = self.offsetLeft;
					for(;;){
						if (current.offsetLeft > offsetLeft){
							current = current.previousElementSibling;
						}
						else
							break;
					}
					
					current.focus();
					event.preventDefault();
					break;	
				case 'Home':
					var current = self.parentElement.parentElement.querySelector('.package');
					if (current == null){
						current = self.parentElement.parentElement.querySelector('.theorem');
					}
					current.focus();
					break;						
				case 'End':
					var current = self.parentElement.parentElement.querySelector('.theorem:last-of-type');
					if (current == null){
						current = self.parentElement.parentElement.querySelector('.package:last-of-type');
					}
					current.focus();
					break;
				case 'F2':
					this.rename();						
					break;
				case 'Enter':
					this.dblclick(event);
					break;
				case 'Delete':
					var self = this.$parent;
					var parent = self.$parent;
					parent.remove(parent.children.indexOf(self));
					break;
				case 'Backspace':
					var parent = this.$parent.$parent;
					var path = parent.path;
					parent.path = path.match(/(.*)\.\w+/)[1];
					break;
				default:
					if (key.length == 1) {
						var currentTime = new Date().getTime();
						console.log("currentTime = " + currentTime);
						console.log("previousTime = " + previousTime);
						if (previousKey && currentTime - previousTime < 256){
							key = previousKey + key;
						}
						
						console.log("key = " + key);
						
						var startFromScratch = 1;
						for (; ;) {
							if (self.nextElementSibling == null) {
								if (!startFromScratch)
									break;
								self = self.parentElement.parentElement.querySelector('.smallPackage');
								--startFromScratch;
							}
							else
								self = self.nextElementSibling;

							if (self.textContent.trim().match(eval(`/^${key}/i`))) {
								self.focus();
								break;
							}
						}
						
						previousKey = key;
						previousTime = currentTime;

						return;
					}
					break;
			}
			
			if (previousKey)
				previousKey = '';
		},

		indexFocused(){
			var self = this.$parent;				
			return self.$parent.children.indexOf(self);
		},			
	}
}
</script>

<style scoped>
div>font {
	background: #00BFFF;
}
</style>