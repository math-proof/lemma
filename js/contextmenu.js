console.log('import contextmenu.js');

export function length(inst){
	return inst.color.length;
}

export function coordinates(inst){
	var self = inst.$parent;
	var table = self.$refs.table;
	return [inst.left - table.getScrollLeft(), inst.top - table.getScrollTop()];
}

export function style_font(inst, j){
	if (inst.focusedIndex == j)
		return `background: #ccc;`
}

export function blur(inst, event){
	inst.$parent.codonContextmenu = '';
}

export function keydown(inst, event){
	var key = event.key;
	var self = event.target;
	switch (key){
	case 'ArrowDown':
		++inst.focusedIndex;
		if (inst.focusedIndex == self.children.length){
			inst.focusedIndex = 0;
		}
		event.preventDefault();
		break;

	case 'ArrowUp':
		--inst.focusedIndex;
		if (inst.focusedIndex < 0){
			inst.focusedIndex = self.children.length - 1;
		}
		event.preventDefault();
		break;

	case 'Enter':
		inst.$el.children[inst.focusedIndex].click();
		event.preventDefault();
		break;

	default:
		if (key.length == 1){
			key = key.toLowerCase();
			for (var j of range(inst.focusedIndex + 1, inst.length + inst.focusedIndex + 1)){
				j %= inst.length;
				if (inst.$el.children[j].textContent[0].toLowerCase() == key){
					inst.focusedIndex = j;
					break;
				}
			}
		}
	}
}

export function click(inst, event){
	var self = event.target;
	inst.$parent.codonContextmenu = '';
	eval(`this.${self.textContent.replace(/ /g, '_')}`)();
}

export function mouseover(inst, event){
    var li = event.target;
    var focusedIndex = inst.$el.children.indexOf(li);
    if (focusedIndex != inst.focusedIndex && focusedIndex >= 0){
    	inst.focusedIndex = focusedIndex;
    }
}

export const directives = {
	focus: {
	    // after dom is inserted into the document
	    mounted(el, binding) {
    		el.focus();
	    },
	},
};
