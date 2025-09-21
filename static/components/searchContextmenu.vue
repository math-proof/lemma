<template>
    <ul class=contextmenu tabindex=2 :style="'left:%spx; top:%spx'.format(left, top)" @blur=blur @keydown=keydown>
        <li @mouseover=mouseover @click.prevent=clickRename :style=style_font(0)>
            <u>R</u>ename
        </li>
        <li @mouseover=mouseover @click.prevent=clickDelete :style=style_font(1)>
            <u>D</u>elete
        </li>
        <li @mouseover=mouseover @click.prevent=clickOpenInNewTab :style=style_font(2)>
            Open in new <u>t</u>ab
        </li>
        <li @mouseover=mouseover @click.prevent=clickOpenInNewWindow :style=style_font(3)>
            Open in new <u>w</u>indow
        </li>
        <li @mouseover=mouseover @click.prevent=clickProperty :style=style_font(4)>
            <u>P</u>roperty
        </li>
    </ul>
</template>

<script>    
console.log('import searchContextmenu.vue');
export default {
    data() {
        return {
            focusedIndex: -1,
        };
    },
    
    props : [ 'left', 'top' ],
    
    computed:{
        numOfLi() {
            return this.$el.children.length;
        },
        
        href() {
            return this.$parent.href;
        },
    },
    
    methods : {    
		style_font(i){
			if (this.focusedIndex == i)
				return `background: #ccc;`
		},
    	
        click(event, args){
            console.log(event);
            console.log(args);
        },
    
        clickProperty(event){
        },
        
        clickDelete(event){
            console.log("clickDelete(event){");
            var parent = this.$parent;
            var indexFocused = parent.focusedIndex;
            this.focusedIndex = -1;
            
            var self = parent.children[indexFocused];
            self.remove();
            parent.remove(indexFocused);
        },
        
        clickMoveTo(event){
            parent = this.$parent;
            parent.left = -1;
            
            var href = location.href;
            var subFolder = href.match(/\/index.php(\/.*)\/(\w+)\/*$/)[2];
            
            var indexFocused = parent.focusedIndex;
            
            parent.$nextTick(()=>{
                
                var packageSelector = null;
                for (let child of parent.children){
                    if (child.$el.className == 'packageSelector-wrapper'){
                        packageSelector = child;
                        break;
                    }
                }
                
                packageSelector.focus(subFolder);
            });
        },
        
        clickRename(event){
            var parent = this.$parent;
            //var icon = parent.children[parent.focusedIndex];
            //console.log('icon = ');
            //console.log(icon);
            
            parent.showContextmenu = false;
            parent.is_edit = true;
            
            setTimeout(()=>{
                var input = parent.$el;
                input.focus();
            }, 100);
        },
        
        clickOpenInNewTab(event){
            this.focusedIndex = -1;
            window.open(this.href);
        },
        
        clickOpenInNewWindow(event){            
//window.open(location.href + theorem, "_blank", "toolbar=yes,top=500,left=500,width=400,height=400");
            this.focusedIndex = -1;
            window.open(this.href, "_blank", "toolbar=yes");
        },
        
        blur(event){
            if (this.$parent.left >= 0)
                this.$parent.showContextmenu = false;
        },
        
        keydown(event){
            console.log("keydown(event){");
            var key = event.key;
            switch(key){
            case 'ArrowDown':
                ++this.focusedIndex;
                if (this.focusedIndex == this.numOfLi){
                    this.focusedIndex = -1;
                }
                event.preventDefault();
                break;
                
            case 'ArrowUp':                
                if (this.focusedIndex < 0){
                    this.focusedIndex = this.numOfLi;
                }
                
                --this.focusedIndex;
                event.preventDefault();
                break;
            case 'Enter':
                this.$el.children[this.focusedIndex].click();
                break;
            default:
                if (key.length == 1){
                    var re = RegExp(`<u>${key}</u>`, "i");
                
                    for (var i = 0; i < this.numOfLi; ++i){
                        if (re.exec(this.$el.children[i].innerHTML)){
                            this.focusedIndex = i;
                            break;
                        }
                    }
                }
            }
        },
        
        mouseover(event){
            var li = event.target;  
            var focusedIndex = this.$el.children.indexOf(li);
            console.log("focusedIndex = " + focusedIndex);
            if (focusedIndex != this.focusedIndex && focusedIndex >= 0){
            	this.focusedIndex = focusedIndex;
            }
        },        
    },
}
</script>

<style>
.contextmenu {
    margin: 0;
    background: #fff;
    z-index: 3000;
    position: absolute;
    list-style-type: none;
    padding: 5px 0;
    border-radius: 4px;
    font-size: 12px;
    font-weight: 400;
    color: #333;
    box-shadow: 2px 2px 3px 0 rgba(0, 0, 0, 0.3);
}

.contextmenu li {
    margin: 0;
    padding: 7px 16px;
    cursor: pointer;
}

ul:focus {
    outline: none;
}

</style>