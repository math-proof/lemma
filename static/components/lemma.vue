<template>
    <div class=lemma>
        <template v-if=comment>
            <span class=green>/--</span><br>
            <textarea class=green :name="`lemma[${index}][comment]`" :value=comment :rows=comment_rows :cols=comment_cols @keydown=keydown_textarea></textarea>
            <span class=green>-/</span>
            <br>
        </template>
        <template v-if=attribute>
            <input type=hidden :name="`lemma[${index}][attribute]`" :value=JSON.stringify(attribute) />
            <span class=orange>@[</span><span class=blue>{{ attribute.join(", ") }}</span><span class=orange>]</span><br>
        </template>

        <select v-if=accessibility :name="`lemma[${index}][accessibility]`" :value=accessibility :style=style_select(accessibility)>
            <option v-for="value of accessibilities" :value=value>{{value}}</option>
        </select>

        <span v-clipboard class=blue :data-clipboard-text=leanSourceCode>lemma</span> <input class=orange :name="`lemma[${index}][name]`" :value=name :size="name.length + 1" @keydown=keydown_input :title=leanSourceCode />
        {{ instImplicit || strictImplicit || implicit || given || explicit? '': ':'}}
        <renderLean v-if=instImplicit :text="given || explicit || strictImplicit || implicit? instImplicit: instImplicit + ' :'" :index="[index, 'instImplicit']"></renderLean>
        <renderLean v-if=strictImplicit :text="given || explicit || implicit? strictImplicit: strictImplicit + ' :'" :index="[index, 'strictImplicit']"></renderLean>
        <renderLean v-if=implicit :text="given || explicit? implicit: implicit + ' :'" :index="[index, 'implicit']"></renderLean>

        <div v-if=given>
            <hr>
            <span v-clipboard class=green :data-clipboard-text=lemmaName :index=index><b>-- given</b></span>
            <div v-for="given, i of given" @keydown=keydown_div @click.left.stop=click_select :index=i :class="class_given(i)" tabindex="1000">
                <renderLean v-if=given.insert :text=given.lean :index="[index, 'given', i]"></renderLean>
                <template v-else>
                    <p v-latex.block=given.latex></p>
                    <input type=hidden :name="`lemma[${index}][given][${i}]`" :value=given.lean />
                </template>
                <markdown v-if=given.think :root=given.think.root v-clipboard :data-clipboard-text=given.prompt />
            </div>
        </div>

        <renderLean v-if=explicit :text=explicit :index="[index, 'explicit']"></renderLean>
        <hr>
        <a style='font-size: inherit' :href="module? `?callee=${module}`: `?mathlib=${name}`" title='callee hierarchy'>
            <span v-clipboard class=green :data-clipboard-text=lemmaName><b>-- imply</b></span>
        </a>
        <div @keydown=keydown_div @click.left.stop=click_select :class=class_imply tabindex="1000">
            <renderLean v-if=imply.insert :text=imply.lean :index="[index, 'imply']"></renderLean>
            <template v-else>
                <p v-latex.block=imply.latex></p>
                <input type=hidden :name="`lemma[${index}][imply]`" :value=imply.lean />
            </template>
            <markdown v-if=imply.think :root=imply.think.root v-clipboard :data-clipboard-text=imply.prompt />
        </div>
        <template v-if=proof>
            <hr>
            <a style='font-size: inherit' :href="`?caller=${module}`" title='caller hierarchy' target="_blank">
                <span class=green><b>-- proof</b></span>
            </a>

            <template v-for="(code, i) in get_proof_list(proof)" :key=refresh>
                <renderLean :text=code.lean :index="get_index(index, i)"></renderLean>
                <p v-latex.block=gather(code.latex)></p>
                <markdown v-if=code.think :root=code.think.root v-clipboard :data-clipboard-text=code.prompt />
            </template>
        </template>
    </div>
</template>

<script>
import renderLean from "./renderLean.vue"
import markdown from "./markdown.vue"
console.log('import lemma.vue');
const accessibilities = ['public', 'protected', 'private', 'public nonrec', 'protected nonrec', 'private nonrec', 'noncomputable', 'scoped', 'nonrec'];

export default {
    components: { renderLean, markdown },
    props : [ 'comment', 'attribute', 'accessibility', 'name', 'instImplicit', 'strictImplicit', 'implicit', 'given', 'explicit', 'imply', 'proof', 'index'],
    
    created() {
    },
    
    data() {
        return {
            postname: 'lemma',
            accessibilities,
        };
    },
    
    computed: {
        comment_rows() {
            var {comment} = this;
			return comment.split('\n').length;
		},
		
		comment_cols() {
            var {comment} = this;
			return max(comment.split('\n').map(arg => max(arg.length, 200)));
		},

        lemma() {
            return this.$parent.lemma[this.index];
        },

        click_left() {
            return this.$parent.click_left;
        },
        
        module() {
            return this.$parent.module;
        },

        sections() {
            return this.$parent.sections;
        },

        renderLean() {
            return this.$parent.renderLean;
        },

        refresh: {
            get() {
                return this.$parent.refresh;
            },
            set(value) {
                this.$parent.refresh = value;
            },
        },

        selectedIndex() {
            return this.$parent.selectedIndex;
        },

        class_imply() {
            return this.selectedIndex.equals([this.index, 'imply'])? 'focus': '';
        },

        regexp_section() {
            return new RegExp(this.sections.join('|'));
        },

        open_lemma_sections() {
            var section = [];
            for (var open of this.$parent.open_sections) {
                if (open.fullmatch(this.regexp_section))
                    section.push(open);
            }
            return section;
        },

        leanSourceCode() {
            return this.$parent.leanSourceCode(this.index);
        },

        lemmaName() {
            return this.$parent.lemmaName(this.index);
        },
    },

    updated() {
    },
    
    mounted() {
    },

    methods: {
        save() {
            this.$parent.save();
        },

        new_file() {
            this.$parent.new_file();
        },

        gather(latex) {
            if (latex && latex.isArray) {
                latex = latex.join(' \\\\\n');
                return `\\begin{gather}
${latex}
\\end{gather}`;
            }
            return latex;
        },

        code_generation(indices, line) {
            this.$parent.code_generation(indices, line);
        },

        async Escape(code, indices) {
            delete code.insert;
            var lean = getitem(this.renderLean, ...indices).editor.getValue();
            if (code.lean != lean) {
                code.lean = lean;
                var data = await form_post('php/request/latex.php', {lean});
                if (data) {
                    if (data.isArray) {
                        var [index, attr] = indices;
                        var lemma = this.$parent.lemma[index];
                        if (attr == 'given') {
                            var i = parseInt(indices[2]);
                            for (var j of range(data.length)) {
                                if (j) {
                                    if (data[j].latex) 
                                        lemma.given.insert(i + j, data[j]);
                                    else {
                                        var explicit = ranged(j, data.length).map(j => data[j].lean);
                                        if (lemma.explicit)
                                            explicit.push(lemma.explicit);
                                        lemma.explicit = explicit.join('\n');
                                        break;
                                    }
                                }
                                else
                                    Object.assign(code, data[j]);
                            }
                        }
                        else {
                            lemma.imply = data.pop();
                            var i = 0;
                            for (var j of range(data.length)) {
                                if (data[j].latex) {
                                    if (!lemma.given)
                                        lemma.given = [];
                                    lemma.given.push(data[j]);
                                }
                                else {
                                    var {lean} = data[j];
                                    if (lean.startsWith('[')) {
                                        if (lemma.instImplicit)
                                            lemma.instImplicit += '\n' + lean;
                                        else
                                            lemma.instImplicit = lean;
                                    }
                                    else if (lean.startsWith('{')) {
                                        if (lemma.implicit)
                                            lemma.implicit += '\n' + lean;
                                        else
                                            lemma.implicit = lean;
                                    }
                                    else if (lean.startsWith('(')) {
                                        if (lemma.explicit)
                                            lemma.explicit += '\n' + lean;
                                        else
                                            lemma.explicit = lean;
                                    }
                                }
                            }
                        }
                    }
                    else {
                        var {latex, error} = data;
                        if (latex)
                            code.latex = latex;
                        else if (error)
                            code.latex = error;
                    }
                }
            }
            this.click_left();
        },

        click_select(event) {
            var {target} = event;
            var {index} = this;
            var child = target;
            while (true) {
                parent = child.parentElement;
                if (parent.tagName == 'DIV')
                    break;
                child = parent;
            }

            var i = parent.getAttribute('index');
            if (i == null && child.tagName != 'P')
                return;
            this.$parent.selectedIndex.array_assign(i == null? [index, 'imply']: [index, 'given', i]);
            console.log('click_select(event) in lemma.vue', this.selectedIndex);
        },

        async keydown_div(event) {
            var {key, target} = event;
            switch (key) {
            case 'Insert':
                var {index, given, imply} = this;
                var div = target;
                while (div.tagName != 'DIV')
                    div = div.parentElement;
                var i = div.getAttribute('index');
                if (i == null) {
                    if (target.tagName == 'TEXTAREA')
                        return;
                    imply.insert = true;
                }
                else
                    given[i].insert = true;
                break;
            case 'Escape':
                var {index, given, imply} = this;
                var leanCode = target.tagName == 'TEXTAREA'? target.parentElement.parentElement: target;
                var div = leanCode.parentElement;
                var i = div.getAttribute('index');
                if (i == null) {
                    if (target.tagName == 'SPAN')
                        return;
                    await this.Escape(imply, [index, 'imply']);
                }
                else if (this.lemma)
                    await this.Escape(given[i], [index, 'given', i]);
                else
                    break;
                leanCode.remove();
                break;
            case 'Delete':
                var {index, given} = this;
                if (target.tagName == 'TEXTAREA')
                    return;
                if (target.className == 'focus' && target.parentElement.className == 'lemma') {
                    var {lemma} = this.$parent;
                    if (lemma.length > 1) {
                        var {renderLean} = this.$parent;
                        for (var i of range(index, lemma.length - 1)) {
                            var {instImplicit, implicit, strictImplicit, explicit, given, proof} = renderLean[i];
                            if (instImplicit)
                                instImplicit.update(renderLean[i + 1].instImplicit);
                            if (implicit)
                                implicit.update(renderLean[i + 1].implicit);
                            if (strictImplicit)
                                strictImplicit.update(renderLean[i + 1].strictImplicit);
                            if (given)
                                given.update(renderLean[i + 1].given);
                            if (explicit)
                                explicit.update(renderLean[i + 1].explicit);
                            if (proof) {
                                var attr = proof.by? 'by': proof.calc? 'calc': '';
                                if (attr) {
                                    for (var j of range(proof[attr].length)) {
                                        proof[attr][j].update(renderLean[i + 1]?.proof[attr][j]);
                                    }
                                }
                            }
                        }
                        lemma.delete(index);
                        if (lemma.length == 1)
                            lemma[0].name = 'main';
                    }
                    return;
                }
                if (!given)
                    return;
                var i = target.getAttribute('index');
                given.delete(i);
                if (given.length == i) {
                    var back = given.back();
                    if (back) {
                        back.lean += ' :';
                        back.latex = back.latex.replace(/(\$\}\\\])$/, ' :$1');
                    }
                    else {
                        var {lemma} = this;
                        delete lemma.given;
                        if (!lemma.explicit) {
                            var key = null;
                            if (lemma.implicit)
                                key = 'implicit';
                            else if (lemma.strictImplicit)
                                key = 'strictImplicit';
                            else if (lemma.instImplicit)
                                key = 'instImplicit';
                            else
                                return;
                            var word = ' :';
                            lemma[key] += word;
                            this.renderLean[index][key].append(word);
                        }
                    }
                }
                break;
            case 'F5':
                console.log('F5');
                event.preventDefault();
                break;
            }
        },

        async keydown_input(event) {
            var {key, target} = event;
            switch (key) {
            case 'Enter':
                var {selectionStart, selectionEnd, value} = target;
                if (selectionStart == selectionEnd && value.length == selectionStart) {
                    var {lemma} = this.$parent;
                    if (!lemma[this.index].instImplicit)
                        lemma[this.index].instImplicit = "[]";
                }
                event.preventDefault();
                break;
            case 'W':
                if (event.altKey)
                    this.openContainingFolder();
                break;
            }
        },

        openContainingFolder() {
            this.$parent.openContainingFolder();
        },

        async keydown_textarea(event) {
            var {key, target} = event;
            switch (key) {
            case 's':
                if (event.ctrlKey) {
                    this.save();
                    event.preventDefault();
                }
                break;
            case 'W':
                if (event.altKey)
                    this.openContainingFolder();
                break;
            }
        },

        class_given(i){
            return this.selectedIndex.equals([this.index, 'given', i])? 'focus': '';
        },

        style_select(value) {
            return `width: ${value.length / 2 + 0.5}em`;
        },

        get_proof_list(proof) {
            return proof.by?? proof.calc?? proof;
        },

        get_index(index, i) {
            var {proof} = this;
            index = [index, 'proof'];
            var by = proof.by? 'by' : proof.calc? 'calc' : '';
            if (by) {
                index.push(by);
                proof = proof[by];
            }
            if (i < 0)
                i += proof.length;
            index.push(i);
            if (i < proof.length)
                return index;
        },
    },
    
    directives: {
        clipboard,
        latex
    },
};

</script>

<style scoped>

select {
    color: blue;
    outline: none;
    background-color: transparent;
    box-shadow: none;
    border: none;
    padding: 0;

    -webkit-appearance: none;
    -moz-appearance: none;
    appearance: none;    
    font-size: inherit;
    font-family: inherit;
    font-weight: inherit;
    font-style: inherit;
}

div {
    caret-color: transparent;
}

span.blue {
    color: blue;
}

.green {
    color: green;
}

.orange {
    color: orange;
}

div.focus {
    outline: 2px dotted red;
    /* background-color: white; */
}

textarea{
	font-style: normal;
	font-size: 1em;
	font-weight: normal;
	font-family: Consolas;

	background: transparent;
	resize: none;
	border: none;
	border-style: none;
	padding: 0px 0px 0px 0px;
	
	display: block;
	overflow: hidden;
}

textarea:focus {
	outline: none;
	caret-color: rgb(127, 0, 85);
}
</style>