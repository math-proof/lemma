<template>
    <textarea :name=name>{{text}}</textarea>
</template>

<script setup>
import Vue from "../js/vue.js";
import { codeMirrorMounted, cmComputedUser, cmComputedModule } from "../js/codeMirrorEditor.js";

console.log('import renderLean.vue');

const props = defineProps(['text', 'index']);

/**
 * `renderLean` is a nested per-lemma tree ({instImplicit, given[i], proof.by[i], …});
 * its leaves are renderLean instances with a mounted CodeMirror in `editor`.
 * Return the first/last leaf in document (on-page) order.
 */
function extremeEditorSibling(root, first) {
    var editors = [];
    (function walk(node) {
        if (node == null)
            return;
        // A renderLean component (leaf); its data always carries `editor`.
        // Stop here so we never descend into Vue's internal instance links.
        if ('editor' in node) {
            if (node.editor)
                editors.push(node);
            return;
        }
        if (Array.isArray(node) || typeof node === 'object') {
            for (var key of Object.keys(node))
                walk(node[key]);
        }
    })(root);
    if (!editors.length)
        return;
    editors.sort((a, b) => {
        var top = (el) => {
            var rect = el.editor.getWrapperElement().getBoundingClientRect();
            return rect.top + window.scrollY;
        };
        return top(a) - top(b);
    });
    return first ? editors[0] : editors[editors.length - 1];
}

const self = new Vue({
    props,

    created() {
        setitem(this.$parent.renderLean, ...this.index, this);
    },

    computed: {
        click_left() {
            return this.$parent.click_left;
        },

        name() {
            return this.$parent.postname + this.index.map(i => `[${i}]`).join('');
        },

        user: cmComputedUser,
        module: cmComputedModule,

        open_lemma_sections() {
            return this.$parent.open_lemma_sections;
        },

        regexp_section() {
            return this.$parent.regexp_section;
        },

        firstSibling() {
            return extremeEditorSibling(this.$parent.renderLean, true);
        },

        nextSibling() {
            var {index} = this;
            var self = this.$parent;
            var [i, key] = index;
            switch (key) {
            case 'instImplicit':
                if (self.lemma.strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }

            case 'strictImplicit':
                if (self.lemma.implicit) {
                    index = [i, 'implicit'];
                    break;
                }

            case 'implicit':
                var {given} = self.lemma;
                if (given) {
                    var hit = false;
                    for (var i of range(0, given.length)) {
                        if (given[i].insert) {
                            index = [i, 'given', i];
                            hit = true;
                            break;
                        }
                    }
                    if (hit)
                        break;
                }

            case 'given':
                var {given} = self.lemma;
                var j = index[2];
                if (given && j + 1 < given.length) {
                    index = [i, 'given', j + 1];
                    break;
                }
                if (self.lemma.explicit) {
                    index = [i, 'explicit'];
                    break;
                }

            case 'explicit':
                if (self.lemma.imply.insert) {
                    index = [i, 'imply'];
                    break;
                }

            case 'imply':
                index = self.get_index(i, 0);
                break;

            case 'proof':
                var _index = self.get_index(i, index.back() + 1);
                if (_index) {
                    index = _index;
                    break;
                }
                ++i;
                var {lemma} = self.$parent;
                if (i == lemma.length) 
                    return;
                if (lemma[i].instImplicit) {
                    index = [i, 'instImplicit'];
                    break;
                }
                if (lemma[i].strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }
                if (lemma[i].implicit) {
                    index = [i, 'implicit'];
                    break;
                }
                if (lemma[i].given) {
                    index = [i, 'given', 0];
                    break;
                }
                if (lemma[i].explicit) {
                    index = [i, 'explicit'];
                    break;
                }
                index = [i, index.slice(1, -1), 0];
                break;
            }
            return getitem(self.renderLean, ...index);
        },

        previousSibling() {
            var {index} = this;
            var self = this.$parent;
            var [i, key] = index;
            switch (key) {
            case 'proof':
                var j = index.back();
                if (j > 0) {
                    index = [...index.slice(0, -1), j - 1];
                    break;
                }
                if (self.lemma.imply.insert) {
                    index = [i, 'imply'];
                    break;
                }

            case 'imply':
                if (self.lemma.explicit) {
                    index = [i, 'explicit'];
                    break;
                }

            case 'explicit':
                var {given} = self.lemma;
                if (given) {
                    var hit = false;
                    for (var j of range(given.length - 1, -1, -1)) {
                        if (given[j].insert) {
                            index = [i, 'given', j];
                            hit = true;
                            break;
                        }
                    }
                    if (hit)
                        break;
                }

            case 'given':
                var j = index[2];
                if (j > 0) {
                    index = [i, 'given', j - 1];
                    break;
                }
                if (self.lemma.implicit) {
                    index = [i, 'implicit'];
                    break;
                }

            case 'implicit':
                if (self.lemma.strictImplicit) {
                    index = [i, 'strictImplicit'];
                    break;
                }

            case 'strictImplicit':
                if (self.lemma.instImplicit) {
                    index = [i, 'instImplicit'];
                    break;
                }

            case 'instImplicit':
                if (i) {
                    index = self.get_index(i - 1, -1);
                    break;
                }
                return self.$parent.newInput;
            }
            return getitem(self.renderLean, ...index);
        },

        lastSibling() {
            return extremeEditorSibling(this.$parent.renderLean, false);
        },

        leanSourceCode() {
            return this.$parent.leanSourceCode;
        },
    },

    data() {
        return {
            editor: null,
            focus: true,
            theme: 'eclipse indent',
            hash: null,
        };
    },

    methods: {
        save() {
            this.$parent.save();
        },

        append(word) {
            // precondition: word does not contain newlines
            var cm = this.editor;
            var line = cm.lineCount() - 1;
            var ch = cm.getLine(line).length;
            cm.setCursor(line, ch);
            cm.replaceSelection(word);
            cm.setCursor(line, ch + word.length);
        },

        new_file() {
            this.$parent.new_file();
        },

        openContainingFolder() {
            this.$parent.openContainingFolder();
        },

        update(source) {
            var cm = this.editor;
            var line = cm.lastLine();
            if (source) {
                if (source.editor)
                    source = source.editor.getValue();
            }
            else
                source = '';
            cm.replaceRange(
                source,
                { line: 0, ch: 0 },
                { line, ch: cm.getLine(line).length},
            );
        }
    },

    mounted: codeMirrorMounted,
});

const { name } = self.globals;
</script>

<style>
.cm-s-indent {
	margin-left: 0.9em;
}
</style>