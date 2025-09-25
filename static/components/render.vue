<template>
    <div v-finish @click.left.stop=click_left @keydown=keydown>
        <form name=form spellcheck=false enctype="multipart/form-data" method=post :action=action>
            <input type=hidden name=imports :value=JSON.stringify(imports) />
            <input type=hidden name=def :value=JSON.stringify(def) />
            <input type=hidden name=open :value=JSON.stringify(open) />
            <input type=hidden name=set_option :value=JSON.stringify(set_option) />
            <input type=hidden name=date :value=JSON.stringify(date) />
            <def v-for="lean, index in def" :lean=lean :index=index></def>
            <lemma v-for="lemma, index in lemma" :comment=lemma.comment :attribute=lemma.attribute :accessibility=lemma.accessibility :name=lemma.name :instImplicit=lemma.instImplicit :strictImplicit=lemma.strictImplicit :implicit=lemma.implicit :given=lemma.given :explicit=lemma.explicit :imply=lemma.imply :proof=lemma.proof :index=index></lemma>
        </form>

        <template v-if="error.length != 0">
            <br><br>
            <h3>Error Information</h3>
        </template>

        <div v-for="err of error">
            <h5>{{err.type}}:</h5>
            <p class="pre-wrap warning">{{err.info}}</p>
            <h5>code:{{ err.line }}:{{ err.col }}</h5>
            <p class="pre-wrap error">{{err.code}}</p>
            <hr>
        </div>

        <div class=bottom-line>
            <p class="right">
                <a :href=href_switch><span class=date>Created on {{date.created}}</span></a>
                <br>
                <span v-if=date.updated class=date>Updated on {{date.updated}}</span>
            </p>
            <p class="left">
                <button type=button class=transparent @click=click_download :title="`download into a single ${ext} file`"><u>download</u></button> into a
			    <select v-model=ext>
				    <option v-for="value of ['lean', 'json']" :value=value>{{value}}</option>
			    </select> file, or view via 
                <button type=button class=transparent @click=click_lean4web title="view this lean file via lean4web"><u>lean4web</u></button>
            </p>
        </div>
    </div>
</template>

<script>
import lemma from "./lemma.vue"
import def from "./def.vue"
import { mounted, click_left, fetch_lemma, has_typeclasses } from "../js/lemma.js"
import { generate, parse_token } from "../js/prompting.js"
import MarkdownParser from "../js/parser/markdown.js"
import { tactics } from "../codemirror/mode/lean/tactics.js"
import { sbd } from "../js/sbd.js"
console.log('import render.vue');

function postprocess_word(text, word) {
	for (var char of word)
		text = postprocess_char(text, char);
	return text;
}

function postprocess_char(parser, char) {
	if (!parser.start)
		parser.start = 0;
	parser.parse(char, parser.start);
	parser.start++;
	return parser;
}

export default {
    components: { lemma, def },
    props : [ 'imports', 'open', 'set_option', 'def', 'lemma', 'error', 'module', 'date'],
    
    created() {
    },
    
    data() {
        // const model = 'deepseek-r1';
        const model = 'deepseek-reasoner';
        const PartialOrder = {
            Preorder: [],
        };
        const Mul = [];
        const Add = [];
        const Inv = [];
        const Zero = [];
        const One = [];
        const Semigroup = {Mul};
        const AddSemigroup = {Add};
        const MulZeroClass = {Mul, Zero};
        const MulOneClass = {One, Mul};
        const Monoid = {
            // typeclass for: Complex, Real, Rational, Integer with supported operators +-* 
            Semigroup,
            MulOneClass,
        };
        const AddMonoid = {
            AddSemigroup,
            AddZeroClass: [],
        };
        const CommMagma = {Mul};
        const AddCommMagma = {Add};
        const CommMonoid = {
            Monoid, 
            CommSemigroup : {
                Semigroup, 
                CommMagma,
            },
        };
        const AddCommMonoid = {
            AddMonoid, 
            AddCommSemigroup: {
                AddSemigroup,
                AddCommMagma,
            }
        };
        const AddGroup = [];
        const AddCommGroup = {
            AddGroup, 
            AddCommMonoid,
        };
        const LeftDistribClass = {Mul, Add};
        const RightDistribClass = {Mul, Add};
        const Distrib = {
            Mul, Add, 
            LeftDistribClass, // Distrib.leftDistribClass
            RightDistribClass, // Distrib.rightDistribClass
        };
        const NonUnitalNonAssocSemiring = {
            AddCommMonoid, 
            Distrib, 
            MulZeroClass
        };
        const SemigroupWithZero = {Semigroup, MulZeroClass};
        const MulZeroOneClass = {MulOneClass, MulZeroClass};
        const MonoidWithZero = {
            Monoid,
            MulZeroOneClass,
            SemigroupWithZero,
        };
        const CommMonoidWithZero = {
            // Nat
            CommMonoid, 
            MonoidWithZero,
        };
        const AddMonoidWithOne = {
            NatCast: [], 
            AddMonoid, 
            One,
        };
        const AddCommMonoidWithOne = {
            AddMonoidWithOne, 
            AddCommMonoid,
        };
        const NonUnitalSemiring = {NonUnitalNonAssocSemiring, SemigroupWithZero};
        const NonAssocSemiring = {NonUnitalNonAssocSemiring, MulZeroOneClass, AddCommMonoidWithOne};
        const Semiring = {NonUnitalSemiring, NonAssocSemiring, MonoidWithZero}
        const AddGroupWithOne = {
            IntCast: [], 
            AddMonoidWithOne, 
            AddGroup,
        };
        const NonUnitalNonAssocRing = {
            AddCommGroup, 
            NonUnitalNonAssocSemiring
        };
        const AddCommGroupWithOne = {
            AddCommGroup, 
            AddGroupWithOne, 
            AddCommMonoidWithOne,
        };
        const NonAssocRing = {
            NonUnitalNonAssocRing, 
            NonAssocSemiring,
            AddCommGroupWithOne,
        };
        const NonUnitalRing = {
            NonUnitalNonAssocRing, 
            NonUnitalSemiring
        };
        const Ring = {
            Semiring,
            AddCommGroup, 
            AddGroupWithOne,
            NonUnitalRing, //Ring.toNonUnitalRing
            NonAssocRing, // Ring.toNonAssocRing
        };
        const CommSemiring = {
            Semiring, 
            CommMonoid,
        };
        const DivInvMonoid = {
            Monoid, 
            Inv,
            Div: [],
        };
        const GroupWithZero = {
            MonoidWithZero, 
            DivInvMonoid,
            Nontrivial: [],
        }
        const DivisionSemiring = {
            Semiring, 
            GroupWithZero,
        };
        const NonUnitalCommRing = {
            NonUnitalRing,
            NonUnitalNonAssocCommRing: {
                NonUnitalNonAssocRing, 
                NonUnitalNonAssocCommSemiring: {
                    NonUnitalNonAssocSemiring, 
                    CommMagma,
                }
            }
        };
        return {
        	renderLean: [],
            refresh: false,
            action: '',
            sections: [],
            typeclass: {
                // typeclass for: Real, Rational with supported operators +-*/<>≤≥ 
                LinearOrderedField: {
                    // typeclass for: Complex, Real, Rational with supported operators +-*/
                    Field : {
                        // typeclass for: Complex, Real, Rational, Integer with supported operators +-*
                        CommRing: {
                            Ring, 
                            CommMonoid,
                            CommSemiring, // CommRing.toCommSemiring
                            AddCommGroupWithOne,// CommRing.toAddCommGroupWithOne
                            NonUnitalCommRing, // CommRing.toNonUnitalCommRing
                        },
                        DivisionRing: {
                            Ring, 
                            DivInvMonoid,
                            DivisionSemiring, // DivisionRing.toDivisionSemiring
                        },
                        // Field.toSemifield
                        Semifield: {
                            CommSemiring, 
                            DivisionSemiring, 
                            CommGroupWithZero: {
                                CommMonoidWithZero, 
                                GroupWithZero,
                                // CommGroupWithZero.toDivisionCommMonoid
                                DivisionCommMonoid: {
                                    DivisionMonoid: {
                                       DivInvMonoid,
                                       InvolutiveInv: {Inv},
                                    },
                                    CommMonoid,
                                }, 
                            },
                        }
                    },
                    LinearOrderedCommRing: {
                        // typeclass for: Real, Rational, Integer with supported operators +-*<>≤≥ 
                        LinearOrderedRing: {
                            StrictOrderedRing: {
                                Ring, 
                                OrderedAddCommGroup: {
                                    AddCommGroup, 
                                    PartialOrder,
                                },
                            }, 
                            LinearOrder: {
                                PartialOrder,
                            },
                        },
                        CommMonoid,
                    }
                },
                // typeclass for: Integer, Natural with supported operators +-*<>≤≥ 
                IntegerRing:[], 
                FloorRing: [],
                Inhabited: [],
                GetElem: [],

                Decidable: [],
                DecidableEq: [],
                DecidablePred: [],
                DecidableRel: [],
                LE: [], 
                LT: [],
                // functions
                KroneckerDelta: [],
            },
            tactics,
            selectedIndex: [],
            model : getParameterByName('model', model),
            ext: 'lean',
            prequisite: {
                Mathlib: {
                    'Mathlib.Tactic': true,
                },
                sympy: {},
                stdlib: {},
                linter: {},
                open: {
                    list: {},
                    dict: {},
                },
            },
        };
    },

    computed: {
        typeclasses() {
            var keys = new Set();
            const queue = new Deque([this.typeclass]);
            while (!queue.isEmpty()) {
                var item = queue.shift();
                if (typeof item === "string") 
                    keys.add(item);
                else {
                    for (var [key, value] of Object.entries(item)) {
                        keys.add(key);
                        if (value.isArray)
                            queue.push(...value);
                        else
                            queue.push(value);
                    }
                }
            }
            return [...keys];
        },

        submodules() {
            return this.imports.flatMap(imp => {
                var m = imp.match(/^Lemma\.(?!Basic$)(.+)/); 
                return m? [m[1]] : [];
            });
        },

        json() {
            return this.$parent.$data;
        },

        initial_line() {
            var {imports, open} = this;
            return imports.length + open.length;
        },

        regexp_section() {
            return new RegExp(this.sections.join('|'));
        },

        open_sections() {
            var sections = [];
            for (var open of this.open) {
                if (open.isArray)
                    sections.push(...open);
            }
            return sections;
        },

        theorem() {
            return this.lemma.back();
        },

        user() {
            return axiom_user();
        },

        hash() {
        	var hash = location.hash;
        	if (hash){
        		return hash.slice(1);
        	}
        },

        href_switch() {
			var {protocol, host, pathname, search, hash} = location;
            if (pathname.match(/\/lean\/(index\.php)?/)) {
                pathname = '/py/';
                search = search.replace(/(?<=[.\/\\])(in|is)(?=[.\/\\])/g, m => m.capitalize());
            }
			return `${protocol}\/\/${host}${pathname}${search}${hash}`;
        },
    },

    updated() {
    },

    async mounted() {
        form_post('php/request/sections.php').then(sections => {
            this.sections = sections;
        });

        mounted(this);
        var {module} = this;
        if (!module) {
            var module = getParameterByName('module');
            module = module.replace(/[\/\\]/g, '.');
            this.$parent.$data.module = module;
            this.$props.module = module;
            await this.echo(module);
        }

        var {hash} = location;
        if (hash) {
            hash = hash.slice(1);
            var [line, col] = hash.split(':');
            var index;
            if (line.isInteger) {
                line = parseInt(line);
                col = parseInt(col);
            }
            else if ((index = this.lemma.findIndex(lem => lem.name == line)) >= 0) {
                var indices = [index, 'proof'];
                var {proof} = this.lemma[index];
                if (proof.calc)
                    indices.push('calc');
                else if (proof.by)
                    indices.push('by');
                indices.push(0);
                line = this.indices2line(indices);
            } else {
                var [indices] = this.regexp2indices(line.replace(/\./g, '\\.'));
                if (indices)
                    line = this.indices2line(indices);
                else 
                    line = null;
            }
            if (line)
                this.highlight(line, col);
            else {
                switch (hash) {
                case 'window.close':
                    window.close();
                    break;
                case 'lean4web':
                    this.click_lean4web();
                    break;
                }
            }
        }

        var {error} = this;
        var sorry = [];
        for (var err of reversed(error)) {
            var {line, col, info} = err;
            if (info == "declaration uses 'sorry'")
                sorry.push(err);
            else
                this.highlight(line, col, info);
        }
        if (sorry.length) {
            var sorryRegexp = /(?<!^ *--.*)\bsorry\b/;
            var [...indices] = this.regexp2indices(sorryRegexp, false, false);
            for (var [err, index] of zip(sorry, indices)) {
                var line = this.indices2line(index);
                var offset = index.pop();
                var code = getitem(this.lemma, ...index);
                var m = code.lean.split('\n')[offset].match(sorryRegexp);
                if (m)
                    col = m.index;
                this.highlight(line, col, err.info);
                err.line = line;
                err.col = col;
            }
        }

        var model = getParameterByName('model');
        if (model) {
            this.model = model;
            for (var [i, lemma] of enumerate(this.lemma)) {
                if (lemma.name == 'main') {
                    var index = [i, 'proof'];
                    var {proof} = lemma;
                    var attr = proof.by? 'by' : (proof.calc? 'calc' : null);
                    if (attr) {
                        index.push(attr);
                        proof = proof[attr];
                    }
                    index.push(proof.length - 1);
                    this.code_generation(index, proof.back().lean.split("\n").length - 1);
                }
            }
        }
    },

    methods: {
        leanSourceCode(index) {
            var {module} = this;
            if (!module)
                module = getParameterByName('module');
            return `Lemma/${module.replace(/[.]/g, '/')}.lean`;
        },

        lemmaName(index) {
            var {name} = this.lemma[index];
            var {module} = this;
            if (name != 'main')
                module += '.' + name.toLowerCase();
            return module;
        },

        async lean() {
            var {module} = this;
            var code = await this.piece_together(`
with topology as (
    WITH RECURSIVE dependencies AS (
        SELECT
            module,
            0 as depth
        FROM
            axiom.lemma
        WHERE
            module = "${module}"
        UNION ALL
        SELECT
            SUBSTRING(jt.module, LOCATE('.', jt.module) + 1),
            dependencies.depth + 1
        FROM
            dependencies
            JOIN axiom.lemma as _t using(module)
            CROSS JOIN JSON_TABLE(
                _t.imports,
                '$[*]' COLUMNS (module text PATH '$')
            ) AS jt
        WHERE
            jt.module LIKE 'Lemma.%'
    )
    SELECT
        module,
        max(depth) as depth
    FROM
        dependencies
    where 
        module != "${module}"
    group by module
)
select * from topology
JOIN axiom.lemma as _t using(module)
order by depth desc`);
            return code.join("\n\n");
        },

        async piece_together(sql, axiom) {
            console.log(sql);
            var topology = await form_post('php/request/execute.php', {sql, resultType: 1});
            for (var obj of topology) {
                var {module, imports, lemma, open, def} = obj;
                Object.assign(
                    obj, 
                    {
                        imports: JSON.parse(imports),
                        lemma: JSON.parse(lemma),
                        open: JSON.parse(open),
                        def: JSON.parse(def)
                    }
                );
            }
            topology.push({
                module: this.module,
                imports: this.imports,
                lemma: deepCopy(this.lemma, ['think', 'final']),
                open: this.open,
                def: this.def
            });
            await this.fetch_lemma_sequentially(topology, axiom);
            if (axiom)
                topology.pop();
            return [await this.fetch_prequisite(topology, axiom), ...this.fetch_dependency(topology)];
        },

		async click_download(event) {
            var {ext, module} = this;
            var data;
            switch (ext) {
            case 'lean':
                data = await this.lean();
                break;
            case 'json':
                data = this.json;
                break;
            }
			module = module.replace(/[.\/\\]/g, '.');
			saveFile(`${module}.${ext}`, data);
		},

		async click_lean4web(event) {
            var code = await this.lean();
            var codez = LZString.compressToEncodedURIComponent(code);
            codez = codez.replace(/-/g, '/');
            window.open(
                `https://live.lean-lang.org/#project=mathlib-stable&codez=${codez}`,
                '_blank'
            );
		},

        highlight(line, col, title) {
            var indices = this.line2indices(line);
            var line = indices.pop();
            if (line == null) {
                var [index, attr] = indices;
                switch (attr) {
                case 'proof':
                    var a = this.$el.querySelectorAll('a[title="caller hierarchy"]')[index];
                    a.focus();
                    this.select_span(a.firstChild);
                    break;
                case 'given':
                    var span = this.$el.querySelector(`span.green[data-clipboard-text][index="${index}"]`);
                    this.select_span(span);
                    break;
                case 'imply':
                    var a = this.$el.querySelectorAll('a[title="callee hierarchy"]')[index];
                    a.focus();
                    this.select_span(a.firstChild);
                    break;
                case 'name':
                    var input = this.$el.querySelector(`input[name="lemma[${index}][name]"]`);
                    input.focus();
                    input.select();
                    break;
                case 'attribute':
                    var input = this.$el.querySelector(`input[name="lemma[${index}][attribute]"]`);
                    this.select_span(input.nextElementSibling);
                    break;
                case 'created':
                    var span = this.$el.querySelector(`a > span.date`);
                    this.select_span(span);
                    break;
                case 'updated':
                    var span = this.$el.querySelector(`p > span.date`);
                    this.select_span(span);
                    break;
                }
            }
            else if (!this.select(indices, line, col, title)) {
                var [index, attr] = indices;
                switch (attr) {
                case 'imply':
                    this.lemma[index].imply.insert = true;
                    this.$nextTick(() => {
                        this.select(indices, line, col, title);
                    });
                    break;
                case 'given':
                    this.lemma[index].given[indices[2]].insert = true;
                    this.$nextTick(() => {
                        this.select(indices, line, col, title);
                    });
                    break;
                }
            }
        },

        save() {
            var {save} = this.$parent;
            if (save)
                save();
            else
                form.submit();
        },

        new_file() {
            var {module} = this;
            if (module.match(/[.\/\\]$/))
                module = module.slice(0, -1);
            window.open(`?new=${module}`);
        },

        async fetch_prequisite(topology, use_axiom) {
            var {prequisite} = this;
            var {stdlib, sympy, linter, open, ...imports_dict} = prequisite;
            var requisites_stdlib = await this.process_inner_import_given_package(stdlib, topology, use_axiom);
            var requisites_sympy = await this.process_inner_import_given_package(sympy, topology, use_axiom);
            var stdlib_code = this.fetch_code_given_package(stdlib, requisites_stdlib);
            var sympy_code = this.fetch_code_given_package(sympy, requisites_sympy);
            var imports = [];
            for (var section in imports_dict)
                imports.push(...Object.keys(prequisite[section]).map(module => `import ${module}`));
            return [[...imports, ...Object.values(linter), ...this.fetch_open(open)].join('\n'), ...stdlib_code, ...sympy_code].join("\n\n");
        },

        fetch_code_given_package(pkg, requisites) {
            var codes = [];
            for (var module of topologicalSortDepthFirst(
                Object.fromEntries(
                    Object.entries(pkg).map(
                        ([module, code]) => [module, code.imports]
                    )
                )
            )) {
                var {code, axiom} = pkg[module];
                if (axiom && axiom.length) {
                    axiom = axiom.map(name => {
                        var index = requisites.findIndex(code => code.module == name);
                        if (index >= 0) {
                            var {def, lemma} = requisites[index];
                            return [...def, ...lemma].join("\n\n");
                        }
                    }).filter(code => code);
                    codes.push(...axiom);
                }
                codes.push(code);
            }
            return codes;
        },

        async process_inner_import_given_package(pkg, topology, use_axiom) {
            var requisites = [];
            for (var module in pkg) {
                var {axiom} = pkg[module];
                if (axiom && axiom.length)
                    await this.process_inner_import(topology, axiom, use_axiom, requisites, module);
            }
            return requisites;
        },

        async process_inner_import(topology, imports, axiom, requisites, parent) {
            var indicesToDelete = [];
            for (var imp of imports) {
                var index = topology.findIndex(code => code.module == imp);
                if (index >= 0) {
                    var codeObject = topology[index];
                    indicesToDelete.push(index);
                }
                else {
                    var sql = `
SELECT
    *
FROM
    axiom.lemma
where
    module = "${imp}"`;
                    var data = await form_post('php/request/execute.php', {sql, resultType: 1});
                    if (data.length) {
                        var codeObject = data[0];
                        codeObject.imports = JSON.parse(codeObject.imports);
                        codeObject.lemma = JSON.parse(codeObject.lemma);
                        codeObject.open = JSON.parse(codeObject.open);
                        codeObject.set_option = JSON.parse(codeObject.set_option);
                        codeObject.def = JSON.parse(codeObject.def);
                        await this.fetch_lemma(codeObject, axiom, parent);
                    }
                    else {
                        console.log(`module ${imp} not found`);
                        continue;
                    }
                }
                requisites.push(codeObject);
            }
            indicesToDelete.reverse();
            for (var index of indicesToDelete)
                topology.splice(index, 1);
        },

        fetch_open(open) {
            var {list, dict} = open;
            var keys = Object.keys(list);
            var open = [];
            for (let key of keys) {
                switch (key) {
                case 'Set':
                case 'Algebra':
                case 'Lean':
                case 'Elab.Tactic':
                case 'Lean.Meta':
                case 'Meta':
                case 'Elab':
                case 'Tactic':
                case 'Command':
                case 'Parser.Term':
                case 'Parser.Tactic':
                    break;
                default:
                    open.push(`namespace ${key}\nend ${key}`);
                }
            }
            keys = keys.join(' ');
            if (keys)
                open.push(`open ${keys}`);
            for (var key in dict) {
                var value = dict[key];
                value = Object.keys(value).join(' ');
                open.push(`open ${key} (${value})`)
            }
            return open;
        },

        async fetch_module_recursively(module, functions, parent) {
            var {prequisite} = this;
            var pkg = module.split('.')[0];
            if (prequisite[pkg][module])
                return;
            if (parent && parent.split('.')[0] == pkg)
                prequisite[pkg][parent].imports.push(module);
            prequisite[pkg][module] = { imports: [] };
            var {code} = await form_post('php/request/fetch.php', {module});
            var m;
            if (functions) {
                code = code.trim();
                var codes = [];
                for (var f of functions) {
                    var m = code.match(new RegExp(`(?<=\n)def ${f.replace(/\./g, '\\.')}\\b(?!\\.)[\\s\\S]*`));
                    if (m)
                        codes.push(m[0].split(/\n\n+/)[0]);
                }
                prequisite[pkg][module].code = codes.join("\n\n");
                return;
            }
            code = code.split("\n");
            var index = 0;
            for (var [i, line] of enumerate(code)) {
                if (m = line.match(/^import ([\w.]+)(.*)/)) {
                    var packages = m[1].split('.');
                    switch (packages[0]) {
                    case 'sympy':
                    case 'stdlib':
                        var match = m[2].trim().match(/^-- using((?: [\w.]+)+)/);
                        var functions = match? match[1].trim().split() : null;
                        console.log(`from ${module} import ${m[1]}`);
                        await this.fetch_module_recursively(m[1], functions, module);
                        if (!functions && pkg == packages[0]) 
                            prequisite[pkg][module].imports.push(m[1]);
                        break;
                    case 'Lemma':
                        if (!prequisite[pkg][module].axiom)
                            prequisite[pkg][module].axiom = [];
                        prequisite[pkg][module].axiom.push(packages.slice(1).join('.'));
                        break;
                    default:
                        setitem(prequisite, packages[0], m[1], true);
                        break;
                    }
                } 
                else if (m = line.match(/^open ([\w.' ]+)$/)) {
                    for (var name of m[1].trim().split(' '))
                        setitem(prequisite.open.list, name, true);
                }
                else if (m = line.match(/^open ([\w.']+) \(([\w.' ]+)\)$/)) {
                    var name = m[1];
                    for (var val of m[2].trim().split(' '))
                        setitem(prequisite.open.dict, name, val, true)
                }
                else if (line.length && !line.isspace()) {
                    index = i;
                    break;
                }
            }
            code = code.slice(index).join("\n");
            code = code.replace(/\/--.*?-\/\n*/sg, ''); // remove all docstrings
            prequisite[pkg][module].code = code.rtrim();
        },

        window_open(module) {
            if (this.seconds) {
                this.seconds += 10;
                this.seconds = Math.min(86400, this.seconds);
            }
            else
                this.seconds = 10;
            setTimeout(async seconds => {
                await sleep(seconds);
                window.open(
                    location.origin + location.pathname + `?module=${module}#window.close`,
                    '_blank'
                );
            }, 1000, this.seconds);
        },

        async fetch_lemma(codeObject, axiom, parent) {
            var {module, imports, lemma, open} = codeObject;
            // console.log(`fetching ${module}`);
            var {prequisite} = this;
            if (module.match(/__/))
                prequisite.linter['linter.style.nameCheck'] = 'set_option linter.style.nameCheck false';
            else if (module.match(/(?<=\.|^)([\w']+)\.\1(?=\.|$)/))
                prequisite.linter['linter.dupNamespace'] = 'set_option linter.dupNamespace false';
            if (!lemma.length)
                this.window_open(module);
            var hit = false;
            for (var [i, lemma] of enumerate(lemma)) {
                var {name} = lemma;
                lemma.name = module;
                if (name != 'main')
                    lemma.name += '.' + name.toLowerCase();
                var lemmaType;
                if (module == this.module && name == 'main')
                    lemmaType = 'theorem';
                else if (axiom) {
                    delete lemma.proof;
                    delete lemma.comment;
                    var m = lemma.imply.lean.match(/(.+) ?:=( ?by| ?calc|$)/);
                    if (m)
                        lemma.imply.lean = m[1];
                    lemmaType = 'axiom';
                }
                else {
                    lemmaType = 'lemma';
                    hit ||= !lemma.comment;
                }
                if (lemma.attribute) {
                    // lemma.attribute.remove('main');
                    lemma.attribute.clear();
                }
                delete lemma.accessibility;
                lemma = fetch_lemma(lemma, lemmaType, false);
                codeObject.lemma[i] = lemma;
                if (lemma.match(/\bmain\]/)) {
                    console.log(lemma);
                    this.window_open(module);
                }
            }

            if (hit && false)
                // console.log(module, 'has no comment');
                this.window_open(module);
            var submodules = [];
            for (let module of imports) {
                var section = module.split('.');
                switch (section[0]) {
                case 'Lemma':
                    if (section[1] == 'Basic')
                        break;
                    module = section.slice(1).join('.');
                    submodules.push(module);
                    break;
                case 'sympy':
                case 'stdlib':
                    console.log(`from ${codeObject.module} import ${module}`);
                    await this.fetch_module_recursively(module, null, parent);
                    break;
                default:
                    setitem(prequisite, section[0], module, true);
                    break;
                }
            }
            codeObject.imports = submodules;
            for (var name of open) {
                if (name.isArray) {
                    for (var name of name)
                        setitem(prequisite.open.list, name, true);
                }
                else {
                    [[key, values]] = Object.entries(name);
                    for (var val of values)
                        setitem(prequisite.open.dict, key, val, true)
                }
            }
        },

        async fetch_lemma_sequentially(topology, axiom) {
            for (var codeObject of topology) {
                try {
                    await this.fetch_lemma(codeObject, axiom);
                }
                catch (err) {
                    var {module} = codeObject;
                    alert(`error fetching ${module}`);
                    this.window_open(module);
                }
            }
        },

        fetch_dependency(topology) {
            var def = [];
            var lemma = [];
            for (var codeObject of topology) {
                def.push(...codeObject.def);
                lemma.push(...codeObject.lemma);
            }
            return [...def, ...lemma];
        },

        update(indices, value) {
            if (!value)
                return;
            if (value.isArray) {
                for (var i of range(value.length))
                    this.update([...indices, i], value[i]);
            }
            else if (typeof value == 'object') {
                if (value._) {
                    var {editor} = value;
                    if (editor) {
                        var value = editor.getValue();
                        if (value?.isString) {
                            var oldValue = getitem(this.lemma, ...indices);
                            if (oldValue?.isString)
                                setitem(this.lemma, ...indices, value);
                            else if (oldValue?.lean.isString)
                                setitem(this.lemma, ...indices, 'lean', value);
                        }
                    }
                    return;
                }
                for (var [key, value] of Object.entries(value)) {
                    this.update([...indices, key], value);
                }
            }
        },

        async code_generation(index, cursor_line) {
            this.update([], this.renderLean);
            var line = this.indices2line(index) + cursor_line;
            var {error, module, imports} = this;
            var lemma = deepCopy(this.lemma, ['think', 'final']);
            setitem(this.lemma, ...index, 'think', new MarkdownParser);
            setitem(this.lemma, ...index, 'final', '');
            var errorIndex = error.findIndex(err => err.line == line && err.type != 'warning');
            var lemmaType = lemma[index[0]].name == 'main'? 'theorem': 'lemma';
            if (errorIndex < 0) {
                var sorry = false;
                if (error.length || (sorry = getitem(lemma, ...index).lean.match(/^ *sorry *$/m))) {
                    var {by} = lemma[index[0]].proof;
                    if (by && by.length == 1) {
                        console.log(by);
                        if (by[0].lean.match(/^ *sorry *$/)) {
                            by[0].lean += ' -- please try to apply builtin lemmas in mathlib to prove this theorem';
                            sorry = true;
                        }
                    }
                    var codes = ranged(index[0] + 1).map(i => {
                        // lemma[i].attribute.remove('main');
                        lemma[i].attribute.clear();
                        var {name} = lemma[i];
                        if (name == 'main') {
                            lemma[i].name = module;
                            var lemmaType = 'theorem';
                        }
                        else {
                            lemma[i].name = module + '.' + name.toLowerCase();
                            var lemmaType = 'lemma';
                        }
                        return fetch_lemma(lemma[i], lemmaType);
                    });
                    var code = codes.join("\n\n");
                    code = code.rtrim();
                    if (!sorry) {
                        var m = code.match(/^ *sorry *$/m);
                        if (!m) {
                            m = code.match(/(\n +).+$/);
                            var spaces = m ? m[1] : '\n  ';
                            code += spaces + 'sorry';
                        }
                    }
                }
                else {
                    if (lemma[index[0]].comment)
                        return;
                    lemma.forEach(lemma => {
                        if (lemma.attribute) {
                            // lemma.attribute.remove('main');
                            lemma.attribute.clear();
                        }
                        delete lemma.accessibility;
                    });
                    var codes = ranged(index[0] + 1).map(i => {
                        lemmaType = 'lemma';
                        if (lemma[i].name == 'main')
                            lemma[i].name = module;
                        if (i == index[0])
                            lemma[i].comment = `Please add the docstring here to describe the purpose of the following ${lemmaType}.`;
                        return fetch_lemma(lemma[i], lemmaType);
                    });
                    var code = codes.join("\n\n");
                    code = code.rtrim();
                    errorIndex = -2;
                }
            }
            else {
                var code = getitem(lemma, ...index);
                var old_lean = code.lean;
                var old_leans = old_lean.split("\n");
                var old_lean_head = old_leans.slice(0, cursor_line + 1).join("\n");
                var old_lean_tail = old_leans.slice(cursor_line + 1).join("\n");
                code.lean = `${old_lean_head}
${error.filter(err => err.line == line).sort((a, b) => a.col - b.col).map(err => `/-\n${err.info}\n-/`).join("\n")}
${old_lean_tail}`;
                var codes = ranged(index[0] + 1).map(i => {
                    if (lemma[i].attribute) {
                        // lemma[i].attribute.remove('main');
                        lemma[i].attribute.clear();
                    }
                    var {name} = lemma[i];
                    var lemmaType;
                    if (name == 'main') {
                        lemma[i].name = module;
                        lemmaType = 'theorem';
                    }
                    else {
                        lemma[i].name = module + '.' + name.toLowerCase();
                        lemmaType = 'lemma';
                    }
                    return fetch_lemma(lemma[i], lemmaType);
                });
                var code = codes.join("\n\n");
                code = code.rtrim();
            }
            var [prequisite, ...imports] = await this.piece_together(`
SELECT
    _t.module,
    imports,
    open,
    def,
    lemma
FROM
    axiom.lemma as _t
    JOIN JSON_TABLE(
        ${JSON.stringify(this.submodules).mysqlStr()},
        '$[*]' COLUMNS (module text PATH '$')
    ) as jt using (module)`, true);
            if (imports.length) {
                if (imports.length > 1)
                    imports[imports.length - 1] += `\n\n-- The axioms above are actually lemmas proven to be true, with detailed proofs omitted here for simplicity. They are listed here to facilitate proving the current ${lemmaType}.`;
                else
                    imports[imports.length - 1] += `\n\n-- The axiom above is actually a lemma proven to be true, with detailed proofs omitted here for simplicity. It is listed here to facilitate proving the current ${lemmaType}.`;
            }
            prequisite = [prequisite, ...imports].join("\n\n");
            var has_intermediate_step = code.match(/^  -- (Goals? to prove: |Premises? given: )?\\\[[^\n]+\\\]$/m);
            if (has_intermediate_step) {
                var proven = errorIndex == -2 ? '' : 'partially proven ';
                var prelude = `Now You're given a ${proven}${lemmaType} where each intermediate proof-step is annotated with its latex representation indicating the tactic state:`;
            }
            else {
                var proven = errorIndex == -2 ? 'in question' : 'to prove';
                var prelude = `Below is the ${lemmaType} ${proven}:`;
            }
            if (prequisite)
                prelude = prequisite + "\n\n-- " + prelude;
            var task;
            if (errorIndex >= 0) {
                task = `At the line \`\`\`${old_leans[cursor_line]}\`\`\`, I got errors from Lean compilor which I wrapped in block comment /- and -/ below the code. Please fix the errors for me. Please don't duplicate my original code. In your final representation, give me only your newly added code which I can easily extract to replace the erroneous line.`;
                this.taskType = 'error';
            }
            else if (errorIndex == -2) {
                task = `The ${lemmaType} is already proven and verified by the lean compiler. Please add a docstring with about two sentences in between /-- -/ for the ${lemmaType} at the line specified above.\n**Note**: No need to prove the ${lemmaType} above and don't duplicate my original code.`;
                this.taskType = 'docstring';
            }
            else if (has_intermediate_step) {
                task = "Please complete the proof for me. If you can't solve the problem all at once, give me only the next proof-step that is workable and helpful for further problem-solving. Please don't duplicate my original code. In your final representation, give me only your newly added code which I can easily extract to replace the \`sorry\` tactic.`";
                this.taskType = 'proof';
            }
            else if (has_typeclasses(this.lemma[index[0]])) {
                task = "Please generate the proof to replace the \`sorry\` tactic. If you can't solve the problem all at once, give me only the next proof-step that is workable and helpful for further problem-solving.";
                this.taskType = 'proof';
            }
            else {
                task = "Please provide necessary typeclasses to make the code compile and generate the proof to replace the \`sorry\` tactic. If you can't solve the problem all at once, give me only the next proof-step that is workable and helpful for further problem-solving.";
                this.taskType = 'typeclass';
            }
            task = `
\`\`\`lean4
${prelude}
${code}
\`\`\`
${task}`;
            console.log(task);
            this.generate(
                [
                    {role: "system", content: "You are a helpful lean4 proof assistant."},
                    {role: "user", content: task}
                ],
                {
                    model: this.model,
                    index: [...index, 'think'],
                    id : module
                }
            );
            setitem(this.lemma, ...index, 'prompt', task);
        },

    	generate(prompt, kwargs) {
			var {onmessage, onclose} = this;
			var {model, id} = kwargs;
            var stream = {
                id,

                onmessage(message) {
                    onmessage(message, kwargs);
                },

                onerror(err) {
                    console.log(err);
                },

                onclose() {
                    onclose(kwargs);
                },
            };
			return generate(prompt, model, stream);
    	},

		postprocess(text, word, postprocess) {
            try {
                if (!text)
                word = word.ltrim();
                return postprocess(text, word);
            }
            catch (err) {
                console.log(err);
            }
		},

		onmessage(message, kwargs) {
			var {id, data} = message;
			var {index} = kwargs;
			if (id && data) {
				try{
					// console.log(data);
                    var think = {};
					var word = parse_token(data, think);
					if (word) {
						var {lemma} = this;
                        var content = getitem(lemma, ...index);
                        if (!think.reasoning_content) {
                            if (!this.think_closed && content.is_MarkdownText) {
                                word = '</think>' + word;
                                this.think_closed = true;
                            }
                        }
                        setitem(
                            lemma,
                            ...index,
                            this.postprocess(
                                content, 
                                word,
                                postprocess_word
                            )
                        );
                        if (!think.reasoning_content) {
                            index = [...index.slice(0, -1), 'final'];
                            setitem(
                                lemma,
                                ...index,
                                getitem(lemma, ...index) + word,
                            );
                        }
					}
                    else if (think.reasoning_content) {
                        word = think.reasoning_content;
						var {lemma} = this;
                        var content = getitem(lemma, ...index);
                        if (content && content.is_MarkdownCaret)
                            word = '<think>' + word;
                        setitem(
                            lemma,
                            ...index,
                            this.postprocess(
                                content, 
                                word,
                                postprocess_word
                            )
                        );
                    }
				}
				catch(err) {
					console.log(message);
					console.log(err);
				}
			}
		},

		async onclose(kwargs) {
			var {index} = kwargs;
            var {lemma} = this;
            this.postprocess(
                getitem(lemma, ...index), 
                "\n", // add newline at the end of the markdown text
                postprocess_char
            );
            index = [...index.slice(0, -1), 'final'];
            var final = getitem(lemma, ...index);
            console.log(final);
            switch (this.taskType) {
            case 'error':
                break;
            case 'docstring':
                var docstring = final.match(/(?<=^|\n)\/--([\s\S]*?)-\/(?=\n|$)/);
                if (docstring) {
                    docstring = docstring[1].trim("\n");
                    docstring = sbd(docstring).map(text => text.replace(/^\n+|\n+$/g, '')).join("\n");
                    console.log(docstring);
                    var i = index[0];
                    this.lemma[i].comment = docstring;
                }
                break;
            case 'proof':
                final = final.replace(/\/-.*?\n/g, '');
                break;
            case 'typeclass':
                break;
            }
		},

		keydown(event) {
			switch (event.key) {
			case 'F5':
				this.echo(this.module);
				event.preventDefault();
				break;
			}
		},

        select_span(span) {
            var range = document.createRange();
            range.selectNodeContents(span);
            var selection = window.getSelection();
            selection.removeAllRanges();
            selection.addRange(range);
        },

        focus(cm, line, start, stop, title) {
            if (title) {
                // Mark the text range and apply styling/title
                var tilde = '~'.repeat(stop - start);
                const mark = cm.markText(
                    { line, ch: start },
                    { line, ch: stop },
                    {
                        className: 'erroneous-text', // CSS class for styling
                        tilde,
                        title,                       // Tooltip text
                        attributes: { title, tilde } // Alternative for some setups
                    }
                );
                // cm.removeLineClass(line, "gutter", "panic");
                cm.addLineClass(line, "gutter", "panic");
            }
            else {
                cm.setCursor(line, start);
                cm.addSelection({ line, ch : start}, { line, ch: stop });
            }
            cm.focus();
        },

        openContainingFolder() {
            var search = location.search;
            var index = search.lastIndexOf('.');
            if (index < 0)
                index = search.lastIndexOf('/');
            ++index;
            // `search` will end with [./] to ensure it is a folder
            var hash = search.substring(index);
            if (hash)
                location.hash = hash;
            location.search = search.substring(0, index);
        },

        select(indices, line, col, title) {
            var cm = getitem(this.renderLean, ...indices);
            if (cm) {
                var cm = cm.editor;
                var text = cm.getLine(line);
                if (col) {
                    // determine the end of the code segment
                    form_post('php/request/segment_detection.php', {lean: text.slice(col)}).then(data => {
                        var {lean} = data;
                        var m = lean.match(/(.*?) *-- .*/);
                        if (m)
                            lean = m[1];
                        this.focus(cm, line, col, col + lean.length, title);
                    });
                }
                else
                    this.focus(cm, line, text.match(/^\s*/)[0].length, text.length, title);
                return true;
            }
        },

        line2indices(find) {
            find -= 1;
            var line = this.initial_line;
            var {def} = this;
            if (def) {
                for (let index of range(def.length)) {
                    line += 2;
                    // def function_name: (x : α) := ...
                    var line_def = line;
                    line += def[index].split("\n").length;
                    if (find < line)
                        return ['def', index, find - line_def];
                }
            }

            for (let index of range(this.lemma.length)) {
                line += 2;
                var lemma = this.lemma[index];
                if (lemma.comment) {
                    ++line;
                    if (find < line)
                        return [index, 'comment', null];
                }
                if (lemma.attribute) {
                    ++line; // @[main]
                    if (find < line)
                        return [index, 'attribute', null];
                }
                ++line; // private lemma main
                if (find < line)
                    return [index, 'name', null];
                var {instImplicit, strictImplicit, implicit, given, explicit} = lemma;
                if (instImplicit) {
                    // instImplicit: [Field α]
                    var line_instImplicit = line;
                    line += instImplicit.split("\n").length;
                    if (find < line)
                        return [index, 'instImplicit', find - line_instImplicit];
                }

                if (strictImplicit) {
                    // strictImplicit: ⦃x : α⦄
                    var line_strictImplicit = line;
                    line += strictImplicit.split("\n").length;
                    if (find < line)
                        return [index, 'strictImplicit', find - line_strictImplicit];
                }
                    
                if (implicit) {
                    // implicit: {x : α}
                    var line_implicit = line;
                    line += implicit.split("\n").length;
                    if (find < line)
                        return [index, 'implicit', find - line_implicit];
                }
                if (given) {
                    ++line; // --given
                    if (find < line)
                        return [index, 'given', null];
                    // given: (h : a = b)
                    for (var i of range(given.length)) {
                        var line_given = line; 
                        line += given[i].lean.split("\n").length;
                        if (find < line)
                            return [index, 'given', i, find - line_given];
                    }
                }
                if (explicit) {
                    // explicit: (left : Bool := false)
                    var line_explicit = line;
                    line += explicit.split("\n").length;
                    if (find < line)
                        return [index, 'explicit', find - line_explicit];
                }

                ++line; // -- imply
                if (find < line)
                    return [index, 'imply', null];
                
                var line_imply = line;
                line += lemma.imply.lean.split("\n").length;
                if (find < line)
                    return [index, 'imply', find - line_imply];

                ++line; // -- proof
                if (find < line)
                    return [index, 'proof', null];
                
                var {proof} = this.lemma[index];
                var attr = proof.by? 'by' : (proof.calc? 'calc' : null);
                proof = proof.by?? proof.calc?? proof;
                for (var i of range(proof.length)) {
                    var line_start = line;
                    var {lean, latex} = proof[i]
                    if (!lean) continue;
                    // if (!lean && latex) continue;
                    line += lean.split("\n").length;
                    // at this point, `line` is exact the line number of the `lean` code 
                    if (find < line) {
                        var offset = find - line_start;
                        if (attr)
                            return [index, 'proof', attr, i, offset];
                        else
                            return [index, 'proof', i, offset];
                    }
                }
            }

            line += 2;
            return ['date', find < line? 'created' : 'updated', null];
        },

        indices2line(indices) {
            var line = this.initial_line + 1;
            var [i, attr] = indices;
            const By = typeof indices[2] == 'string' ? indices[2] : null;
            const Index = By ? indices[3] : indices[2];
            var offset = By ? indices[4] : indices[3];
            if (offset)
                line += offset;
            for (let index of range(i + 1)) {
                line += 2;
                var lemma = this.lemma[index];
                if (lemma.comment) {
                    if (index == i && attr == 'comment')
                        return line;
                    ++line;
                }

                if (lemma.attribute) {
                    if (index == i && attr == 'attribute')
                        return line;
                    ++line; // @[main]
                }

                if (index == i && attr == 'name')
                    return line;
                ++line; // private lemma main
                var {instImplicit, strictImplicit, implicit, given, explicit} = lemma;
                if (instImplicit) {
                    if (index == i && attr == 'instImplicit')
                        return line;
                    // instImplicit: [Field α]
                    line += instImplicit.split("\n").length;
                }

                if (strictImplicit) {
                    if (index == i && attr == 'strictImplicit')
                        return line;
                    // strictImplicit: ⦃x : α⦄
                    line += strictImplicit.split("\n").length;
                }
                    
                if (implicit) {
                    if (index == i && attr == 'implicit')
                        return line;
                    // implicit: {x : α}
                    line += implicit.split("\n").length;
                }
                if (given) {
                    if (index == i && attr == 'given' && indices[2] == null)
                        return line;
                    ++line; // --given
                    // given: (h : a = b)
                    for (var j of range(given.length)) {
                        if (index == i && attr == 'given' && j == indices[2])
                            return line;
                        line += given[j].lean.split("\n").length;
                    }
                }
                if (explicit) {
                    // explicit: (left : Bool := false)
                    line += explicit.split("\n").length;
                    if (index == i && attr == 'explicit')
                        return line;
                }

                if (index == i && attr == 'imply' && indices.length == 3 && indices[2] == null)
                    return line;
                ++line; // -- imply

                if (index == i && attr == 'imply')
                    return line;
                line += lemma.imply.lean.split("\n").length;
                if (index == i && attr == 'proof' && indices[2] == null)
                    return line;
                ++line; // -- proof
                var {proof} = this.lemma[index];
                // var by = proof.by? 'by' : (proof.calc? 'calc' : null);
                proof = proof.by?? proof.calc?? proof;
                for (var j of range(proof.length)) {
                    if (index == i && j == Index)
                        return line;
                    var {lean} = proof[j];
                    if (lean)
                        line += lean.split("\n").length;
                }
            }

            if (indices[0] == this.lemma.length)
                line += 2;
            return line + 1;
        },

        *regexp2indices(regexp, match_comment, whole_word=true) {
            if (whole_word) {
                regexp = `\\b${regexp}\\b`;
                regexp = new RegExp(regexp);
            }
            for (let index of range(this.lemma.length)) {
                var lemma = this.lemma[index];

                var {instImplicit, strictImplicit, implicit, given, explicit} = lemma;
                if (instImplicit) {
                    // instImplicit: [Field α]
                    for (var [offset, line] of enumerate(instImplicit.split("\n"))) {
                        if (line.match(regexp))
                            yield [index, 'instImplicit', offset];
                    }
                }

                if (strictImplicit) {
                    // strictImplicit: ⦃x : α⦄
                    for (var [offset, line] of enumerate(strictImplicit.split("\n"))) {
                        if (line.match(regexp))
                            yield [index, 'strictImplicit', offset];
                    }
                }
                    
                if (implicit) {
                    // implicit: {x : α}
                    for (var [offset, line] of enumerate(implicit.split("\n"))) {
                        if (line.match(regexp))
                            yield [index, 'implicit', offset];
                    }
                }
                if (given) {
                    // given: (h : a = b)
                    for (var i of range(given.length)) {
                        for (var [offset, line] of enumerate(given[i].lean.split("\n"))) {
                            if (line.match(regexp))
                                yield [index, 'given', i, offset];
                        }
                    }
                }
                if (explicit) {
                    // explicit: (left : Bool := false)
                    for (var [offset, line] of enumerate(explicit.split("\n"))) {
                        if (line.match(regexp))
                            yield [index, 'explicit', offset];
                    }
                }

                for (var [offset, line] of enumerate(lemma.imply.lean.split("\n"))) {
                    if (line.match(regexp))
                        yield [index, 'imply', offset];
                }

                var {proof} = this.lemma[index];
                var attr = proof.by? 'by' : (proof.calc? 'calc' : null);
                proof = proof.by?? proof.calc?? proof;
                for (var i of range(proof.length)) {
                    for (var [offset, line] of enumerate(proof[i].lean.split("\n"))) {
                        if (line.match(regexp))
                            if (attr)
                                yield [index, 'proof', attr, i, offset];
                            else
                                yield [index, 'proof', i, offset];
                    }
                }
            }

            for (let index of range(this.lemma.length)) {
                var lemma = this.lemma[index];
                if (lemma.comment && match_comment) {
                    for (var [offset, line] of enumerate(lemma.comment.split("\n"))) {
                        if (line.match(regexp))
                            yield [index, 'comment', offset];
                    }
                }
            }
        },

        click_left,

        delete(indices) {
            var [index, attr] = indices;
            switch (attr) {
            case 'instImplicit':
                this.lemma[index].instImplicit = null;
                break;
            case 'strictImplicit':
                this.lemma[index].strictImplicit = null;
                break;
            case 'implicit':
                this.lemma[index].implicit = null;
                break;
            case 'given':
                var j = indices[2];
                this.lemma[index].given.delete(j);
                break;
            case 'explicit':
                this.lemma[index].explicit = null;
                break;
            case 'imply':
                this.lemma[index].imply = null;
                break;
            case 'proof':
                var proof = this.lemma[index].proof;
                if (indices.length == 4) {
                    proof = proof[indices[2]];
                    var i = indices[3];
                }
                else {
                    var i = indices[2];
                }
                proof.delete(i);
                break;
            }
        },

        async echo(module){
            var code = await form_post('php/request/echo.php', {module});
            console.log(JSON.stringify(code, null, "\t"));
            var {imports, open, set_option, def, lemma, error, date} = code;
            this.lemma.array_assign(lemma);
            this.error.array_assign(error);
            this.refresh = true;
            var {user} = this;
            var sql = `
replace into 
    axiom.lemma
    (user, module, imports, open, set_option, def, lemma, error, date) 
    values (
        '${user}',
        "${module}",
        ${JSON.stringify(imports).mysqlStr()},
        ${JSON.stringify(open).mysqlStr()},
        ${JSON.stringify(set_option).mysqlStr()},
        ${JSON.stringify(def).mysqlStr()},
        ${JSON.stringify(lemma).mysqlStr()},
        ${JSON.stringify(error).mysqlStr()},
        ${JSON.stringify(date).mysqlStr()}
    )
`;
            console.log(sql);
            form_post('php/request/execute.php', {sql}).then(rowcount => {
                console.log("rowcount =", rowcount);
            });
        },
    },
    
    directives: {
        finish :{
            mounted(el, binding){
            },
        },
    },
};

//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-clear
//http://docs.mathjax.org/en/latest/advanced/typeset.html
//http://docs.mathjax.org/en/latest/web/typeset.html#typeset-async
//http://docs.mathjax.org/en/latest/web/typeset.html#get-math-items
</script>

<style scoped>
.warning {
  color: #B5A642;
}

.error {
  color: red;
}

.error:hover {
  cursor: pointer;
}

[v-cloak] {
  display: none !important;
}

.bottom-line {
  width: auto;
  height: 50px;
  position: relative;
}

.bottom-line p.right {
  position: absolute;
  bottom: 0;
  right: 0;
}

.bottom-line p.left {
  position: absolute;
  bottom: 0;
  left: 0;
}

.pre-wrap {
  white-space: pre-wrap;
}

span.date {
  font-size: 12px;
}

div.lemma + div.lemma {
    /* add spaces between two consecutive tags of div.lemma */
    margin-top: 2em;
}

button.transparent {
	background-color: inherit;
	border-style: none;
	outline: none;
    font-size: 1.1em;
}

button.transparent:hover{
	background-color: red;
}

</style>
<style>

.erroneous-text {
  position: relative;
  display: inline-block;
}

.erroneous-text::after {
  content: attr(tilde);
  position: absolute;
  bottom: -9px; /* Adjust vertical position */
  left: 0;
  width: 100%; /* Match parent width */
  white-space: nowrap; /* Keep tildes in single line */
  overflow: hidden; /* Hide excess tildes */
  letter-spacing: 1px; /* Adjust spacing between tildes */
  color: red;
}

.panic {
  position: relative;
}

.panic:before{
	width: 4px;
	height: 1.5px;
	position: absolute;
	left: 0px;
	top: 11.5px;
	content: "";
	transform: rotate(-45deg);
	background: red;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}
    
.panic:after {
	width: 6px;
	height: 6px;
	position: absolute;
	left: 2.3px;
	top: 6px;
	content: "";
	background: red;
	border-radius: 50%;
	box-shadow: 1px 1px 0 0 #9da0a0;
	z-index: 0;
}

</style>