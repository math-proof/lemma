import { ref, computed, watch, nextTick, getCurrentInstance, onMounted, onUnmounted, defineAsyncComponent, unref, isRef } from 'vue'


class Component {
	defineProperty(data, key, $emit = null) {
		var attributes = $emit?
			{
				get() {
					return data[key];
				},
				set(value) {
					$emit(`update:${key}`, value);
				},
			} :
			{
				get() {
					return unref(data[key]);
				},
				set(value) {
					const slot = data[key];
					if (isRef(slot))
						slot.value = value;
				},
			};
		attributes.enumerable = true;
		attributes.configurable = true;
		Object.defineProperty(this, key, attributes);
	}
}

class Parent extends Component {
	constructor(instance = null) {
		super();
		// fetch exposed data from Vue.prototype.defineExpose() on parent chain
		this.$$instance = instance;
		const exposed = instance?.exposed || {};
		for (let key in exposed) {
			this.defineProperty(exposed, key);
		}
		// Options-API root: $data lives on proxy, not in exposed. Skip if defineExpose already set $data.
		const proxy = instance?.proxy;
		if (proxy && proxy.$data != null && !('$data' in exposed)) {
			Object.defineProperty(this, '$data', {
				enumerable: true,
				configurable: true,
				get() {
					return proxy.$data;
				},
			});
		}
	}

	get $parent() {
		if (!this.$$parent) {
			const parentInstance = this.$$instance?.parent || null;
			this.$$parent = parentInstance ? new Parent(parentInstance) : null;
		}
		return this.$$parent;
	}

	get $root() {
		let node = this;
		while (node && node.$parent) {
			node = node.$parent;
		}
		return node || this;
	}
}

class Vue extends Component {
	constructor(vue) {
		super();
		const instance = this.$$instance = getCurrentInstance();
		let {
			data,
			$refs,
			computed: $computed,
			props,
			$emit,
			directives,
			components,
			mounted,
			unmounted,
			created,
			methods: $methods,
			watch: $watch,
		} = vue;
		if (props) {
			var emit = $emit?? ((event, value) => {
				console.log(`emit ${event} = ${value} is not defined`);
			});
			for (const key in props) {
				this.defineProperty(props, key, emit);
			}
			this.$props = props;
		}
		if (typeof data === 'function') {
			data = data.call(this);
		}
		var $data = null;
		if ($refs) {
			var keys = Object.keys($refs);
			for (const key of keys) {
				$refs[key] = ref($refs[key]);
			}
			this.$refs = $refs;
			const mountedCounters = Object.fromEntries(keys.map((k) => [k, 0]));
			if (data) {
				data.$mounted = mountedCounters;
				$data = data;
			} else {
				$data = { $mounted: mountedCounters };
			}

			let computed_ref = {};
			for (const key of keys) {
				if ($computed && key in $computed) {
					console.warn(`[Vue] computed.${key} is already defined`);
					continue;
				}
				computed_ref[key] = function refMountedHost() {
					return this.$mounted[key] ? this.$refs[key].value : {};
				};
			}
			if ($computed) {
				Object.assign($computed, computed_ref);
			} else {
				$computed = computed_ref;
			}
		}
		else {
			$data = data;
		}

		if ($data) {
			for (const key in $data) {
				$data[key] = ref($data[key]);
				this.defineProperty($data, key);
			}
			this.$data = $data;
		}

		if ($computed) {
			for (const key in $computed) {
				const definition = $computed[key];
				if (typeof definition === "function") {
					$computed[key] = computed(() => definition.call(this));
				} else if (definition && typeof definition === "object") {
					const getter = definition.get;
					const setter = definition.set;
					if (typeof getter !== "function") {
						throw new Error(`computed.${key} requires a get() function`);
					}
					if (typeof setter === "function") {
						$computed[key] = computed({
							get: () => getter.call(this),
							set: (value) => setter.call(this, value),
						});
					} else {
						$computed[key] = computed(() => getter.call(this));
					}
				} else {
					throw new Error(`computed.${key} must be a function or {get,set} object`);
				}
				this.defineProperty($computed, key);
			}
			this.$computed = $computed;
		}
		if ($watch) {
			for (const key in $watch) {
				const definition = $watch[key];
				const getter = key.includes('.')
					? function () {
						let v = this;
						for (const k of key.split('.')) v = v?.[k];
						return v;
					}
					: function () { return this[key]; };
				const opts = typeof definition === 'object' && definition !== null && !Array.isArray(definition)
					? { deep: !!definition.deep, immediate: !!definition.immediate }
					: {};
				const handler = typeof definition === 'function'
					? definition
					: definition?.handler;
				if (typeof handler !== 'function') continue;
				watch(getter.bind(this), (newVal, oldVal) => handler.call(this, newVal, oldVal), opts);
			}
		}
		// Handle directives registration
		if (directives) {
			if (instance) {
				// Merge the component's existing directives with new ones
				instance.type.directives = {
					...(instance.type.directives || {}),
					...directives,
				};
			}
		}
		if (components) {
			// std.js: Array.prototype.isArray = true -- only array-of-names is supported here.
			console.assert(components.isArray, 'components must be an array of .vue base names');
			const resolved = components.reduce((acc, name) => {
				acc[name] = defineAsyncComponent(() => import(`../components/${name}.vue`));
				return acc;
			}, {});
			this.components = resolved;
			if (instance) {
				instance.type.components = {
					...(instance.type.components || {}),
					...resolved,
				};
			}
		}
		const __name = instance?.type?.__name;
		if (__name) {
			onMounted(() => {
				var { $mounted } = this.$parent;
				if ($mounted && __name in $mounted)
					$mounted[__name] = 1;
			});
		}
		if (mounted) {
			onMounted(() => {
				mounted.call(this);
			});
		}
		if (unmounted) {
			onUnmounted(() => {
				unmounted.call(this);
			});
		}
		if (__name) {
			onUnmounted(() => {
				var { $mounted } = this.$parent;
				if ($mounted && __name in $mounted)
					$mounted[__name] = 0;
			});
		}
		if ($methods) {
			for (const key in $methods) {
				if (key in this) {
					console.warn(`[Vue] method "${key}" collides with existing property; skipping method binding.`);
					continue;
				}
				this[key] = $methods[key] = $methods[key].bind(this);
			}
			this.$methods = $methods;
		}
		this.$nextTick = (cb) => {
			if (typeof cb === 'function')
				return nextTick(() => cb.call(this));
			return nextTick();
		};
		if ($emit)
			this.$emit = $emit;
		if (created)
			created.call(this);
		this.defineExpose();
	}

	/** Mirror former `defineExpose(self.$expose)` in SFCs: publish bindings for `this.$parent`. */
	defineExpose() {
		const instance = this.$$instance;
		if (instance == null) return;
		const exposed = {};
		const props = this.$props;
		if (props) {
			for (const key in props)
				exposed[key] = props[key];
		}
		if (this.$refs != null)
			exposed.$refs = this.$refs;
		const $data = this.$data;
		if ($data) {
			for (const key in $data)
				exposed[key] = $data[key];
			exposed.$data = $data;
		}
		const $computed = this.$computed;
		if ($computed) {
			for (const key in $computed)
				exposed[key] = $computed[key];
		}
		const $methods = this.$methods;
		if ($methods) {
			for (const key in $methods)
				exposed[key] = $methods[key];
		}
		exposed.$nextTick = this.$nextTick;
		if (this.$emit)
			exposed.$emit = this.$emit; // allow this.$parent.$emit(...) to work
		instance.exposed = exposed;
	}

	get $parent() {
		if (!this.$$parent) {
			const parentInstance = this.$$instance?.parent || null;
			this.$$parent = parentInstance ? new Parent(parentInstance) : null;
		}
		return this.$$parent;
	}

	get $root() {
		if (!this.$$root) {
			let node = this;
			while (node && node.$parent) {
				node = node.$parent;
			}
			this.$$root = node || this;
		}
		return this.$$root;
	}

	get $el() {
		const inst = this.$$instance;
		if (!inst) return undefined;
		return inst.proxy?.$el;
	}

	get globals() {
		const globals = {};
		for (const source of ['$data', '$computed', '$methods']) {
			const obj = this[source];
			if (obj) {
				for (const key in obj) {
					if (this.$props && key in this.$props) {
						console.warn(`[Vue.globals] ATTENTION: "${key}" is also declared in $props -- overlap between props and ${source} will confuse bindings; rename one of them.`);
					}
					if (key in globals) {
						console.warn(`[Vue.globals] name collision on "${key}" from ${source}`);
						continue;
					}
					globals[key] = obj[key];
				}
			}
		}
		globals.$refs = this.$refs;
		return globals;
	}
}

console.log('import vue.js');

export default Vue;
