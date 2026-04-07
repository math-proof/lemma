import { ref, computed, watch, nextTick, getCurrentInstance, onMounted, onUnmounted, defineAsyncComponent } from 'vue'


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
			}:
			{
				get() {
					return data[key].value;
				},
				set(value) {
					data[key].value = value;
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
		// fetch exposed data from defineExpose(self.$expose) on parent chain
		this.$$instance = instance;
		const exposed = instance?.exposed || {};
		for (let key in exposed) {
			this.defineProperty(exposed, key);
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
		this.$$instance = getCurrentInstance();
		const {data, $refs, computed: $computed, props, $emit, directives, components, mounted, unmounted, created, methods : $methods, watch: $watch} = vue;
		var $expose = {};
		if (props) {
			var emit = $emit?? ((event, value) => {
				console.log(`emit ${event} = ${value} is not defined`);
			});
			const $props = {};
			for (const key in props) {
				$props[key] = props[key];
				this.defineProperty($props, key, emit);
				$expose[key] = $props[key];
			}
			this.$props = $props;
		}
		if (data) {
			const $data = {};
			for (const key in data) {
				$data[key] = ref(data[key]);
				this.defineProperty($data, key);
				$expose[key] = $data[key];
			}
			$expose['$data'] = this.$data = $data;
		}
		if ($refs) {
			for (const key in $refs) {
				$refs[key] = ref($refs[key]);
				this.defineProperty($refs, key);
			}
			$expose['$refs'] = this.$refs = $refs;
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
				$expose[key] = $computed[key];
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
			const instance = this.$$instance;
			if (instance) {
				// Merge the component's existing directives with new ones
				instance.type.directives = {
					...(instance.type.directives || {}),
					...directives,
				};
			}
		}
		if (components) {
			this.components = components.isArray?
				components.reduce((acc, name) => {
					acc[name] = (name => defineAsyncComponent(() => import(`../components/${name}.vue`)))(name);
					return acc;
				}, {}) :
				components;
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
		if ($methods) {
			for (const key in $methods) {
				if (key in this) {
					console.warn(`[Vue] method "${key}" collides with existing property; skipping method binding.`);
					continue;
				}
				$expose[key] = this[key] = $methods[key] = $methods[key].bind(this);
			}
			this.$methods = $methods;
		}
		this.$nextTick = (cb) => {
			if (typeof cb === 'function')
				return nextTick(() => cb.call(this));
			return nextTick();
		};
		$expose['$nextTick'] = this.$nextTick;
		this.$expose = $expose;
		if (created)
			created.call(this);
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

	get globals() {
		const globals = {};
		for (const source of ['$data', '$computed', '$methods']) {
			const obj = this[source];
			if (obj) {
				for (const key in obj) {
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
