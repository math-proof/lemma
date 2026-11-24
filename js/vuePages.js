/**
 * Precompiled Vue pages. The browser loads this bundle instead of
 * compiling `.vue` files with vue3-sfc-loader.
 */
import * as Vue from "vue";

const modules = import.meta.glob("../vue/*.vue", { eager: true });
const pages = {};
for (const [file, mod] of Object.entries(modules)) {
	const name = file.slice(file.lastIndexOf("/") + 1, -4);
	pages[name] = mod.default;
}

window.Vue = Vue;
window.__vuePages = pages;
window.__loadVueComponent = async function (name) {
	const comp = pages[name];
	if (!comp)
		throw new Error("Unknown Vue component: " + name);
	return { default: comp };
};
