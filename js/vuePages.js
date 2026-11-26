/**
 * Precompiled Vue pages. The browser loads this bundle instead of
 * compiling `.vue` files in the browser.
 * Each page is its own chunk. `createApp` loads the one the route asks for.
 */
import * as Vue from "vue";
// The search page is the landing route, so its chunk starts with this file.
import "../vue/searchResult.vue";

const loaders = import.meta.glob("../vue/*.vue");
const pages = {};
for (const [file, load] of Object.entries(loaders)) {
	const name = file.slice(file.lastIndexOf("/") + 1, -4);
	pages[name] = load;
}

window.Vue = Vue;
window.__vuePages = pages;
window.__loadVueComponent = async function (name) {
	const load = pages[name];
	if (!load)
		throw new Error("Unknown Vue component: " + name);
	return load();
};
