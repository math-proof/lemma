import { installCodeMirrorExtras } from './codemirror.js';
const CM_MODULE_PATHS = [
	'node_modules/codemirror/lib/codemirror.js',
	'js/codemirror-lean.js',
	'node_modules/codemirror/addon/selection/active-line.js',
	'node_modules/codemirror/addon/hint/show-hint.js',
	'node_modules/codemirror/addon/edit/matchbrackets.js',
	'node_modules/codemirror/addon/comment/comment.js',
];

export function preloadCodeMirror() {
	if (!window.__cmReady) {
		const base = document.baseURI;
		const importFrom = (p) => import(new URL(p, base).href);
		window.__cmReady = importFrom(CM_MODULE_PATHS[0]).then(() => {
			installCodeMirrorExtras();
			return Promise.all(CM_MODULE_PATHS.slice(1).map(importFrom));
		}).catch((err) => {
			console.error('[codemirrorBoot] failed to load CodeMirror', err);
			throw err;
		});
	}
	return window.__cmReady;
}

preloadCodeMirror();
