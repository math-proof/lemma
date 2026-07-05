const CM_MODULE_PATHS = [
	'static/codemirror/lib/codemirror.js',
	'static/codemirror/mode/lean/lean.js',
	'static/codemirror/addon/selection/active-line.js',
	'static/codemirror/addon/hint/show-hint.js',
	'static/codemirror/addon/edit/matchbrackets.js',
	'static/codemirror/addon/comment/comment.js',
];

export function preloadCodeMirror() {
	if (!window.__cmReady) {
		const base = document.baseURI;
		const importFrom = (p) => import(new URL(p, base).href);
		window.__cmReady = importFrom(CM_MODULE_PATHS[0]).then(() =>
			Promise.all(CM_MODULE_PATHS.slice(1).map(importFrom))
		).catch((err) => {
			console.error('[codemirrorBoot] failed to load CodeMirror', err);
			throw err;
		});
	}
	return window.__cmReady;
}

preloadCodeMirror();
