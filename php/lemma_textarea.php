<?php
$text = str_replace("\r", '', file_get_contents($leanFile));
?>
<title><?php echo htmlspecialchars($title, ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8'); ?></title>
<body>
<pre id="lemma-shell" style="width:100%;height:92vh;box-sizing:border-box;margin:0;font-family:monospace;font-size:14px;line-height:1.4;border:1px solid #ccc;padding:8px;overflow:auto;white-space:pre-wrap"><?php
echo htmlspecialchars($text, ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8');
?></pre>
</body>
<script type="module">
function asset(path) {
	return new URL(path, document.baseURI).href;
}

function loadScript(src) {
	return new Promise((resolve, reject) => {
		if ([...document.scripts].some((s) => s.src === src))
			return resolve();
		const s = document.createElement('script');
		s.src = src;
		s.onload = () => resolve();
		s.onerror = () => reject(new Error(`script failed: ${src}`));
		document.head.appendChild(s);
	});
}

function loadCss(href) {
	return new Promise((resolve, reject) => {
		if ([...document.styleSheets].some((sheet) => sheet.href === href))
			return resolve();
		if ([...document.querySelectorAll('link[rel="stylesheet"]')].some((l) => l.href === href))
			return resolve();
		const l = document.createElement('link');
		l.rel = 'stylesheet';
		l.href = href;
		l.onload = () => resolve();
		l.onerror = () => reject(new Error(`stylesheet failed: ${href}`));
		document.head.appendChild(l);
	});
}

const VUE_STYLES = [
	'static/codemirror/lib/codemirror.css',
	'static/codemirror/theme/eclipse.css',
	'static/codemirror/addon/hint/show-hint.css',
	'static/unpkg.com/katex@0.16.21/dist/katex.min.css',
	'static/unpkg.com/prismjs@1.30.0/themes/prism.min.css',
];

const VUE_SCRIPTS = [
	'static/unpkg.com/axios@0.24.0/dist/axios.min.js',
	'static/unpkg.com/qs@6.10.2/dist/qs.js',
	'static/unpkg.com/clipboard@2.0.11/dist/clipboard.min.js',
	'static/unpkg.com/file-saver@2.0.5/dist/FileSaver.min.js',
	'static/unpkg.com/vue@3.5.13/dist/vue.global.prod.js',
	'static/unpkg.com/vue3-sfc-loader@0.9.5/dist/vue3-sfc-loader.js',
	'static/js/std.js',
];

const VUE_DEFER_SCRIPTS = [
	'static/unpkg.com/lz-string@1.5.0/libs/lz-string.js',
	'static/unpkg.com/katex@0.16.21/dist/katex.min.js',
	'static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js',
	'static/unpkg.com/prismjs@1.30.0/prism.js',
	'static/unpkg.com/prismjs@1.30.0/components/prism-lean.js',
];

async function upgradeLemmaVue(module) {
	for (const path of VUE_STYLES)
		await loadCss(asset(path));

	for (const path of VUE_SCRIPTS)
		await loadScript(asset(path));

	await Promise.all([
		import(asset('static/js/utility.js')),
		import(asset('static/js/codemirrorBoot.js')),
	]);

	await Promise.all(VUE_DEFER_SCRIPTS.map((path) => loadScript(asset(path))));

	const res = await fetch(asset(`php/request/lemma_payload.php?module=${encodeURIComponent(module)}`));
	if (!res.ok)
		throw new Error(`lemma payload HTTP ${res.status}`);
	const code = await res.json();
	if (typeof code?.error === 'string' && code.error)
		throw new Error(code.error);

	document.body.replaceChildren();
	await createApp('render', code);
}

// const module = <?php echo json_encode($module, JSON_UNESCAPED_UNICODE); ?>;
// const run = () => upgradeLemmaVue(module).catch((err) => console.error('[upgradeLemmaVue]', err));
// if ('requestIdleCallback' in window)
// 	requestIdleCallback(run, { timeout: 2000 });
// else
// 	setTimeout(run, 0);
</script>
