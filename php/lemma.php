<?php
require_once 'init.php';
require_once 'std.php';

function lemma_shell_h(?string $s): string
{
    return htmlspecialchars($s ?? '', ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8');
}

function lemma_shell_unindent_decl(?string $text): ?string
{
    if ($text === null || $text === '')
        return $text;
    return preg_replace('/^  /m', '', $text);
}

/** Match renderLean.vue CodeMirror theme "eclipse indent" (.cm-s-indent). */
function lemma_shell_render_lean_line(?string $text, bool $indent = false): void
{
    if ($text === null || $text === '')
        return;
    $class = 'lean-line Consolas' . ($indent ? ' lean-line-indent' : '');
    echo '<pre class="', $class, '">', lemma_shell_h($text), "</pre>\n";
}

function lemma_shell_render_latex_block(?string $latex): void
{
    if ($latex === null || $latex === '')
        return;
    echo '<p class="latex-block">', lemma_shell_h($latex), "</p>\n";
}

/** Extract proposition identifier from trailing \\tag*{...} (e.g. $h$ → h). */
function lemma_shell_extract_latex_tag(string $latex): ?string
{
    if (!preg_match('/\\\\tag\*\{([^}]*)\}$/', $latex, $m))
        return null;
    $tag = $m[1];
    if (preg_match('/^\$([^$]+)\$$/', $tag, $inner))
        return $inner[1];
    return ltrim($tag);
}

function lemma_shell_tag_from_lean(?string $lean): ?string
{
    if ($lean && preg_match('/^\(([^:]+)\s*:/', trim($lean), $m))
        return trim($m[1]);
    return null;
}

function lemma_shell_render_latex_tag(?string $tag): void
{
    if ($tag === null || $tag === '')
        return;
    echo '<span class="latex-tag">', lemma_shell_h($tag), '</span>';
}

function lemma_shell_codecogs_url(string $latex): string
{
    return 'https://latex.codecogs.com/png.latex?' . rawurlencode($latex);
}

/** Strip project-specific LaTeX wrappers so CodeCogs can parse the math. */
function lemma_shell_simplify_latex_for_codecogs(string $latex): string
{
    $latex = preg_replace('/\\\\tag\*\{[^}]*\}$/', '', $latex);
    $latex = preg_replace('/\\\\color\{[^{}]+\}\s*/', '', $latex);
    while (preg_match('/\\\\colorbox\{[^{}]+\}\{\$\\\\mathord\{(.+?)\}\$\}/s', $latex, $m, PREG_OFFSET_CAPTURE)) {
        $start = $m[0][1];
        $len = strlen($m[0][0]);
        $latex = substr($latex, 0, $start) . $m[1][0] . substr($latex, $start + $len);
    }
    $latex = preg_replace('/\{([a-zA-Z0-9_\']+)\}/', '$1', $latex);
    $latex = str_replace(['\\lt', '\\gt'], ['<', '>'], $latex);
    return trim($latex);
}

function lemma_shell_wrap_for_codecogs(string $latex): string
{
    if ($latex === '')
        return '';
    if (strlen($latex) > 60 || str_contains($latex, '=') || str_contains($latex, '\\left'))
        return '\\displaystyle ' . $latex;
    return '$' . $latex . '$';
}

/** Render given/imply: insert → lean; else latex → CodeCogs PNG (temporary KaTeX substitute). */
function lemma_shell_render_given_or_imply(?array $pair): void
{
    if (!is_array($pair))
        return;
    $lean = $pair['lean'] ?? null;
    $latex = $pair['latex'] ?? null;
    if (!empty($pair['insert'])) {
        lemma_shell_render_lean_line(lemma_shell_unindent_decl($lean), true);
        return;
    }
    if ($latex !== null && $latex !== '') {
        $simplified = lemma_shell_simplify_latex_for_codecogs($latex);
        $wrapped = lemma_shell_wrap_for_codecogs($simplified);
        if ($wrapped !== '') {
            $url = lemma_shell_codecogs_url($wrapped);
            if (strlen($url) <= 7000) {
                $tag = lemma_shell_extract_latex_tag($latex) ?? lemma_shell_tag_from_lean($lean);
                echo '<div class="latex-display"><span class="latex-body"><img class="latex-formula" src="', lemma_shell_h($url),
                    '" alt="', lemma_shell_h($lean ?? ''), '" loading="lazy" decoding="async"',
                    ' onerror="this.closest(\'.latex-display\').classList.add(\'latex-formula-failed\')">',
                    '<pre class="lean-line lean-fallback Consolas">',
                    lemma_shell_h($lean ?? ''), '</pre></span>';
                lemma_shell_render_latex_tag($tag);
                echo "</div>\n";
                return;
            }
        }
    }
    lemma_shell_render_decl_line($lean);
}

function lemma_shell_render_decl_line(?string $text): void
{
    lemma_shell_render_lean_line(lemma_shell_unindent_decl($text), true);
}

function lemma_shell_render_proof_line(?array $line): void
{
    if (!is_array($line))
        return;
    lemma_shell_render_lean_line(lemma_shell_unindent_decl($line['lean'] ?? null), true);
    lemma_shell_render_latex_block($line['latex'] ?? null);
}

function lemma_shell_render_lemma(array $lemma, string $module): void
{
    $comment = $lemma['comment'] ?? null;
    $attribute = $lemma['attribute'] ?? null;
    $accessibility = $lemma['accessibility'] ?? null;
    $name = $lemma['name'] ?? 'main';
    $instImplicit = $lemma['instImplicit'] ?? null;
    $strictImplicit = $lemma['strictImplicit'] ?? null;
    $implicit = $lemma['implicit'] ?? null;
    $explicit = $lemma['explicit'] ?? null;
    $given = $lemma['given'] ?? null;
    $default = $lemma['default'] ?? null;
    $imply = $lemma['imply'] ?? null;
    $proof = $lemma['proof'] ?? null;

    echo '<div class="lemma">' . "\n";

    if ($comment) {
        echo '<span class="green">/--</span><br>' . "\n";
        echo '<div class="lemma-comment"><pre class="green Consolas">', lemma_shell_h($comment), "</pre></div>\n";
        echo '<span class="green">-/</span><br>' . "\n";
    }

    if (is_array($attribute) && $attribute) {
        $parts = array_map('lemma_shell_h', $attribute);
        echo '<span class="lemma-attribute-area"><span class="orange">@[</span>';
        echo '<span class="blue">', implode('</span><span class="orange">, </span><span class="blue">', $parts), '</span>';
        echo '<span class="orange">]</span></span><br>' . "\n";
    }

    if ($accessibility)
        echo '<span class="blue">', lemma_shell_h($accessibility), '</span> ';

    echo '<span class="blue">lemma</span> <span class="orange">', lemma_shell_h($name), '</span>';

    $has_decl = $instImplicit || $strictImplicit || $implicit || $explicit || $given || $default;
    if (!$has_decl)
        echo ' :';
    echo '<br>' . "\n";

    if ($instImplicit)
        lemma_shell_render_decl_line($given || $explicit || $strictImplicit || $implicit ? $instImplicit : $instImplicit . ' :');
    if ($strictImplicit)
        lemma_shell_render_decl_line($given || $explicit || $implicit ? $strictImplicit : $strictImplicit . ' :');
    if ($implicit)
        lemma_shell_render_decl_line($given || $explicit ? $implicit : $implicit . ' :');

    if ($explicit || $given || $default) {
        echo "<hr>\n<span class=\"green\"><b>-- given</b></span><br>\n";
        if ($explicit)
            lemma_shell_render_decl_line($explicit);
        if (is_array($given)) {
            foreach ($given as $item)
                lemma_shell_render_given_or_imply($item);
        }
        if ($default)
            lemma_shell_render_decl_line($default);
    }

    echo "<hr>\n<span class=\"green\"><b>-- imply</b></span><br>\n";
    if (is_array($imply))
        lemma_shell_render_given_or_imply($imply);
    elseif ($imply)
        lemma_shell_render_decl_line($imply);

    if (is_array($proof)) {
        $by = $proof['by'] ?? null;
        $calc = $proof['calc'] ?? null;
        $lines = is_array($by) ? $by : (is_array($calc) ? $calc : (is_array($proof) && array_is_list($proof) ? $proof : null));
        if ($lines) {
            echo "<hr>\n<span class=\"green\"><b>-- proof</b></span><br>\n";
            foreach ($lines as $line)
                lemma_shell_render_proof_line($line);
        }
    }

    echo "</div>\n";
}

$code = fetch_from_mysql(get_project_name(), $module);
if ($code) {
    $code['imports'] = std\decode($code['imports']);
    $code['open'] = std\decode($code['open']);
    $code['def'] = std\decode($code['def']);
    $code['lemma'] = std\decode($code['lemma']);
    $code['error'] = std\decode($code['error']);
    $code['date'] = std\decode($code['date']);
}

if (!$code || !$code['lemma'] || !$code['date']) {
    if (!is_readable($leanFile))
        $code = null;
    else {
        $leanCode = compile(file_get_contents($leanFile));
        $code = $leanCode->render2vue(false);
    }
}

if ($code)
    $code['module'] = $module;
?>
<title><?php echo lemma_shell_h($title); ?></title>
<style>
#lemma-shell { margin-left: 1.5em; }
.lemma { margin-bottom: 1.5em; font-family: Consolas, monospace; font-size: 1em; }
.lean-line { margin: 0.25em 0; white-space: pre-wrap; background: transparent; border: none; padding: 0; }
.lean-line-indent { margin-left: 0.9em; }
.latex-block { margin: 0.25em 0 0.5em 1em; white-space: pre-wrap; }
.latex-display {
    position: relative;
    display: flex;
    align-items: center;
    justify-content: center;
    margin: 0.35em 0 0.5em 0;
    min-height: 1.6em;
    width: 100%;
}
.latex-display .latex-body { flex: 0 1 auto; text-align: center; }
.latex-display img.latex-formula { max-width: 100%; height: auto; vertical-align: middle; }
.latex-display .latex-tag {
    position: absolute;
    right: 0;
    top: 50%;
    transform: translateY(-50%);
    font-family: "KaTeX_Main", "Times New Roman", serif;
    font-style: italic;
    font-size: 1em;
    line-height: 1;
    white-space: nowrap;
}
.latex-display.latex-formula-failed img.latex-formula { display: none; }
.latex-display.latex-formula-failed { justify-content: flex-start; }
.latex-display.latex-formula-failed .latex-body { flex: 0 1 auto; text-align: left; }
.latex-display.latex-formula-failed .latex-tag { position: static; transform: none; margin-left: auto; }
.latex-display .lean-fallback { display: none; margin: 0; }
.latex-display.latex-formula-failed .lean-fallback { display: block; }
#lemma-shell.lemma-shell-fade-out {
	opacity: 0;
	transition: opacity 0.35s ease;
	pointer-events: none;
}
#lemma-vue-root {
	transition: opacity 0.35s ease;
}
#lemma-vue-root.lemma-vue-pending {
	opacity: 0;
}
#lemma-vue-root.lemma-vue-visible {
	opacity: 1;
}
.green { color: green; }
.blue { color: blue; }
.orange { color: orange; }
.bottom-line {
    width: auto;
    height: 50px;
    position: relative;
    margin-top: 2em;
}
.bottom-line p.right {
    position: absolute;
    bottom: 0;
    right: 0;
    margin: 0;
}
span.date {
    font-size: 12px;
}
#lemma-stage { position: relative; }
#lemma-vue-root.lemma-vue-overlay {
    position: absolute;
    left: 0;
    right: 0;
    top: 0;
    z-index: 1;
}
</style>
<body>
<div id="lemma-stage">
<div id="lemma-shell">
<?php
if ($code && !empty($code['lemma'])) {
    if (!empty($code['def']) && is_array($code['def'])) {
        foreach ($code['def'] as $def)
            if (is_string($def) && $def !== '')
                lemma_shell_render_lean_line($def);
    }
    foreach ($code['lemma'] as $lemma) {
        if (is_array($lemma))
            lemma_shell_render_lemma($lemma, $module);
    }
    $date = $code['date'] ?? [];
    if (!empty($date['created']) || !empty($date['updated'])) {
        echo '<div class="bottom-line"><p class="right">';
        if (!empty($date['created']))
            echo '<span class="date">Created on ', lemma_shell_h($date['created']), '</span>';
        if (!empty($date['updated'])) {
            if (!empty($date['created']))
                echo '<br>';
            echo '<span class="date">Updated on ', lemma_shell_h($date['updated']), '</span>';
        }
        echo "</p></div>\n";
    }
} else {
    echo '<p>', lemma_shell_h("No lemma data in MySQL for module: $module"), "</p>\n";
}
?>
</div>
</div>
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

async function upgradeLemmaVue(code) {
	for (const path of VUE_STYLES)
		await loadCss(asset(path));

	for (const path of VUE_SCRIPTS)
		await loadScript(asset(path));

	await Promise.all([
		import(asset('static/js/utility.js')),
		import(asset('static/js/codemirrorBoot.js')),
	]);

	await Promise.all(VUE_DEFER_SCRIPTS.map((path) => loadScript(asset(path))));

	const shell = document.getElementById('lemma-shell');
	const stage = document.getElementById('lemma-stage');
	const mountId = 'lemma-vue-root';
	await createApp('render', code, mountId);

	const mount = document.getElementById(mountId);
	if (mount)
		mount.classList.add('lemma-vue-pending');
	if (stage && mount)
		stage.appendChild(mount);

	await new Promise((resolve) => requestAnimationFrame(() => requestAnimationFrame(resolve)));

	if (shell && stage)
		stage.style.minHeight = shell.offsetHeight + 'px';
	if (mount) {
		mount.classList.remove('lemma-vue-pending');
		mount.classList.add('lemma-vue-overlay');
		mount.classList.add('lemma-vue-visible');
	}

	const finish = () => {
		if (finish.done)
			return;
		finish.done = true;
		if (shell)
			shell.remove();
		if (stage)
			stage.style.minHeight = '';
		if (mount)
			mount.classList.remove('lemma-vue-overlay', 'lemma-vue-pending', 'lemma-vue-visible');
	};

	if (shell) {
		shell.classList.add('lemma-shell-fade-out');
		shell.addEventListener('transitionend', finish, { once: true });
		setTimeout(finish, 450);
	} else
		finish();
}

const lemmaCode = <?php echo $code ? std\encode($code) : 'null'; ?>;
const run = () => {
	if (!lemmaCode?.lemma)
		return;
	upgradeLemmaVue(lemmaCode).catch((err) => console.error('[upgradeLemmaVue]', err));
};
if ('requestIdleCallback' in window)
	requestIdleCallback(run, { timeout: 2000 });
else
	setTimeout(run, 0);
</script>
