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

/**
 * Trailing \\tag{...} / \\tag*{...} (KaTeX / this printer).
 * Body may be $h$,  := by, or one nested {...}.
 */
function lemma_shell_latex_tag_re(): string
{
    return '/\\\\tag\*?\{((?:[^{}]|\{[^{}]*\})*)\}\s*$/';
}

/** Matching `}` for `{` at $open; skip `\{` / `\}`. */
function lemma_shell_latex_match_brace(string $s, int $open): ?int
{
    if (($s[$open] ?? '') !== '{')
        return null;
    $depth = 0;
    $len = strlen($s);
    for ($i = $open; $i < $len; $i++) {
        $c = $s[$i];
        if ($c === '\\') {
            $i++;
            continue;
        }
        if ($c === '{')
            $depth++;
        elseif ($c === '}') {
            $depth--;
            if ($depth === 0)
                return $i;
        }
    }
    return null;
}

/** Heavy `\left(...\right)` is 400; keep `\left(...\right]` intervals. Also drop `\\` in the body. */
function lemma_shell_latex_flatten_left_right_paren(string $latex): string
{
    $open = '\\left(';
    $close = '\\right)';
    $pos = 0;
    while (($i = strpos($latex, $open, $pos)) !== false) {
        $start = $i + strlen($open);
        $depth = 1;
        $j = $start;
        $len = strlen($latex);
        $interval = false;
        while ($j < $len && $depth > 0) {
            if (substr($latex, $j, 6) === $open) {
                $depth++;
                $j += 6;
                continue;
            }
            if (substr($latex, $j, 7) === $close) {
                $depth--;
                if ($depth === 0)
                    break;
                $j += 7;
                continue;
            }
            if ($depth === 1 && substr($latex, $j, 7) === '\\right]') {
                $interval = true;
                break;
            }
            $j++;
        }
        if ($interval || $depth !== 0) {
            $pos = $i + 1;
            continue;
        }
        $body = trim(str_replace(["\\\\\n", '\\\\'], ' ', substr($latex, $start, $j - $start)));
        // {\left(-2\right)} must become {-2}, not {(-2)}, or \frac {{(-2)} β} parses as \frac{(-2)} β.
        $repl = preg_match('/^-[0-9]+$/', $body) ? $body : '(' . $body . ')';
        $latex = substr($latex, 0, $i) . $repl . substr($latex, $j + strlen($close));
        $pos = $i + 1;
    }
    return $latex;
}

/** `{ {A} - {B} }` as an `=` RHS is 400 when both sides are heavy fracs. */
function lemma_shell_latex_is_group_diff(string $inner): bool
{
    $inner = trim($inner);
    if (($inner[0] ?? '') !== '{')
        return false;
    $c = lemma_shell_latex_match_brace($inner, 0);
    if ($c === null)
        return false;
    $rest = substr($inner, $c + 1);
    if (!preg_match('/^\s*[-+]\s*\{/', $rest))
        return false;
    $open2 = strpos($rest, '{');
    $c2 = lemma_shell_latex_match_brace($rest, $open2);
    return $c2 !== null && trim(substr($rest, $c2 + 1)) === '';
}

function lemma_shell_latex_peel_eq_group_diff(string $latex): string
{
    $pos = 0;
    while (($i = strpos($latex, ' = {', $pos)) !== false) {
        $open = $i + 3;
        $close = lemma_shell_latex_match_brace($latex, $open);
        if ($close === null) {
            $pos = $i + 1;
            continue;
        }
        $inner = substr($latex, $open + 1, $close - $open - 1);
        if (($inner[0] ?? '') === '{' || lemma_shell_latex_is_group_diff($inner)) {
            $latex = substr($latex, 0, $open) . $inner . substr($latex, $close + 1);
            $pos = $open + strlen($inner);
        } else {
            $pos = $close + 1;
        }
    }
    return $latex;
}

/** Extra `{ A \lor B }` around a heavy or is 400; do not peel `\frac`/`\sqrt`/`^`/`_` args. */
function lemma_shell_latex_peel_wrapped_lor(string $latex): string
{
    $needle = ' \\lor ';
    for ($guard = 0; $guard < 64; $guard++) {
        $changed = false;
        $len = strlen($latex);
        $i = 0;
        while ($i < $len) {
            if ($latex[$i] === '{') {
                $close = lemma_shell_latex_match_brace($latex, $i);
                if ($close === null)
                    break;
                $inner = substr($latex, $i + 1, $close - $i - 1);
                $prefix = substr($latex, 0, $i);
                $before = $i > 0 ? $latex[$i - 1] : '';
                $cmd = $before !== '^' && $before !== '_'
                    && !preg_match('/\\\\(?:frac|sqrt(?:\[\d+\])?|text|ensuremath|mathrm|mathbf|mathbb|overline|colorbox|begin)\\s*$/', $prefix);
                if ($cmd && str_contains($inner, $needle)) {
                    $latex = substr($latex, 0, $i) . $inner . substr($latex, $close + 1);
                    $changed = true;
                    break;
                }
                $i = $close + 1;
                continue;
            }
            $i++;
        }
        if (!$changed)
            break;
    }
    return $latex;
}

/** Strip project-specific LaTeX wrappers so CodeCogs can parse the math. */
function lemma_shell_simplify_latex_for_codecogs(string $latex): string
{
    $latex = preg_replace(lemma_shell_latex_tag_re(), '', $latex);
    $latex = preg_replace('/\\\\color\{[^{}]+\}\s*/', '', $latex);
    // Drop align wrappers. Ite is {\\begin{align*} &{cases}&& \\end{align*}}; leftover & / && is 400.
    $latex = preg_replace('/\\\\begin\{align\*?\}(?:\s*&)?/', '', $latex);
    $latex = preg_replace('/(?:&+)?\s*\\\\end\{align\*?\}/', '', $latex);
    $latex = str_replace('&&', '', $latex);
    $latex = str_replace('{{\\begin{cases}', '{\\begin{cases}', $latex);
    $latex = str_replace('\\end{cases}}}', '\\end{cases}}', $latex);
    // {factor  cases} (ite as a product) is 400 when the cases body is heavy.
    $latex = preg_replace(
        '/\{((?:[^{}]|\{[^{}]*\})+?)\s*\\\\begin\{cases\}(.*?)\\\\end\{cases\}\}/s',
        '{$1}\\cdot\\begin{cases}$2\\end{cases}',
        $latex
    );
    // Align rows are `\\ &`; cases are `val & cond \\` — only strip tab-after-break.
    $latex = str_replace(["\\\\\n&", '\\\\&'], ["\\\\\n", '\\\\'], $latex);
    $latex = preg_replace('/\\\\colorbox\{#[0-9a-fA-F]+\}(\{\$)/', '$1', $latex);
    $latex = str_replace('{$\\mathord{\\left', '{\\left', $latex);
    $latex = str_replace('\\right)}$}', '\\right)}', $latex);
    $latex = str_replace('\\right)$}', '\\right)}', $latex);
    // {colorbox{mathord}} leaves {{\left(...\right)}}; extra group around a heavy body is 400.
    $latex = preg_replace(
        '/\{\{\\\\left\(((?:(?!\\\\left).)*?)\\\\right\)\}\}/s',
        '{\\left($1\\right)}',
        $latex
    );
    $latex = lemma_shell_latex_flatten_left_right_paren($latex);
    $latex = lemma_shell_latex_peel_wrapped_lor($latex);
    $latex = lemma_shell_latex_peel_eq_group_diff($latex);
    if (!str_contains($latex, '$')) {
        $latex = str_replace(['\\left\\{', '\\right\\}'], ['\\{', '\\}'], $latex);
    }
    $latex = str_replace(['{\\text{\'}}', '\\text{\'}'], "'", $latex);
    $latex = str_replace(['+\\!\\!+', '+\\!\\!\\!\\!+'], '++', $latex);
    $latex = str_replace([
        '\\mathbb{R}', '\\mathbb{C}', '\\mathbb{N}', '\\mathbb{Z}',
        '\\alpha', '\\beta', '\\gamma', '\\delta', '\\Delta', '\\omega', '\\pi',
        '\\exists', '\\forall',
        '\\langle', '\\rangle',
        'ℝ', 'ℂ', 'ℕ', 'ℤ',
        'α', 'β', 'γ', 'δ', 'Δ', 'ω', 'π',
        '∃', '∀',
        '⟨', '⟩',
    ], [
        '\\ensuremath{\\mathbb{R}}', '\\ensuremath{\\mathbb{C}}', '\\ensuremath{\\mathbb{N}}', '\\ensuremath{\\mathbb{Z}}',
        '\\ensuremath{\\alpha}', '\\ensuremath{\\beta}', '\\ensuremath{\\gamma}', '\\ensuremath{\\delta}',
        '\\ensuremath{\\Delta}', '\\ensuremath{\\omega}', '\\ensuremath{\\pi}',
        '\\ensuremath{\\exists}', '\\ensuremath{\\forall}',
        '\\ensuremath{\\langle}', '\\ensuremath{\\rangle}',
        '\\ensuremath{\\mathbb{R}}', '\\ensuremath{\\mathbb{C}}', '\\ensuremath{\\mathbb{N}}', '\\ensuremath{\\mathbb{Z}}',
        '\\ensuremath{\\alpha}', '\\ensuremath{\\beta}', '\\ensuremath{\\gamma}', '\\ensuremath{\\delta}',
        '\\ensuremath{\\Delta}', '\\ensuremath{\\omega}', '\\ensuremath{\\pi}',
        '\\ensuremath{\\exists}', '\\ensuremath{\\forall}',
        '\\ensuremath{\\langle}', '\\ensuremath{\\rangle}',
    ], $latex);
    $latex = str_replace(['\\lt', '\\gt'], ['<', '>'], $latex);
    // {\left(-2\right)} → {-2} can turn \frac {{-2} β}{d} into \frac {-2} β}{d}.
    $latex = preg_replace(
        '/\\\\frac \{(-[0-9]+)\}(\s+(?:\\\\ensuremath\{[^}]+\}|\\\\[a-zA-Z]+))\}(\s*\{)/',
        '\\frac {{\\1}\\2}\\3',
        $latex
    );
    return trim($latex);
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
        $wrapped = lemma_shell_simplify_latex_for_codecogs($latex);
        if ($wrapped !== '') {
            if (!str_contains($wrapped, '$')) {
                if (strlen($wrapped) > 60 || str_contains($wrapped, '=') || str_contains($wrapped, '\\left') || str_contains($wrapped, '\\lt') || str_contains($wrapped, '\\gt'))
                    $wrapped = '\\displaystyle ' . $wrapped;
                else
                    $wrapped = '$' . $wrapped . '$';
            }
            $url = 'https://latex.codecogs.com/png.latex?' . rawurlencode($wrapped);
            if (strlen($url) <= 7000) {
                $tag = null;
                if (preg_match(lemma_shell_latex_tag_re(), $latex, $m)) {
                    $tag = $m[1];
                    if (preg_match('/^\$([^$]+)\$$/', $tag, $inner))
                        $tag = $inner[1];
                    else
                        $tag = ltrim($tag);
                } elseif ($lean && preg_match('/^\(([^:]+)\s*:/', trim($lean), $m)) {
                    $tag = trim($m[1]);
                }
                echo '<div class="latex-display"><span class="latex-body"><img class="latex-formula" src="', lemma_shell_h($url),
                    '" alt="', lemma_shell_h($lean ?? ''), '" loading="lazy" decoding="async"',
                    ' onerror="this.closest(\'.latex-display\').classList.add(\'latex-formula-failed\')">',
                    '<pre class="lean-line lean-fallback Consolas">',
                    lemma_shell_h($lean ?? ''), '</pre></span>';
                if ($tag !== null && $tag !== '')
                    echo '<span class="latex-tag">', lemma_shell_h($tag), '</span>';
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
            foreach ($lines as $line) {
                if (!is_array($line))
                    continue;
                lemma_shell_render_lean_line(lemma_shell_unindent_decl($line['lean'] ?? null), true);
                $proof_latex = $line['latex'] ?? null;
                if ($proof_latex !== null && $proof_latex !== '')
                    echo '<p class="latex-block">', lemma_shell_h($proof_latex), "</p>\n";
            }
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
