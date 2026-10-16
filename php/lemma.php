<?php
require_once 'init.php';
require_once 'std.php';

function lemma_shell_h(?string $s): string
{
    return htmlspecialchars($s ?? '', ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8');
}

/** URL segment for this project (`lean` when docroot is `…/github` and site is `/lean/`). */
function lemma_user_segment(): string
{
    return get_project_name();
}

/**
 * Resolve a package.json `exports` / `module` / `main` entry to a path relative to the package root.
 * Mirrors `mjs/app.mjs` `resolveCmEsmFile` so Apache can serve CM6 via static `node_modules/`.
 */
function lemma_resolve_npm_entry(string $pkg): ?string
{
    $pkgJsonPath = dirname(__DIR__) . '/node_modules/' . $pkg . '/package.json';
    if (!is_readable($pkgJsonPath))
        return null;
    $pkgJson = json_decode(file_get_contents($pkgJsonPath), true);
    if (!is_array($pkgJson))
        return null;
    $entry = $pkgJson['exports'] ?? $pkgJson['module'] ?? $pkgJson['main'] ?? null;
    while (is_array($entry)) {
        if (isset($entry['.']))
            $entry = $entry['.'];
        elseif (isset($entry['import']))
            $entry = $entry['import'];
        elseif (isset($entry['default']))
            $entry = $entry['default'];
        else
            $entry = reset($entry);
    }
    if (!is_string($entry) || $entry === '')
        return null;
    $entry = ltrim(str_replace('\\', '/', $entry), './');
    $file = dirname(__DIR__) . '/node_modules/' . $pkg . '/' . $entry;
    if (!is_readable($file))
        return null;
    return $entry;
}

/** Emit import map matching `ejs/codemirror-importmap.ejs`, pointing at static node_modules ESM files. */
function lemma_emit_codemirror_importmap(string $userSegment): void
{
    $pkgs = [
        '@codemirror/state',
        '@codemirror/view',
        '@codemirror/commands',
        '@codemirror/language',
        '@codemirror/autocomplete',
        '@codemirror/search',
        '@codemirror/streamparser',
        '@lezer/common',
        '@lezer/highlight',
        '@lezer/lr',
        'style-mod',
        '@marijn/find-cluster-break',
        'crelt',
        'w3c-keyname',
    ];
    $imports = [];
    foreach ($pkgs as $pkg) {
        $entry = lemma_resolve_npm_entry($pkg);
        if ($entry === null)
            continue;
        $imports[$pkg] = '/' . $userSegment . '/node_modules/' . $pkg . '/' . $entry;
    }
    if (!$imports)
        return;
    echo '<script type="importmap">', "\n";
    echo json_encode(['imports' => $imports], JSON_UNESCAPED_SLASHES | JSON_PRETTY_PRINT), "\n";
    echo "</script>\n";
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
        '\\mathbb{R}', '\\mathbb{C}', '\\mathbb{N}', '\\mathbb{Z}',
        '\\alpha', '\\beta', '\\gamma', '\\delta',
        '\\Delta', '\\omega', '\\pi',
        '\\exists', '\\forall',
        '\\langle', '\\rangle',
        '\\mathbb{R}', '\\mathbb{C}', '\\mathbb{N}', '\\mathbb{Z}',
        '\\alpha', '\\beta', '\\gamma', '\\delta',
        '\\Delta', '\\omega', '\\pi',
        '\\exists', '\\forall',
        '\\langle', '\\rangle',
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

/** Render given/imply. preview=1 uses a CodeCogs PNG; otherwise KaTeX in the shell. */
function lemma_shell_is_preview(): bool
{
    return (($_GET['preview'] ?? '') === '1');
}

function lemma_shell_codecogs_wrapped(string $latex): string
{
    $wrapped = lemma_shell_simplify_latex_for_codecogs($latex);
    if ($wrapped === '')
        return '';
    if (!str_contains($wrapped, '$')) {
        if (strlen($wrapped) > 60 || str_contains($wrapped, '=') || str_contains($wrapped, '\left') || str_contains($wrapped, '\lt') || str_contains($wrapped, '\gt'))
            $wrapped = '\displaystyle ' . $wrapped;
        else
            $wrapped = '$' . $wrapped . '$';
    }
    return $wrapped;
}

function lemma_shell_latex_tag(?string $latex, ?string $lean): ?string
{
    $tag = null;
    if ($latex && preg_match(lemma_shell_latex_tag_re(), $latex, $m)) {
        $tag = $m[1];
        if (preg_match('/^\$([^$]+)\$$/', $tag, $inner))
            $tag = $inner[1];
        else
            $tag = ltrim($tag);
    } elseif ($lean && preg_match('/^\(([^:]+)\s*:/', trim($lean), $m)) {
        $tag = trim($m[1]);
    }
    return ($tag !== null && $tag !== '') ? $tag : null;
}

function lemma_shell_render_codecogs(string $latex, ?string $lean): bool
{
    $wrapped = lemma_shell_codecogs_wrapped($latex);
    if ($wrapped === '')
        return false;
    $prev = null;
    while ($prev !== $wrapped) {
        $prev = $wrapped;
        $wrapped = preg_replace('/\\\\ensuremath\{([^{}]*)\}/', '$1', $wrapped);
    }
    $wrapped = str_replace(['\\left.', '\\right.', '\\left', '\\right', '\\displaystyle ', '\\middle|', '\\middle'], ['', '', '', '', '', '|', ''], $wrapped);
    $wrapped = trim($wrapped, " $\t\n");
    // Serve via local proxy so Chrome never hits latex.codecogs.com through Clash.
    $url = 'php/request/codecogs.php?latex=' . rawurlencode($wrapped);
    if (strlen($url) > 7000)
        return false;
    $tag = lemma_shell_latex_tag($latex, $lean);
    echo '<div class="latex-display"><span class="latex-body"><img class="latex-formula" src="', lemma_shell_h($url),
        '" alt="', lemma_shell_h($lean ?? ''), '" loading="lazy" decoding="async"',
        ' onerror="this.closest(\'.latex-display\').classList.add(\'latex-formula-failed\')">',
        '<pre class="lean-line lean-fallback Consolas">',
        lemma_shell_h($lean ?? ''), '</pre></span>';
    if ($tag !== null)
        echo '<span class="latex-tag">', lemma_shell_h($tag), '</span>';
    echo "</div>\n";
    return true;
}


/**
 * When lean is a single stmt, MySQL-cached latex may still be multi-row
 * ({have}/PSpace/`rw`/align*). Keep only the last latex row — the concluding
 * equality. Also used as a finalizer after multi-stmt have-stripping.
 */
function lemma_shell_strip_have_rows_from_latex(?string $latex): ?string
{
    if ($latex === null || $latex === '')
        return $latex;

    $unwrap = static function (string $row): string {
        $row = trim($row);
        $row = preg_replace('/^&\s*/', '', $row);
        $row = preg_replace('/\s*&&\s*$/', '', $row);
        $row = preg_replace('/\\\\\\\\end\{align\*\}\s*$/', '', $row);
        $row = preg_replace('/\\\\end\{align\*\}\s*$/', '', $row);
        return trim($row);
    };

    $mode = 'none';
    $rows = [];
    if (preg_match('/\\\\begin\{align\*\}(.*?)\\\\end\{align\*\}/s', $latex, $am)) {
        $mode = 'align';
        $body = trim($am[1]);
        $rows = preg_split('/\\\\\\\\\s*(?:\n|$)/', $body);
        $rows = array_values(array_filter($rows, static fn($r) => trim($r) !== ''));
    } elseif (str_contains($latex, '\\\\')) {
        $mode = 'raw';
        $rows = preg_split('/\\\\\\\\\s*(?:\n|$)/', $latex);
        $rows = array_values(array_filter($rows, static fn($r) => trim($r) !== ''));
    }
    if ($mode === 'none' || count($rows) <= 1)
        return $latex;

    $picked = $unwrap(end($rows));
    if ($picked === '')
        return $latex;
    if ($mode === 'align') {
        $replaced = preg_replace('/\\\\begin\{align\*\}.*?\\\\end\{align\*\}/s', $picked, $latex, 1);
        return is_string($replaced) ? $replaced : $picked;
    }
    return $picked;
}

function lemma_shell_strip_local_have_imply(?string $lean, ?string $latex): array
{
    if ($lean === null || $lean === '')
        return [$lean, $latex];

    $raw = $lean;
    $tagSuffix = '';
    if (preg_match('/\s*(:=\s*(?:by|calc)?)\s*$/u', $raw, $tm)) {
        $tagSuffix = $tm[1];
        $raw = substr($raw, 0, -strlen($tm[0]));
    }

    $lines = preg_split("/\r?\n/", $raw);
    $stmts = [];
    $cur = [];
    $baseIndent = null;
    $is_have_let = static function (string $first): bool {
        return (bool) preg_match('/^\s*(haveI?|letI?|set|replace)\b/u', $first);
    };
    foreach ($lines as $line) {
        if ($cur === [] && $line === '')
            continue;
        $indent = strlen($line) - strlen(ltrim($line));
        $startsHave = (bool) preg_match('/^\s*(haveI?|letI?|set|replace)\b/u', $line);
        // New stmt: another have/let, or a same-indent non-continuation after a have/let
        // (concluding equality must not stay glued to the last have).
        if ($startsHave) {
            if ($cur)
                $stmts[] = $cur;
            $cur = [$line];
            $baseIndent = $indent;
        } elseif (
            $cur
            && $baseIndent !== null
            && trim($line) !== ''
            && $indent <= $baseIndent
            && $is_have_let($cur[0] ?? '')
        ) {
            $stmts[] = $cur;
            $cur = [$line];
            $baseIndent = $indent;
        } else {
            $cur[] = $line;
            if ($baseIndent === null && trim($line) !== '')
                $baseIndent = $indent;
        }
    }
    if ($cur)
        $stmts[] = $cur;

    if (count($stmts) <= 1) {
        // Lean already clean (<=1 stmt), but MySQL-cached latex may still be
        // multi-row with {have}/PSpace path rows. Strip latex-only.
        return [$lean, lemma_shell_strip_have_rows_from_latex($latex)];
    }

    $keptIdx = [];
    foreach ($stmts as $i => $st) {
        $first = '';
        foreach ($st as $ln) {
            if (trim($ln) !== '') {
                $first = $ln;
                break;
            }
        }
        if ($first !== '' && !$is_have_let($first))
            $keptIdx[] = $i;
    }
    if (!$keptIdx)
        $keptIdx = [count($stmts) - 1];
    if (count($keptIdx) === count($stmts))
        return [$lean, $latex];

    $keptLines = [];
    foreach ($keptIdx as $i) {
        foreach ($stmts[$i] as $ln)
            $keptLines[] = $ln;
    }
    $newLean = implode("\n", $keptLines);
    if ($tagSuffix !== '')
        $newLean .= $tagSuffix;

    $newLatex = $latex;
    if ($latex !== null && $latex !== '') {
        $unwrap_align_row = static function (string $row): string {
            $row = trim($row);
            $row = preg_replace('/^&\s*/', '', $row);
            $row = preg_replace('/\s*&&\s*$/', '', $row);
            return $row;
        };
        $pick_rows = static function (array $rows) use ($stmts, $keptIdx, $unwrap_align_row): ?string {
            if (!$rows)
                return null;
            if (count($rows) === count($stmts)) {
                $keptRows = [];
                foreach ($keptIdx as $i)
                    $keptRows[] = $rows[$i];
            } elseif (count($keptIdx) === 1 && count($rows) > 1) {
                // Fallback: keep last row when stmt/row counts disagree
                $keptRows = [end($rows)];
            } else {
                return null;
            }
            if (count($keptRows) === 1)
                return $unwrap_align_row($keptRows[0]);
            return implode("\\\\\n", $keptRows);
        };

        if (preg_match('/\\\\begin\{align\*\}(.*?)\\\\end\{align\*\}/s', $latex, $am)) {
            $body = trim($am[1]);
            $rows = preg_split('/\\\\\\\\\s*\n/', $body);
            $rows = array_values(array_filter($rows, static fn($r) => trim($r) !== ''));
            $picked = $pick_rows($rows);
            if ($picked !== null) {
                if (count($keptIdx) === 1 || (is_string($picked) && !str_contains($picked, "\\\\\n"))) {
                    $newLatex = preg_replace('/\\\\begin\{align\*\}.*?\\\\end\{align\*\}/s', $picked, $latex, 1);
                } else {
                    $newLatex = preg_replace(
                        '/\\\\begin\{align\*\}.*?\\\\end\{align\*\}/s',
                        "\\begin{align*}\n{$picked}\n\\end{align*}",
                        $latex,
                        1
                    );
                }
            }
        } elseif (str_contains($latex, '\\\\')) {
            // MySQL-cached imply latex is often \\-joined rows without align*
            $rows = preg_split('/\\\\\\\\\s*(?:\n|$)/', $latex);
            $rows = array_values(array_filter($rows, static fn($r) => trim($r) !== ''));
            $picked = $pick_rows($rows);
            if ($picked !== null)
                $newLatex = $picked;
        }
    }

    $newLatex = lemma_shell_strip_have_rows_from_latex($newLatex);
    return [$newLean, $newLatex];
}


function lemma_shell_render_given_or_imply(?array $pair): void
{
    if (!is_array($pair))
        return;
    $lean = $pair['lean'] ?? null;
    $latex = $pair['latex'] ?? null;
    [$lean, $latex] = lemma_shell_strip_local_have_imply($lean, $latex);
    if (!empty($pair['insert'])) {
        lemma_shell_render_lean_line(lemma_shell_unindent_decl($lean), true);
        return;
    }
    if ($latex !== null && $latex !== '') {
        if (lemma_shell_is_preview() && lemma_shell_render_codecogs($latex, $lean))
            return;
        $wrapped = lemma_shell_codecogs_wrapped($latex);
        if ($wrapped !== '') {
            $math = $wrapped;
            if (preg_match('/^\$(.*)\$$/s', $math, $mm) && !str_contains($mm[1], '$'))
                $math = $mm[1];
            if (str_starts_with($math, '\displaystyle '))
                $math = substr($math, strlen('\displaystyle '));
            $tag = lemma_shell_latex_tag($latex, $lean);
            echo '<div class="latex-display"><span class="latex-body"><span class="latex-math">', lemma_shell_h($math),
                '</span><pre class="lean-line lean-fallback Consolas">',
                lemma_shell_h($lean ?? ''), '</pre></span>';
            if ($tag !== null)
                echo '<span class="latex-tag">', lemma_shell_h($tag), '</span>';
            echo "</div>\n";
            return;
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
        // array_is_list() is PHP 8.1+; WAMP/lemma.cn may still be on 8.0.
        $proofIsList = is_array($proof) && (
            function_exists('array_is_list')
                ? array_is_list($proof)
                : array_keys($proof) === range(0, count($proof) - 1)
        );
        $lines = is_array($by) ? $by : (is_array($calc) ? $calc : ($proofIsList ? $proof : null));
        if ($lines) {
            echo "<hr>\n<span class=\"green\"><b>-- proof</b></span><br>\n";
            foreach ($lines as $line) {
                if (!is_array($line))
                    continue;
                lemma_shell_render_lean_line(lemma_shell_unindent_decl($line['lean'] ?? null), true);
                $proof_latex = $line['latex'] ?? null;
                if ($proof_latex !== null && $proof_latex !== '') {
                    if (!(lemma_shell_is_preview() && lemma_shell_render_codecogs($proof_latex, $line['lean'] ?? null)))
                        echo '<p class="latex-block">', lemma_shell_h($proof_latex), "</p>\n";
                }
            }
        }
    }

    echo "</div>\n";
}

$code = fetch_from_mysql(get_project_name(), $module);
if ($code) {
    $code['imports'] = std\decode($code['imports']);
    $code['open'] = std\decode($code['open']);
    $code['preamble'] = std\decode($code['preamble']);
    $code['lemma'] = std\decode($code['lemma']);
    $code['meta'] = std\decode($code['meta']) ?? [];
    if (!is_array($code['meta']))
        $code['meta'] = [];
    if (!isset($code['meta']['error']) || !is_array($code['meta']['error']))
        $code['meta']['error'] = [];
    $code['date'] = std\decode($code['date']);
}

if (!$code || !$code['lemma'] || !$code['date']) {
    if (!is_readable($leanFile))
        $code = null;
    else {
        $leanCode = compile(file_get_contents($leanFile));
        $code = $leanCode->render2vue(false);
        if (!isset($code['meta']) || !is_array($code['meta']))
            $code['meta'] = [];
        if (isset($code['error'])) {
            if (!isset($code['meta']['error']))
                $code['meta']['error'] = $code['error'];
            unset($code['error']);
        }
        if (!isset($code['meta']['error']) || !is_array($code['meta']['error']))
            $code['meta']['error'] = [];
    }
}

if ($code)
    $code['module'] = $module;

$userSegment = lemma_user_segment();
?>
<?php if (lemma_shell_is_preview()): ?>
<base href="/<?php echo lemma_shell_h($userSegment); ?>/">
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
.latex-display img.latex-formula { max-width: 100%; height: auto; vertical-align: middle; zoom: 1.2; }
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
</style>
<body>
<div id="lemma-stage">
<div id="lemma-shell">
<?php
if ($code && !empty($code['lemma'])) {
    if (!empty($code['preamble']) && is_array($code['preamble'])) {
        foreach ($code['preamble'] as $preamble)
            if (is_string($preamble) && $preamble !== '')
                lemma_shell_render_lean_line($preamble);
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
<?php else: ?>
<base href="/<?php echo lemma_shell_h($userSegment); ?>/">
<title><?php echo lemma_shell_h($title); ?></title>
<link rel="stylesheet" href="css/codemirror-overrides.css">
<link rel="stylesheet" href="node_modules/katex/dist/katex.min.css">
<link rel="stylesheet" href="node_modules/prismjs/themes/prism.min.css" />
<body></body>

<script src="node_modules/axios/dist/axios.min.js"></script>
<script src="node_modules/qs/dist/qs.js"></script>
<script src="node_modules/clipboard/dist/clipboard.min.js" defer></script>
<script src="node_modules/file-saver/dist/FileSaver.min.js" defer></script>
<script src="node_modules/vue/dist/vue.global.prod.js"></script>
<script src="node_modules/vue3-sfc-loader/dist/vue3-sfc-loader.js"></script>

<script src="js/py.js?v=9"></script>
<script src="js/std.js?v=9"></script>
<script src="node_modules/lz-string/libs/lz-string.js" defer></script>
<script src="node_modules/katex/dist/katex.min.js" defer></script>
<script src="node_modules/katex/dist/contrib/auto-render.min.js" defer></script>
<script type=module src="js/utility.js"></script>
<script src="node_modules/prismjs/prism.js" defer></script>
<script src="js/prism-lean.js" defer></script>
<?php lemma_emit_codemirror_importmap($userSegment); ?>
<script type="module" src="js/codemirrorBoot.js"></script>
<script type=module>
createApp('render', <?php echo $code ? std\encode($code) : 'null'; ?>);
</script>
<?php endif; ?>
