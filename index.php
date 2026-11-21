<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';
require_once 'php/parser/lean.php';

/** True when `$head` names an existing top-level repo folder (`Lemma`, `Theorem`, …). */
function is_top_level_folder(string $head): bool
{
    return preg_match('/^[A-Z][A-Za-z0-9]*$/', $head)
        && is_dir(project_directory() . $head);
}

/** `?lemma=` → full module: keep an explicit top-level prefix, else add `Lemma.`. */
function lemma_param_to_module(string $input): ?string
{
    $module = str_replace('/', '.', trim($input));
    $hash = strpos($module, '#');
    if ($hash !== false)
        $module = substr($module, 0, $hash);
    if (str_ends_with($module, '.lean'))
        $module = substr($module, 0, -strlen('.lean'));
    if ($module === '')
        return null;
    $head = explode('.', $module)[0];
    return is_top_level_folder($head) ? $module : "Lemma.$module";
}

/** `Lemma.X` → `['lemma', 'X']`, `Theorem.X` → `['theorem', 'X']`; null otherwise. */
function canonical_decl_param(string $module): ?array
{
    if (preg_match('/^(Lemma|Theorem)\.(.+)$/s', $module, $matches))
        return [$matches[1] === 'Lemma' ? 'lemma' : 'theorem', $matches[2]];
    return null;
}

/** 302 to `/<userSegment>/?<param>=<value>`, keeping `#fragment` outside the query value. */
function redirect_decl_param(string $param, string $value, string $fragment = ''): void
{
    $location = '/' . get_project_name() . '/?' . $param . '=' . rawurlencode($value);
    if ($fragment !== '')
        $location .= '#' . $fragment;
    header("location:$location", true, 302);
    exit();
}

/**
 * Redirect a dotted module to its canonical address. `$declParam` is `lemma` when the
 * request already used `?lemma=`, so a normalising redirect never chains back through
 * `?module=` (one hop from the user's point of view).
 */
function redirect_module(string $module, string $declParam = 'module'): void
{
    $fragment = '';
    $hash = strpos($module, '#');
    if ($hash !== false) {
        $fragment = substr($module, $hash + 1);
        $module = substr($module, 0, $hash);
    }
    $canonical = canonical_decl_param($module);
    if ($canonical)
        redirect_decl_param($canonical[0], $canonical[1], $fragment);
    if ($declParam === 'lemma')
        redirect_decl_param('lemma', $module, $fragment);
    $location = '?module=' . $module;
    if ($fragment !== '')
        $location .= '#' . $fragment;
    header("location:$location");
    exit();
}

/** Repo `.lean` path → full dotted module (`Theorem.Rat.…Ne_0`); null outside the repo. */
function repo_lean_path_to_module(string $path): ?string
{
    $root = realpath(project_directory());
    $abs = realpath($path);
    if ($root === false || $abs === false || !str_ends_with($abs, '.lean'))
        return null;
    $rel = substr($abs, strlen($root) + 1);
    if ($rel === '' || str_starts_with($rel, '..'))
        return null;
    return str_replace(['/', '\\'], '.', substr($rel, 0, -strlen('.lean')));
}

/** Absolute path on either platform (`/…`, `C:\…`, `C:/…`, `\\server\…`). */
function is_absolute_path(string $path): bool
{
    return str_starts_with($path, '/')
        || (bool) preg_match('#^[A-Za-z]:[\\\\/]#', $path)
        || str_starts_with($path, '\\\\');
}

/** Canonical `?theorem=` value for a file: its dotted module without the `Theorem.` prefix. */
function theorem_canonical_module(string $path): ?string
{
    $module = repo_lean_path_to_module($path);
    if ($module === null)
        return null;
    return str_starts_with($module, 'Theorem.')
        ? substr($module, strlen('Theorem.'))
        : $module;
}

/**
 * `?theorem=` → `.lean` path: a bare dotted name is a `Theorem/` module, an explicit
 * top-level prefix (`Lemma.…`, `Theorem.…`, `Def.…`) is used as written.
 */
function theorem_param_to_lean(string $input): ?string
{
    $raw = rtrim(trim($input), "/\\");
    if ($raw === '')
        return null;
    if (str_ends_with($raw, '.lean')) {
        $path = is_absolute_path($raw) ? $raw : project_directory() . $raw;
        return is_file($path) ? $path : null;
    }
    $head = explode('.', $raw)[0];
    foreach (is_top_level_folder($head) ? [$raw] : ["Theorem.$raw", $raw] as $module) {
        $path = project_directory() . str_replace('.', '/', $module) . '.lean';
        if (is_file($path))
            return $path;
    }
    return null;
}

$key = array_keys($_GET);
switch (count($key)) {
    case 0:
        $key = array_keys($_POST);
        switch (count($key)) {
            case 0:
                require_once 'php/summary.php';
                exit();
            default:
                if (array_key_exists('module', $_POST)) {
                    $module = $_POST['module'];
                    break;
                } else {
                    require_once 'php/search.php';
                    exit();
                }
        }
        break;
    case 1:
        [$key] = $key;
        switch ($key) {
            case 'module':
                $module = $_GET['module'];
                break;
            case 'axiom':
                $sympy = $_GET['axiom'];
                require_once 'php/sympy.php';
                exit();
            case 'sympy':
                $sympy = $_GET['sympy'];
                require_once 'php/sympy.php';
                exit();
            case 'callee':
                require_once 'php/hierarchy.php';
                exit();
            case 'caller':
                require_once 'php/hierarchy.php';
                exit();
            case 'new':
                require_once 'php/new.php';
                exit();
            case 'type':
            case 'q':
            case 'latex':
                require_once 'php/search.php';
                exit();
        }
    case 2:
        $module = $_GET['module']?? null;
        if ($module)
            break;
    default:
        if (($_GET['q']?? null) || ($_GET['type']?? null)) {
            require_once 'php/search.php';
            exit();
        }
        if (array_key_exists('mathlib', $_GET)) {
            require_once 'php/mathlib.php';
            exit();
        }
        break;
}

$declParam = 'module';
$module = $module ?? '';

/** `?theorem=<repo path | module>` — render any repo `.lean` file, not only `Lemma/`. */
if (isset($_GET['theorem']) && is_string($_GET['theorem']) && trim($_GET['theorem']) !== '') {
    $raw = trim($_GET['theorem']);
    if (str_ends_with(rtrim($raw, "/\\"), '.lean')) {
        $path = is_absolute_path($raw) ? $raw : project_directory() . $raw;
        $canonical = is_file($path) ? theorem_canonical_module($path) : null;
        if ($canonical === null) {
            http_response_code(404);
            exit();
        }
        redirect_decl_param('theorem', $canonical);
    }
    $leanFile = theorem_param_to_lean($raw);
    $module = $leanFile === null ? null : repo_lean_path_to_module($leanFile);
    if ($module === null) {
        http_response_code(404);
        exit();
    }
    $title = str_replace('.', '/', $module);
    $path_info = substr($leanFile, 0, -strlen('.lean'));
    require 'php/lemma.php';
    exit();
}

/** `?lemma=<Lemma-relative module>` — where `?module=Lemma.…` redirects to. */
if (isset($_GET['lemma']) && is_string($_GET['lemma']) && trim($_GET['lemma']) !== '') {
    $module = lemma_param_to_module(trim($_GET['lemma']));
    if ($module === null) {
        http_response_code(404);
        exit();
    }
    if (str_starts_with($module, 'Lemma.')) {
        $module = substr($module, strlen('Lemma.'));
        $declParam = 'lemma';
    } else {
        $leanFile = project_directory() . str_replace('.', '/', $module) . '.lean';
        if (!is_file($leanFile)) {
            http_response_code(404);
            exit();
        }
        $title = str_replace('.', '/', $module);
        $path_info = substr($leanFile, 0, -strlen('.lean'));
        require 'php/lemma.php';
        exit();
    }
}

/**
 * Legacy `?module=<Lemma-relative module>`: without a top-level prefix the module
 * resolves under `Lemma/`, so it is a lemma address — canonicalise it to `?lemma=`.
 * Setting `$declParam` early also keeps the normalising redirects below on `?lemma=`,
 * so the user sees one hop.
 */
$fromModuleParam = isset($_GET['module']) && $declParam === 'module';
$moduleFrag = '';
if ($fromModuleParam) {
    $normalized = str_replace('/', '.', trim($module));
    $hash = strpos($normalized, '#');
    if ($hash !== false) {
        $moduleFrag = substr($normalized, $hash + 1);
        $normalized = substr($normalized, 0, $hash);
    }
    if (!is_top_level_folder(explode('.', $normalized)[0])) {
        $declParam = 'lemma';
        $module = $normalized;
    }
}

if (str_ends_with($module, '.lean')) {
    $module = str_replace('/', '.', substr($module, 0, -strlen('.lean')));
    redirect_module($module, $declParam);
}

$module = str_replace('/', '.', trim($module));

/** `?module=Lemma.…` → `?lemma=…`, `?module=Theorem.…` → `?theorem=…`. */
$base = $module;
$fragment = '';
$hash = strpos($base, '#');
if ($hash !== false) {
    $fragment = substr($base, $hash + 1);
    $base = substr($base, 0, $hash);
}
$canonical = canonical_decl_param($base);
if ($canonical)
    redirect_decl_param($canonical[0], $canonical[1], $fragment);

$title = str_replace('.', '/', $module);

$path_info = substr(__FILE__, 0, -9) . "Lemma/" . $title;

$leanFile = null;
if (! str_ends_with($path_info, '/')) {
    $leanFile = $path_info . ".lean";
    if (!file_exists($leanFile)) {
        if ($_POST);
        elseif (is_dir($path_info))
            $leanFile = null;
        elseif (file_exists($dirname = dirname($leanFile) . '.lean')) {
            $lastDotPosition = strrpos($module, '.');
            $module = substr($module, 0, $lastDotPosition) . '#' . substr($module, $lastDotPosition + 1);
            redirect_module($module, $declParam);
            exit();
        }
        else {
            $tokens = explode('.', $module);
            [$section, $segment] = parseInfixSegments($tokens);
            $index = array_search('of', $tokens);
            if ($index !== false) {
                if (count ($segment[1]) == 1) {
                    switch ($segment[1][0]) {
                        case 'is':
                            $index = array_search('of', $tokens);
                            if ($index === false) {
                                $tokens_ = [...$tokens];
                                $tokens_[1] = transformPrefix($tokens[1]);
                                $tokens_[3] = transformPrefix($tokens[3]);
                                $module = implode('.', $tokens_);
                                $path = module_to_lean($module);
                                if (file_exists($path)) {
                                    redirect_module($module, $declParam);
                                    exit();
                                }
                                $tokens = array_merge([$tokens[0]], array_slice($tokens, 3), ['is'], [$tokens[1]]);
                            }
                            else {
                                if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[1], $matches))
                                    $tokens[1] = $matches[1] . $matches[2];
                                $tokens = array_merge([$tokens[0]], array_slice($tokens, 3, $index - 3), ['is'], [$tokens[1]], array_slice($tokens, $index));
                            }
                            break;
                        case 'eq':
                        case 'as':
                        case 'ne':
                            $tmp = $tokens[1];
                            $tokens[1] = $tokens[3];
                            $tokens[3] = $tmp;
                            break;
                        case 'of':
                            $first = $segment[0];
                            if (count($first) == 1) {
                                if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $first[0], $matches)) {
                                    $tokens[1] = $matches[1] . $matches[2];
                                    $module = implode('.', $tokens);
                                    $path = module_to_lean($module);
                                    if (!file_exists($path)) {
                                        $tokens[1] = $first;
                                        $tokens[2] = 'is';
                                        if (count($tokens) > 4)
                                            std\array_insert($tokens, 4, 'of');
                                    }
                                }
                                else {
                                    if (count($tokens) == 5) {
                                        $tokens_ = [...$tokens];
                                        $tokens_[1] = transformPrefix($tokens_[1]);
                                        $tokens_[3] = transformPrefix($tokens_[3]);
                                        $tokens_[4] = transformPrefix($tokens_[4]);
                                        $module = implode('.', $tokens_);
                                        $path = module_to_lean($module);
                                        if (file_exists($path)) {
                                            redirect_module($module, $declParam);
                                            exit();
                                        }
                                    }
                                    $hit = false;
                                    for ($i = 2; $i < count($segment); $i++) {
                                        # try mt $i
                                        $segment_ = [...$segment];
                                        $segment_[0] = Not($segment_[$i]);
                                        $segment_[$i] = Not($first);
                                        $path = module_to_lean($segment_, $section);
                                        if (file_exists($path)) {
                                            $hit = true;
                                            $segment = $segment_;
                                            break;
                                        }
                                    }
                                    if (! $hit) {
                                        $alt = try_of_is_of_file_rewrite($tokens);
                                        if ($alt !== null) {
                                            redirect_module($alt, $declParam);
                                            exit();
                                        }
                                        $segment[1][0] = 'is';
                                    }
                                }
                            }
                            elseif (count($first) == 3) {
                                if (is_infix_operator($first[1])) {
                                    # comm — when swapped path exists, use it (e.g. Nat.AddSub.eq.SubAdd.of.Ge → Nat.SubAdd.eq.AddSub.of.Ge)
                                    $segment_ = [...$segment];
                                    $segment_[0] = [$first[2], $first[1], $first[0]];
                                    $path = module_to_lean($segment_, $section);
                                    if (file_exists($path)) {
                                        $segment = $segment_;
                                    } else {
                                        $segment[1][0] = 'is';
                                    }
                                }
                            }
                            break;
                        default:
                            $first = $tokens[1];
                            if (preg_match($first, "^(S?Eq)_([\w'!₀-₉]+)$", $m))
                                $tokens[1] = $m[1] . $m[2];
                            else if ($index = array_search('of', $tokens))
                                $tokens[$index] = 'is';
                            else if ($index = array_search('is', $tokens)) {
                                $section = $tokens[0];
                                $first = array_slice($tokens, 1, $index - 1);
                                $second = array_slice($tokens, $index + 1);
                                $tokens = array_merge([$section], $second, ['is'], $first);
                            }
                            else 
                                $leanFile = null;
                            break;
                    }
                }
            }
            else {
                if (count ($segment) > 1 && count ($segment[1]) == 1) {
                    switch ($segment[1][0]) {
                        case 'is':
                            $index = array_search('of', $tokens);
                            if ($index === false) {
                                [$segment[0], $segment[2]] = [$segment[2], $segment[0]]; 
                                $module = tokens_to_module($segment, $section);
                                $path = module_to_lean($module);
                                if (file_exists($path)) {
                                    redirect_module($module, $declParam);
                                    exit();
                                }
                                $tokens = array_merge([$tokens[0]], array_slice($tokens, 3), ['is'], [$tokens[1]]);
                            }
                            else {
                                if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $tokens[1], $matches))
                                    $tokens[1] = $matches[1] . $matches[2];
                                $tokens = array_merge([$tokens[0]], array_slice($tokens, 3, $index - 3), ['is'], [$tokens[1]], array_slice($tokens, $index));
                            }
                            break;
                        case 'eq':
                        case 'as':
                        case 'ne':
                            $tmp = $tokens[1];
                            $tokens[1] = $tokens[3];
                            $tokens[3] = $tmp;
                            break;
                        case 'of':
                            $first = $tokens[1];
                            if (preg_match("/^([SH]?Eq|Iff)_(.+)/", $first, $matches)) {
                                $tokens[1] = $matches[1] . $matches[2];
                                $module = implode('.', $tokens);
                                $path = module_to_lean($module);
                                if (!file_exists($path)) {
                                    $tokens[1] = $first;
                                    $tokens[2] = 'is';
                                    if (count($tokens) > 4)
                                        std\array_insert($tokens, 4, 'of');
                                }
                            }
                            else {
                                if (count($tokens) == 5) {
                                    $tokens_ = [...$tokens];
                                    $tokens_[1] = transformPrefix($tokens_[1]);
                                    $tokens_[3] = transformPrefix($tokens_[3]);
                                    $tokens_[4] = transformPrefix($tokens_[4]);
                                    $module = implode('.', $tokens_);
                                    $path = module_to_lean($module);
                                    if (file_exists($path)) {
                                        redirect_module($module, $declParam);
                                        exit();
                                    }
                                }
                                $tokens[2] = 'is';
                            }
                            break;
                        default:
                            $first = $tokens[1];
                            if (preg_match($first, "^(S?Eq)_([\w'!₀-₉]+)$", $m))
                                $tokens[1] = $m[1] . $m[2];
                            else if ($index = array_search('of', $tokens))
                                $tokens[$index] = 'is';
                            else if ($index = array_search('is', $tokens)) {
                                $section = $tokens[0];
                                $first = array_slice($tokens, 1, $index - 1);
                                $second = array_slice($tokens, $index + 1);
                                $tokens = array_merge([$section], $second, ['is'], $first);
                            }
                            else 
                                $leanFile = null;
                            break;
                    }
                }
                else {
                    $first = $segment[0];
                    if (count($first) == 1) {
                        if (preg_match($first[0], "^(S?Eq)_([\w'!₀-₉]+)$", $m))
                            $tokens[1] = $m[1] . $m[2];
                    }
                    elseif (count($first) == 3) {
                        if (is_symm_operator($first[1])) {
                            # comm
                            $segment_ = [...$segment];
                            $segment_[0] = [$first[2], $first[1], $first[0]];
                            $path = module_to_lean($segment_, $section);
                            if (file_exists($path)) {
                                $segment = $segment_;
                            }
                            else {
                                $first = $segment_[0];
                                $first[0] = transformPrefix($first[0]);
                                $first[2] = transformPrefix($first[2]);
                                $segment_[0] = [$first[0], $first[1], $first[2]];
                                $path = module_to_lean($segment_, $section);
                                if (file_exists($path))
                                    $segment = $segment_;
                                else {
                                    $segment_[0] = [$first[2], $first[1], $first[0]];
                                    $path = module_to_lean($segment_, $section);
                                    if (file_exists($path))
                                        $segment = $segment_;
                                }
                            }
                        }
                    }
                    elseif (preg_match($first, "^(S?Eq)_([\w'!₀-₉]+)$", $m))
                        $tokens[1] = $m[1] . $m[2];
                    else if ($index = array_search('of', $tokens))
                        $tokens[$index] = 'is';
                    else if ($index = array_search('is', $tokens)) {
                        $section = $tokens[0];
                        $first = array_slice($tokens, 1, $index - 1);
                        $second = array_slice($tokens, $index + 1);
                        $tokens = array_merge([$section], $second, ['is'], $first);
                    }
                    else 
                        $leanFile = null;
                }
            }
            if ($leanFile) {
                $alt = try_of_is_of_file_rewrite(explode('.', $module));
                if ($alt !== null) {
                    redirect_module($alt, $declParam);
                    exit();
                }
                $module = tokens_to_module($segment, $section);
                redirect_module($module, $declParam);
                exit();
            }
        }
    }
}

/** Legacy `?module=` lemma address: emit the single `?lemma=` hop instead of rendering. */
if ($fromModuleParam && $declParam === 'lemma')
    redirect_decl_param('lemma', $module, $moduleFrag);

$php = $leanFile ? 'lemma' : 'package';
require_once  "php/$php.php";
?>