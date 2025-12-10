<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';
require_once 'php/parser/lean.php';

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
        if ($_GET['q']?? null || $_GET['type']?? null) {
            require_once 'php/search.php';
            exit();
        }
        if (array_key_exists('mathlib', $_GET)) {
            require_once 'php/mathlib.php';
            exit();
        }
        break;
}

if (str_ends_with($module, '.lean')) {
    $module = lean_to_module($module);
    header("location:?module=$module");
    exit();
}

$module = str_replace('/', '.', $module);
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
            header("location:?module=$module");
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
                                    header("location:?module=$module");
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
                                            header("location:?module=$module");
                                            exit();
                                        }
                                    }
                                    $segment[1][0] = 'is';
                                }
                            }
                            elseif (count($first) == 3) {
                                if (is_infix_operator($first[1])) {
                                    # comm
                                    $segment_ = [...$segment];
                                    $segment_[0] = [$first[2], $first[1], $first[0]];
                                    $path = module_to_lean($segment_, $section);
                                    if (!file_exists($path)) {
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
                                $tokens_ = [...$tokens];
                                $tokens_[1] = transformPrefix($tokens[1]);
                                $tokens_[3] = transformPrefix($tokens[3]);
                                $module = implode('.', $tokens_);
                                $path = module_to_lean($module);
                                if (file_exists($path)) {
                                    header("location:?module=$module");
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
                                        header("location:?module=$module");
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
                $module = tokens_to_module($segment, $section);
                header("location:?module=$module");
                exit();
            }
        }
    }
}

$php = $leanFile ? 'lemma' : 'package';
require_once  "php/$php.php";
?>