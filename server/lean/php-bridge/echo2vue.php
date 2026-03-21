<?php
/**
 * CLI: `compile(file)->echo2vue($absPath)` — same as `php/request/echo.php` pipeline.
 * Needs repo root as CWD (Node sets this), plus `lake` + `lean` on PATH / elan.
 *
 * Usage: php server/lean/php-bridge/echo2vue.php <absolute-or-repo-relative-path/to/file.lean>
 */

$here = __DIR__;
$root = dirname($here, 3);
chdir($root);

require_once $root . '/php/parser/lean.php';

$arg = $argv[1] ?? null;
if ($arg === null || $arg === '') {
    fwrite(STDERR, "Usage: php echo2vue.php <path/to/file.lean>\n");
    exit(1);
}

$normalized = str_replace('\\', '/', $arg);
if (!is_file($arg) && is_file($root . '/' . ltrim($normalized, '/'))) {
    $leanFile = realpath($root . '/' . ltrim($normalized, '/'));
} elseif (is_file($arg)) {
    $leanFile = realpath($arg);
} else {
    fwrite(STDERR, "File not found: {$arg}\n");
    exit(1);
}

if ($leanFile === false) {
    fwrite(STDERR, "Could not resolve path: {$arg}\n");
    exit(1);
}

$source = file_get_contents($leanFile);
if ($source === false) {
    fwrite(STDERR, "Failed to read: {$leanFile}\n");
    exit(1);
}

$tree = compile($source);
$code = $tree->echo2vue($leanFile);

$flags = JSON_UNESCAPED_UNICODE;
if (defined('JSON_INVALID_UTF8_SUBSTITUTE')) {
    $flags |= JSON_INVALID_UTF8_SUBSTITUTE;
}
$json = json_encode($code, $flags);
if ($json === false) {
    fwrite(STDERR, 'json_encode failed: ' . json_last_error_msg() . "\n");
    exit(1);
}
echo $json;
