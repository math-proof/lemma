<?php
/**
 * CLI: read Lean source from stdin, print `compile($src)->render2vue(false)` as JSON.
 * CWD should be the repository root (Node sets this).
 *
 * Usage: php server/lean/php-bridge/render2vue.php < path/to/file.lean
 */

$here = __DIR__;
$root = dirname($here, 3);
chdir($root);

require_once $root . '/php/parser/lean.php';

$source = stream_get_contents(STDIN);
if ($source === false) {
    fwrite(STDERR, "Failed to read stdin\n");
    exit(1);
}

$tree = compile($source);
$modify = null;
$syntax = null;
$code = $tree->render2vue(false, $modify, $syntax);

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
