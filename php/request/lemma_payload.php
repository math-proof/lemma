<?php
require_once '../init.php';
require_once '../utility.php';
require_once '../parser/lean.php';
require_once '../lemma_load_code.php';

$module = $_GET['module'] ?? '';
if ($module === '') {
    http_response_code(400);
    header('Content-Type: application/json; charset=utf-8');
    echo std\encode(['error' => 'missing module']);
    exit;
}

$module = str_replace('/', '.', $module);
$leanFile = module_to_path($module) . '.lean';
if (!is_readable($leanFile)) {
    http_response_code(404);
    header('Content-Type: application/json; charset=utf-8');
    echo std\encode(['error' => 'not found']);
    exit;
}

$code = load_lemma_code($module, $leanFile);
if (!$code || empty($code['lemma'])) {
    http_response_code(500);
    header('Content-Type: application/json; charset=utf-8');
    echo std\encode(['error' => 'failed to load lemma']);
    exit;
}

header('Content-Type: application/json; charset=utf-8');
echo std\encode($code);
