<?php
require_once '../std.php';
require_once '../parser/lean.php';
$module = $_POST['module'];
$root = dirname(dirname(dirname(__FILE__))) . "/Lemma/";
$sections = std\listdir($root);
$module = "/" . str_replace('.', '/', $module);

function try_to_die($module) {
    global $root;
    global $sections;
    foreach ($sections as $section) {
        $file = $root . $section . $module;
        if (file_exists($file) || file_exists($file . ".lean"))
            die($section);
    }
}

try_to_die($module);
if (preg_match("#(.+)/[a-z]+$#", $module, $m)) {
    $module = $m[1];
    try_to_die($module);
}
