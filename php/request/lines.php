<?php
require_once '../utility.php';
require_once '../init.php';
$lines = 0;
foreach (["Lemma", "Def", "Theorem", "Instance", "Class", "Structure", "Abbrev", "Notation", "Inductive", "Syntax", "Macro", "Initialize"] as $dir) {
    foreach (read_all_lean(project_directory() . $dir) as $file) {
        $lines += count(file($file, FILE_IGNORE_NEW_LINES | FILE_SKIP_EMPTY_LINES));
    }
}
echo $lines;
?>