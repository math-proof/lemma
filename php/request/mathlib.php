<?php
require_once '../std.php';
if (!std\is_linux())
    require_once '../parser/lean.php';

$name = $_POST['name'];

$leanFile = "test.$name.lean";
chdir("../../");
if (!file_exists($leanFile)) {
    error_log("create new lean file = $leanFile");
    std\createNewFile($leanFile);
}
// create a block to write the code
{
    $file = new std\Text($leanFile);
    $codeStr = <<< EOT
import Mathlib
import sympy.printing.json
#eval do
  println! ← Name.toJson `$name
EOT;

    $file->writelines([$codeStr]);
}

if (std\is_linux()) {
    $cmd = "~/.elan/bin/lake env lean \"$leanFile\"";
    exec($cmd, $output_array);
} else {
    $cmd = get_lake_path() . ' env lean ' . escapeshellarg($leanFile);
    std\exec($cmd, $output_array, get_lean_env());
}
echo implode("\n", $output_array);
unlink($leanFile);
