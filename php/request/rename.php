<?php
require_once '../utility.php';
require_once '../mysql.php';
require_once '../init.php';

$user = get_project_name();
chdir("../../");
function rename_lemma($old, $new)
{
    if (std\is_linux()) {
        $cmd = "bash sh/rename.sh";
        $cmd .= " \"$old\" \"$new\"";
    }
    else {
        // using json_encode instead of escapeshellarg due to ! character
        $args = "-src " . json_encode($old) . " -dst ". json_encode($new);
        $cmd = "powershell -ExecutionPolicy Bypass -NoProfile -File ".  json_encode("ps1\\rename.ps1") . " -ArgumentList $args";;
    }

    error_log("cmd = $cmd");
    exec($cmd, $output_array, $ret);
    
    error_log(implode("\n", $output_array));
    
    if ($ret)
        error_log("Error in renaming $old to $new");
}

$dict = empty($_POST) ? $_GET : $_POST;

$package = $dict['package']?? null;
$old = $dict['old'];
$new = $dict['new'];

error_log("old = $old");
error_log("new = $new");
if ($package !== null) {
    $oldLemma = "$package$old";
    $newLemma = "$package$new";
    update_lemma($user, $oldLemma, $newLemma, true, function($old, $new) use ($user) {
        rename_lemma($old, $new);
    });

    update_axiom($user, $oldLemma, $newLemma, true);
    $folder = axiom_directory() . str_replace('.', '/', $package) . '/';
    std\deleteDirectory($folder . $old);
} else {

    $newFile = module_to_lean($new);

    if (file_exists($newFile))
        die("$newFile already exists");

    unlink($newFile);

    rename_lemma($old, $new);

    update_axiom($user, $old, $new);
}

echo std\encode("renamed!");
