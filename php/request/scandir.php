<?php
require_once '../utility.php';
use std\Graph, std\Text, std\Set;

$dict = empty($_POST) ? $_GET : $_POST;

$folder = $dict['folder'];

$packages = [];

switch($folder[0]){
    case '/':
    case '\\':
        break;
    default:
        $folder = '/'.$folder;
        break;
}

$folder = str_replace('.', '/', $folder);

$folder = dirname(dirname(dirname(__file__))).'/Lemma'.$folder;

foreach (scandir($folder) as $file) {
    switch ($file) {
        case ".":
        case "..":
        case "__pycache__":
            break;
        case "__init__.py":
            break;
        default:
            if (!str_ends_with($file, '.py')) {
                $packages[] = $file;
            }
    }
}

echo std\encode($packages);

?>