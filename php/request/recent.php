<?php
require_once '../utility.php';

$arr = [];

$topk = $_GET['top'];

$folder = axiom_directory();

$topKHeap = new std\TopKHeap($topk);
foreach (read_all_lean($folder) as $leanFile) {
    $lean = file($leanFile);
    $count = count($lean);
    
    $module = lean_to_module($leanFile);
    if (!$count){
        error_log($leanFile." is empty!");
        try {
            unlink($leanFile);
        } catch (Exception $e) {
            error_log($e->getMessage());
        }
        
        continue;
    }
    
    $updatedTime = $lean[$count - 1];
    if (preg_match("/(\d\d\d\d)-(\d\d)-(\d\d)/", $updatedTime, $m)){
        $element = [(int)$m[1], (int)$m[2], (int)$m[3], $module];        
        $topKHeap->push($element);
    }
}

$arr = $topKHeap->topk();

$res = [];
foreach ($arr as [,,, $module]){
    $res[] = $module;
}
echo std\encode($res);
?>