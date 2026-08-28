<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<title>hierarchy</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'init.php';

// ^ *error_log

$array_keys = array_keys($_GET);

if (count($array_keys) > 1) {
    // print_r($_GET);
    $deep = json_decode($_GET['deep']);
    unset($_GET['deep']);
} else {
    $deep = false;
}

$keyInput = array_keys($_GET)[0];

switch ($keyInput) {
    case "callee":
        $key = 'caller';
        $invert = true;
        break;

    case "caller":
        $key = 'callee';
        $invert = false;
        break;
}

$module = $_GET[$keyInput];
$module = str_replace('/', '.', $module);

$user = get_user();
$graph = establish_hierarchy($user, $module, $invert);

// $graph->convert_set_to_list();
$graph->detect_cycle_traceback($module, $parent);

if ($parent) {
//     echo implode('<br>', $parent)."<br>";
    
    $cyclicProof = $parent[0];

    for ($i = 1; $i < count($parent); ++ $i) {
        if ($parent[$i] == $cyclicProof) {
            break;
        }
    }

    $parent[] = $module;
    
    $traceback = [];
    for ($j = count($parent) - 1; $j >= $i; -- $j) {
        $traceback[] = $parent[$j];
    }    
    
//     echo implode('<br>', $traceback)."<br>";
    
} else {
    $traceback = null;
}
?>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>

<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/clipboard@2.0.10/dist/clipboard.min.js"></script>
<script src="static/js/std.js"></script>
<script src="static/js/utility.js"></script>

<script type=module>
createApp('hierarchy', {
	module : <?php echo std\encode($module)?>,
	graph : <?php echo std\encode($graph)?>,
	traceback: <?php echo std\encode($traceback)?>,
	keyInput : <?php echo std\encode($keyInput)?>,
    deep: <?php echo std\encode($deep)?>,
});

</script>

