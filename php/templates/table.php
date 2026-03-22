<!DOCTYPE HTML>
<html lang=en>
<meta charset="UTF-8">
<link rel="shortcut icon" href="static/jetty.ico" type="image/x-icon" />
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">

<title><?php echo $sql?></title>
<body></body>

<?php
include_once 'script.php';
?>

<script src="static/unpkg.com/he@1.2.0/he.js"></script>
<script src="static/unpkg.com/xlsx@0.18.5/dist/xlsx.full.min.js"></script>
<script src="static/unpkg.com/papaparse@5.4.1/papaparse.min.js"></script>
<script src="static/unpkg.com/xregexp@5.1.1/xregexp-all.js"></script>

<script src="static/js/std.js"></script>
<script type="module" src='static/js/utility.js'></script>
<script>
MathJax = InitMathJax(1000);
</script>
<script async src="static/unpkg.com/mathjax@3.2.0/es5/tex-chtml.js"></script>

<?php
//<script src="static/unpkg.com/vue-async-computed@3.9.0/dist/vue-async-computed.js"></script>
// error_log('$table ='.$table);
if ($dual?? false)
    $component = 'dual';
else {
    $component = std\hump($table);
    $component = file_exists(dirname(__file__)."/../../static/components/$component.vue")? $component: 'mysqlTable';
}

if ($table && $table[0] == '`')
    $table = std\substring($table, 1, -1);

$props['table'] = $table?? 'dual';
$props['host'] = $host;
$props['user'] = $user;
$props['token'] = $token;
$props['data'] = $data;
$props['sql'] = $sql;
$props['kwargs'] = $kwargs;
// error_log('$props ='.std\encode($props));
?>

<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as lean from "./static/codemirror/mode/lean/lean.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"
import * as comment from "./static/codemirror/addon/comment/comment.js"

createApp('<?php echo $component?>', <?php echo std\encode($props)?>);
</script>
</html>