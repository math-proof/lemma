<?php
require_once 'std.php';
require_once 'mysql.php';
require_once 'init.php';

function get_lemma($args) {
    [$name, $type, $instImplicit, $strictImplicit, $implicit, $given, $explicit, $imply] = $args;
    return [
        'name' => $name,
        'type' => $type,
        'instImplicit' => $instImplicit,
        'strictImplicit' => $strictImplicit,
        'implicit' => $implicit,
        'given' => std\decode($given),
        'explicit' => $explicit,
        'imply' => std\decode($imply)
    ];
}
$name = $_GET["mathlib"];
$lemma = [];
foreach (get_rows("select * from mathlib where name = \"$name\"", MYSQLI_NUM) as $args)
    $lemma[] = get_lemma($args);
if (!$lemma) {
    $limit = $_GET["limit"]?? 100;
    if ($name) {
        $regexp = str_replace(".", '\.', $name);
        $regexp = preg_replace("/(?<![\\\\])[\\\\]b/", '\\\\\\\\b', $name);
        $binary = 'COLLATE utf8mb4_bin';
        $where = "name $binary regexp \"$regexp\"";
    }
    else {
        $where = "json_length(imply) = 0 order by rand()";
    }
    foreach (get_rows("select * from mathlib where $where limit $limit", MYSQLI_NUM) as $args)
        $lemma[] = get_lemma($args);
}
?>

<title><?php echo $name;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<body></body>
<?php
include_once 'script.php';
?>
<script src="static/unpkg.com/katex@0.16.21/dist/katex.min.js" defer></script>
<script src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js" defer></script>
<script type=module>
createApp('mathlib', {lemma: <?php echo std\encode($lemma);?>});
</script>
