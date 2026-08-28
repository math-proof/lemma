<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<title>search</title>
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'std.php';
$dict = empty($_POST) ? $_GET : $_POST;

// if (! $dict) {
//     // https://www.php.net/manual/en/function.getopt.php
//     $dict = getopt("", [
//         'keyword::',
//         'regularExpression::',
//         'caseSensitive::',
//         'wholeWord::',
//         'latex::',
//     ]);
// }

if (array_key_exists("keyword", $dict)) {
    if ($dict["latex"] == 'on') {
        $latex = $dict["keyword"];
    }
}
else  {
    if (array_key_exists("state", $dict)) {
        $state = $dict["state"];
        $dict["keyword"] = null;
    }
    elseif (array_key_exists("latex", $dict)) {
        $latex = $dict["latex"];
        if ($dict["keyword"]) {
            $latex = $dict["keyword"];
        }
        else 
            $dict["keyword"] = null;
    } else {
        $dict["keyword"] = ".*";
        $dict["regularExpression"] = true;
    }
}

$keyword = $dict["keyword"];
$wholeWord = array_key_exists("wholeWord", $dict) ? true : false;
$caseSensitive = array_key_exists("caseSensitive", $dict) ? true : false;
$regularExpression = array_key_exists("regularExpression", $dict) ? true : false;
$limit = $dict["limit"]?? 100;
if (!$limit)
    $limit = 100;
// error_log("wholeWord = $wholeWord");
// error_log("caseSensitive = $caseSensitive");
// error_log("regularExpression = $regularExpression");
// error_log("latex = $latex");

$like = false;

$regex = $keyword;
if ($wholeWord) {
    $regex = "\\\\b$regex\\\\b";
} else if ($regularExpression) {
    $regex = str_replace("\\", "\\\\", $regex);
} else {
    $like = true;
}

if ($latex){
    // $_GET['user'] = 'user';
    // include "include/bootstrap.inc.php";
    // include "include/tmpfile.inc.php";    
    //error_log('$latex = '.$latex);
    $list = std\json_post('http://localhost:5000/latex/similarity', ['latex' => $latex]);
}
else  {
    require_once 'init.php';
    $user = get_user();
    if ($like) {
        if ($regex == null) {
            $list = select_axiom_by_state($user, $state, $limit);
        } else {
            $list = select_axiom_by_like($user, $regex, $caseSensitive, $limit);
        }
    } else {
        $list = select_axiom_by_regex($user, $regex, $caseSensitive, $limit);
    }
    
    $replacement = array_key_exists("replacement", $dict) ? $dict["replacement"] : null;
    if ($replacement) {
        if ($like)
            $regex = str_replace(".", "\\.", $regex);
        else
            $regex = str_replace("\\\\", "\\", $regex);
        $regex = "/$regex/";
        if (!$caseSensitive)
            $regex .= 'i';
        // error_log("regex = $regex");    
        // error_log("replacement = $replacement");
        foreach ($list as &$item) {
            
            // error_log("item = $item");
            $item = [$item, preg_replace($regex, $replacement, $item)];
        }
    }

    $list = std\encode($list);
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
var latex = <?php echo std\encode($latex)?>;
var list = <?php echo $list?>;
if (latex) {
    createApp('searchLatexResult', {
        list,
	    latex,
    });
}
else {
    createApp('searchResult', {
        list,
        user: <?php echo std\encode($user)?>,
        keyword: <?php echo std\encode($keyword)?>,
        regularExpression: <?php echo std\encode($regularExpression)?>,
        wholeWord: <?php echo std\encode($wholeWord)?>,
        caseSensitive: <?php echo std\encode($caseSensitive)?>,
        latex: <?php echo std\encode($latex)?>,
        replacement: <?php echo std\encode($replacement)?>,
        limit: <?php echo $limit?>,
    });
}
</script>