<title>search</title>
<link rel=stylesheet href="node_modules/katex/dist/katex.min.css">
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'std.php';
$dict = empty($_POST) ? $_GET : $_POST;
$docstring = false;
if (array_key_exists("q", $dict)) {
    if (($dict["docstring"] ?? '') == 'on' || ($dict["fullText"] ?? '') == 'on')
        $docstring = $dict["q"];
    elseif ($dict["latex"] == 'on')
        $latex = $dict["q"];
}
else  {
    if (array_key_exists("type", $dict)) {
        $type = $dict["type"];
        $dict["q"] = null;
    }
    elseif (array_key_exists("latex", $dict)) {
        $latex = $dict["latex"];
        if ($dict["q"]) {
            $latex = $dict["q"];
        }
        else 
            $dict["q"] = null;
    } else {
        $dict["q"] = ".*";
        $dict["regularExpression"] = true;
    }
}

$q = $dict["q"];
$wholeWord = array_key_exists("wholeWord", $dict) ? true : false;
$caseSensitive = array_key_exists("caseSensitive", $dict) ? true : false;
$regularExpression = array_key_exists("regularExpression", $dict) ? true : false;
$limit = $dict["limit"]?? 100;
if (!$limit)
    $limit = 100;

$like = false;

$regex = $q;
if ($wholeWord)
    $regex = "\\\\b$regex\\\\b";
elseif ($regularExpression)
    $regex = str_replace("\\", "\\\\", $regex);
else
    $like = true;

if ($docstring) {
    require_once 'init.php';
    $qEsc = escape_string($docstring);
    $lim = (int) $limit;
    $offset = (int) ($dict["offset"] ?? 0);
    $rows = get_rows("
        SELECT l.module, d.lemma_id, d.text
        FROM docstring d
        JOIN lemma l ON l.id = d.id
        WHERE MATCH(d.text) AGAINST ('$qEsc' IN NATURAL LANGUAGE MODE)
        ORDER BY MATCH(d.text) AGAINST ('$qEsc' IN NATURAL LANGUAGE MODE) DESC
        LIMIT $lim OFFSET $offset
    ");
    $data = [];
    if (is_array($rows)) {
        foreach ($rows as $row) {
            $text = preg_replace('/\s+/', ' ', (string) $row['text']);
            $at = mb_stripos($text, $docstring);
            if ($at === false)
                $snippet = mb_substr($text, 0, 160);
            else {
                $from = max(0, $at - 50);
                $snippet = mb_substr($text, $from, 160);
                if ($from > 0)
                    $snippet = "…$snippet";
            }
            $data[] = [
                'module' => $row['module'],
                'lemmaId' => (int) $row['lemma_id'],
                'section' => 'proof',
                'latexId' => 0,
                'snippet' => $snippet,
            ];
        }
    }
} elseif ($latex) {
    // $_GET['user'] = 'user';
    // include "include/bootstrap.inc.php";
    // include "include/tmpfile.inc.php";
    //error_log('$latex = '.$latex);
    $data = std\json_post('http://localhost:5000/latex/similarity', ['latex' => $latex]);
}
else  {
    require_once 'init.php';
    $user = get_project_name();
    $replacement = array_key_exists("replacement", $dict) ? $dict["replacement"] : null;
    if ($like) {
        if ($regex == null) {
            if ($type == 'missing')
                $data = select_lemma_missing($user, $limit);
            else
                $data = select_lemma_by_type($user, $type, $limit);
        }
        else {
            $data = select_lemma_by_like($user, $regex, $caseSensitive, $limit);
            if (!$data && !$caseSensitive && ($index = strpos($regex, ' ')) !== false) {
                $regex = str_replace(' ', '.*', $regex);
                $data = select_lemma_by_regex($user, $regex, $caseSensitive, $limit, $replacement);
            }
        }
    } else
        $data = select_lemma_by_regex($user, $regex, $caseSensitive, $limit, $replacement);
    
    if ($replacement) {
        if ($like)
            $regex = str_replace(".", "\\.", $regex);
        else
            $regex = str_replace("\\\\", "\\", $regex);
        $regex = "/$regex/";
        if (!$caseSensitive)
            $regex .= 'i';
        foreach ($data as &$item)
            $item['replacement'] = preg_replace($regex, $replacement, $item['module']);
    }
}

include_once 'script.php';
?>
<script src="node_modules/katex/dist/katex.min.js" defer></script>
<script src="node_modules/katex/dist/contrib/auto-render.min.js" defer></script>
<script type=module>
createApp('searchResult', {
    data: <?php echo std\encode($data)?>,
    user: <?php echo std\encode($user)?>,
    q: <?php echo std\encode($q)?>,
    regularExpression: <?php echo std\encode($regularExpression)?>,
    wholeWord: <?php echo std\encode($wholeWord)?>,
    caseSensitive: <?php echo std\encode($caseSensitive)?>,
    docstring: <?php echo std\encode($docstring? true : false)?>,
    latex: <?php echo std\encode($latex)?>,
    replacement: <?php echo std\encode($replacement)?>,
    limit: <?php echo $limit?>,
});
</script>