<title>search</title>
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<?php
require_once 'utility.php';
require_once 'mysql.php';
require_once 'std.php';
$dict = empty($_POST) ? $_GET : $_POST;
$fullText = false;
if (array_key_exists("q", $dict)) {
    if ($dict["fullText"] == 'on')
        $fullText = $dict["q"];
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

if ($fullText) {
    if ($wholeWord || $regularExpression) {
        $fullText = $regex;
        $P = "P";
    }
    else {
        $P = "";
        $fullText = str_replace("\\", "\\\\", $fullText);
    }
    $fullText = str_replace("\"", "\\\"", $fullText);
    if (std\is_linux()) {
        // the following command is used to search for all typeclass names in the Lemma directory
        // grep -rhP --include="*.lean" --exclude="*.echo.lean" -o "(?<=\[)\w+(?= \p{L}\])" Lemma | sort -u        
        exec("grep -rn$P --include=*.lean --exclude=*.echo.lean \"$fullText\" Lemma | head -n $limit", $output_array);
        $sep = '/';
    }
    else {
        exec("powershell.exe -Command \"[System.Console]::OutputEncoding = [System.Text.Encoding]::UTF8; \$OutputEncoding = [System.Text.Encoding]::UTF8; Get-ChildItem -Path Lemma -Recurse -Include *.lean -Exclude *.echo.lean | Select-String -CaseSensitive -Pattern '" . addslashes($fullText) . "' -AllMatches | Select-Object -First $limit\"", $output_array);
        $sep = '\\\\';
    }

    $data = [];
    foreach ($output_array as &$item) {
        [$file, $line, $text] = explode(":", $item, 3);

        if (preg_match("#^Lemma$sep(.*)\.lean$#", $file, $matches)) {
            $data[] = [
                'module' => str_replace($sep, ".", $matches[1]),
                'line' => $line,
                'text' => $text,
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
    if ($like) {
        if ($regex == null)
            $data = select_lemma_by_type($user, $type, $limit);
        else {
            $data = select_lemma_by_like($user, $regex, $caseSensitive, $limit);
            if (!$data && !$caseSensitive && ($index = strpos($regex, ' ')) !== false) {
                $regex = str_replace(' ', '.*', $regex);
                $data = select_lemma_by_regex($user, $regex, $caseSensitive, $limit);
            }
        }
    } else
        $data = select_lemma_by_regex($user, $regex, $caseSensitive, $limit);
    
    $replacement = array_key_exists("replacement", $dict) ? $dict["replacement"] : null;
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
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script type=module>
createApp('searchResult', {
    data: <?php echo std\encode($data)?>,
    user: <?php echo std\encode($user)?>,
    q: <?php echo std\encode($q)?>,
    regularExpression: <?php echo std\encode($regularExpression)?>,
    wholeWord: <?php echo std\encode($wholeWord)?>,
    caseSensitive: <?php echo std\encode($caseSensitive)?>,
    fullText: <?php echo std\encode($fullText? true : false)?>,
    latex: <?php echo std\encode($latex)?>,
    replacement: <?php echo std\encode($replacement)?>,
    limit: <?php echo $limit?>,
});
</script>