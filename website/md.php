<?php

$PATH_INFO = isset($_SERVER["PATH_INFO"])? $_SERVER["PATH_INFO"]: '';

if (preg_match('/(\w+)\/.+\.md/', $PATH_INFO, $m)) {
    $lang = $m[1];
} else {
    require_once '../php/std.php';
    
    $path = dirname(__file__) . "/md$PATH_INFO";
    $prefix = str_starts_with($PATH_INFO, '/')? substr($PATH_INFO, 1): $PATH_INFO;
    
    error_log("prefix = $prefix");
    
    $index = strrpos($prefix, '/');
    if ($index !== false) {
        $_prefix = substr($prefix, $index + 1);
        if ($_prefix) {
            $prefix = $_prefix;
        }
        else {
            $prefix = $_SERVER["REQUEST_URI"];
            if (str_ends_with($prefix, '/'))
                $prefix = std\slice($prefix, 0, -1);
        }
    }
    elseif (!$prefix)
        $prefix = "md.php";
    
    error_log("prefix = $prefix");
    foreach (scandir($path) as $name) {
        switch ($name) {
            case '.':
            case '..':
                break;
            default:
                $file = "$path/$name";
                if (is_dir($file)) {
                    $md = "$file.md";
                    if (!is_file($md))
                        echo "<a href=$prefix/$name>$name</a><br><br>";
                } else {
                    echo "<a href=$prefix/$name>$name</a><br><br>";
                }
        }
    }

    exit();
}

switch ($lang) {
    case 'en':
        $title = 'MarkDown Documents';
        break;
    case 'zh':
        $title = '标记文档';
        break;
    case 'fr':
        $title = 'Documents Markdown';
        break;
    default:
        $title = 'MarkDown Documents';
        break;
}

?>

<html>

<head>
<meta http-equiv="content-type" content="text/html;charset=utf-8" />
<link rel=stylesheet href="static/unpkg.com/highlight.js/8.8.0/styles/default.min.css" />
<title><?php echo $title ?></title>
<style>
body {
	background-color: rgb(199, 237, 204);
	margin-left: 2.5em;
}
</style>
</head>

<body>
	<div id=content></div>
</body>

</html>

<script src="/axiom/static/unpkg.com/highlight.js/8.8.0/highlight.min.js"></script>
<script src="/axiom/static/unpkg.com/marked@2.1.3/marked.min.js"></script>
<script src="/axiom/static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="/axiom/static/unpkg.com/qs@6.10.2/dist/qs.js"></script>
<script src="/axiom/static/js/std.js"></script>
<script> 
	hljs.initHighlightingOnLoad();
	var url = `/axiom/website/md<?php echo $PATH_INFO ?>`;
	get(url).then(text =>{
    	url = url.slice(0, -3);
    	var newText = [];
    	var start = 0;
    	for (let m of text.matchAll(/(?<=\n)!\[(.+)\]\((.+)\)/g)){            	
        	var title = m[1];            	
        	var address = url + m[2].match(/[^\/]+(\/.+)/)[1];
        	var link = `![${title}](${address})`;
        	console.log(link);

        	newText.push(text.slice(start, m.index));
        	newText.push(link);
        	start = m.index + m[0].length;
        }

    	newText.push(text.slice(start));
    	text = newText.join('');

        $("#content").innerHTML = marked(text);
	});

</script>