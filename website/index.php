<?php
if (array_key_exists('lang', $_GET)) {
    $lang = $_GET['lang'];
} else {
    $HTTP_ACCEPT_LANGUAGE = $_SERVER['HTTP_ACCEPT_LANGUAGE'];
    error_log("HTTP_ACCEPT_LANGUAGE = $HTTP_ACCEPT_LANGUAGE");

    if (isset($HTTP_ACCEPT_LANGUAGE) && strlen($HTTP_ACCEPT_LANGUAGE) > 1) {
        $x = explode(",", $HTTP_ACCEPT_LANGUAGE);
        foreach ($x as $val) {
            if (preg_match("/(.*);q=([0-1]{0,1}.\d{0,4})/i", $val, $matches))
                $langue[$matches[1]] = (float) $matches[2];
            else
                $langue[$val] = 1.0;
        }
        $qval = 0.0;
        foreach ($langue as $key => $value) {
            if ($value > $qval) {
                $qval = (float) $value;
                $lang = $key;
            }
        }
        if (strpos("-", $lang) >= 0){
            $lang = explode("-", $lang)[0];
        }
        //error_log("langue = ".json_encode($langue));
        //error_log("lang = ".$lang);        
    }
    else{
        $lang = 'zh';
    }
}

if (array_key_exists('section', $_GET)) {
    $section = $_GET['section'];
} else {
    $section = "home";
}

switch ($lang) {
    case 'zh':
        $title = '算法形式化定理库';
        $home = '网站主页';
        $faq = '常见问题';
        $bugReport = '故障报告';

        $userGuide = '用户指南';
        $participation = '项目参与';
        $contact = '联系作者';
        $endeavour = '我的奋斗';
        // $elementaryExamples = '初级例题';
        // $intermediateExamples = '中级例题';
        // $advancedExamples = '高级例题';
        $designManual = '设计文档';
        $languageSelect = '选择语言';

        $history = '探索历程';
        $userManual = '操作手册';
        $signIn = '登陆';
        $signUp = '注册';
        $programmingReference = "编程参考";
        break;
    default:
    case 'en':
        $title = 'Formalized Algorithmic Theorem Library';
        $home = 'Home';
        $faq = 'Frequently Asked Questions';
        $bugReport = 'Bug Report';
        
        $userGuide = 'User Guide';
        $participation = 'Participation';
        $contact = 'Contact Us';
        $endeavour = 'Lifelong Endeavour';
        // $elementaryExamples = 'Elementary Examples';
        // $intermediateExamples = 'Intermediate Examples';
        // $advancedExamples = 'Advanced Examples';
        $designManual = 'Design Manual';
        
        $languageSelect = 'Select Language';
        
        $history = 'Breif History';
        
        $userManual = 'User Manual';
        $signIn = 'Sign In';
        $signUp = 'Sign UP';
        $programmingReference = "Programming Reference";
        break;
}
?>

<html>
<head>
<meta http-equiv="content-type" content="text/html;charset=utf-8" />
<link href="style.css" rel="stylesheet" type="text/css" />
<title><?php echo $title ?></title>
</head>
<body>
	<div id='container'>

		<div id='header' align='center'>
			<font size=200%> <?php echo $title ?></font>

			<div style="float:right">
				<?php echo $languageSelect ?>
				<select align='left' onchange="location.href = `?lang=${this.value}`">
					<option value=en <?php echo $lang == 'en'? 'selected': ''?>>English</option>
					<option value=zh <?php echo $lang == 'zh'? 'selected': ''?>>简体中文</option>
					<option value=fr <?php echo $lang == 'fr'? 'selected': ''?>>Français</option>
				</select>
				<br>
				<a href='signin.php?lang=<?php echo $lang ?>' align='left'><?php echo $signIn ?></a>
				<a href='signup.php?lang=<?php echo $lang ?>' align='left'><?php echo $signUp ?></a>
			</div>

		</div>

		<hr />

		<div id='content_container'>

			<div id='sidebar'>
				<div class='sidebar_heading'>
					<a href='?lang=<?php echo $lang ?>'><?php echo $home ?></a>
				</div>
				<br>
				<div class='sidebar_body'>
					<a href='?lang=<?php echo $lang ?>&section=bugReport'><?php echo $bugReport ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='?lang=<?php echo $lang ?>&section=participation'><?php echo $participation ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='?lang=<?php echo $lang ?>&section=contact'><?php echo $contact ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='?lang=<?php echo $lang ?>&section=history'><?php echo $history ?></a>
				</div>
				<div class='sidebar_body'>
					<a href='?lang=<?php echo $lang ?>&section=endeavour'><?php echo $endeavour ?></a>
				</div>

				<br>
				<div class='sidebar_heading'><?php echo $userGuide ?></div>
				<br>
				<div class='sidebar_body'>
					<a href="?lang=<?php echo $lang ?>&section=faq"
						title="<?php echo $faq ?>"><?php echo $faq ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="?lang=<?php echo $lang ?>&section=designManual"
						title="<?php echo $designManual ?>"><?php echo $designManual ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="?lang=<?php echo $lang ?>&section=userManual"
						title="<?php echo $userManual ?>"><?php echo $userManual ?></a>
				</div>
				<div class='sidebar_body'>
					<a href="md.php/<?php echo $lang ?>/programming"
						title="<?php echo $programmingReference ?>"><?php echo $programmingReference ?></a>
				</div>
			</div>

			<div id='content'></div>
		</div>
	</div>

</body>
</html>

<script	src="../static/unpkg.com/highlight.js/8.8.0/highlight.min.js"></script>
<script src="../static/unpkg.com/marked@2.1.3/marked.min.js"></script>
<script src="../static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="../static/unpkg.com/qs@6.10.2/dist/qs.js"></script>
<script src="../static/js/std.js"></script>
<script type=module>

hljs.initHighlightingOnLoad();

var url = `../website/md/<?php echo "$lang/$section.md" ?>`;

var text = await get(url);
url = url.slice(0, -3);

text = text.transform(/(?<=\n)!\[(.+)\]\((.+)\)/g, m=>{
	var title = m[1];
	var address = url + m[2].match(/[^\/]+(\/.+)/)[1];
	return `![${title}](${address})`;
});

text = text.transform(/<script( type=module)?>([\s\S]*)<\/script>/g, m=>{
    var script = m[2];
    if (m[1])
        script = `(async function(){${script}})();`;

    console.log('eval: ', script);
    setTimeout(()=>eval(script), 100);
    return '';
});

$("#content").innerHTML = marked(text);

</script>