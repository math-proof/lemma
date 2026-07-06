<?php
$text = str_replace("\r", '', file_get_contents($leanFile));
?>
<title><?php echo htmlspecialchars($title, ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8'); ?></title>
<body>
<textarea readonly spellcheck="false" style="width:100%;height:92vh;box-sizing:border-box;font-family:monospace;font-size:14px;line-height:1.4;border:1px solid #ccc;padding:8px">
<?php echo htmlspecialchars($text, ENT_QUOTES | ENT_SUBSTITUTE, 'UTF-8');?>
</textarea>
</body>
