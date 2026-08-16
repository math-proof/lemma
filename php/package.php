<?php
// error_log("path_info = $path_info");
if (! str_ends_with($path_info, '/')) {
    $path_info .= "/";
}

$theorems = [];

$packages = [];

foreach (scandir($path_info) as $file) {
    switch ($file) {
        case '.':
        case '..':
            break;
        default:
            if (str_ends_with($file, '.lean')) {
                if (str_ends_with($file, '.echo.lean'))
                    break;
                $theorems[] = substr($file, 0, - 5);
            } elseif (is_dir($path_info . $file)) {
                $packages[] = $file;
            }
    }
}

if (str_ends_with($title, '/'))
    $title = substr($title, 0, - 1);
?>

<title><?php echo $title;?></title>
<body></body>
<?php
include_once 'script.php';
?>

<script type=module>
createApp('axiomContents', {
	packages: <?php echo std\encode($packages)?>,
	theorems: <?php echo std\encode($theorems)?>,
});
</script>



