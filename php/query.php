<?php
// use the following regex to remove error_log prints:
// ^ *error_log
require_once 'std.php';
include "include/bootstrap.inc.php";
include "include/tmpfile.inc.php";

if ($statement = $_POST['sql']?? null) {
    if (is_string($statement)) {
        die(std\encode(get_rows($statement)));
    }

    if (std\is_list($statement)) {
        $result = [];
        foreach ($statement as $sql) {
            try {
                $count = get_rows($sql);
                if (is_string($count)) {
                    if (preg_match("/File '(\S+.tsv)' already exists/", $count, $m)) {
                        error_log("unlink($m[1])");
                        unlink($m[1]);
                        error_log("reexecuting: $sql");
                        $count = get_rows($sql);
                    }
                }
                $result[] = $count;
            } catch (Exception $e) {
                error_log($e->getMessage());
            }
        }
        die(std\encode($result));
    }

    require_once 'mysql.php';
	if ($statement['get']) {
		die(std\encode([
            'password' => get_password(),
            'user' => get_user("pwds"),
        ]));
	}
	
    $data = &$statement['data'];
    [$database, $table] = get_db_table($statement);
    $ignore = std\boolval($statement['ignore']);
    $replace = std\boolval($statement['replace']);
    $step = isset($statement['step']) ? (int)$statement['step'] : 1000;
    die(std\encode(mysql\load_data("$database.$table", $data, $replace, $ignore, $step)));
}

$token = std\pop($_POST, 'token');
$user = get_user("pwds");
$host = std\pop($_GET, 'host', 'localhost');
$sql = std\pop($_GET, 'sql');
$kwargs = array_merge($_POST, $_GET);
// error_log('$kwargs = std\decode(' . std\encode(std\encode($kwargs)) . ');');
if ($sql) {
    require_once 'parser/sql.php';
    //error_log('$sql = '.$sql);
    $kwargs = array_merge($kwargs, SQL::compile($sql)->jsonSerialize());
}

$props = [];
foreach ($kwargs as $key => &$value) {
    if (std\fullmatch('/select|update|delete|set|alter|show|rename|revoke|grant|drop|from|into|where|with(_recursive)?|having|order|group|on|using|limit|offset|kwargs|union(_all)?/', $key))
        continue;
    
    $props[$key] = $value;
}

foreach ($props as $key => &$value) {
    unset($kwargs[$key]);
}

require_once 'mysql.php';
include_once 'utility.php';

[$database, $table, $is_union] = get_db_table($kwargs);
if ($update = $kwargs['update']?? null) {
    $cmd = 'update';
} elseif ($into = $kwargs['into']?? null) {
    $cmd = 'insert';
} elseif (isset($kwargs['delete'])) {
    unset($kwargs['delete']);
    $cmd = 'delete';
} elseif ($set = $kwargs['set']?? null) {
    $cmd = 'set';
} elseif ($show = $kwargs['show']?? null) {
    $cmd = 'show';
} else {
    $cmd = 'select';
    if (!$is_union) {
        if (! array_key_exists('from', $kwargs))
            $kwargs['from'] = ['corpus' => 'reward'];
        if (! array_key_exists('select', $kwargs))
            $kwargs['select'] = '*';
    }
}

$data = [];
$sample = std\pop($props, 'sample');

include "mysql/utility.php";
include "mysql/$cmd.php";

sample($data);
if ($sample)
    $props['sample'] = $sample;

include 'templates/table.php';
?>