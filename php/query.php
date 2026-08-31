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
?>