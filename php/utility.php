<?php
// use the following regex to remove error_log prints:
// ^ *error_log
require_once 'std.php';
require_once 'mysql.php';

use std\Set, std\Queue;

function get_project_name()
{
    return basename(dirname(dirname(__file__)));
}

// to speed up the .php page rendering, disable error_log!!
function lean_to_module($lean)
{
    $module = [];
    for (;;) {
        $dirname = dirname($lean);
        $basename = basename($lean);
        if (std\equals($basename, 'Lemma')) {
            break;
        }

        $module[] = $basename;
        $lean = $dirname;
    }

    $module[0] = substr($module[0], 0, -strlen(std\get_extension($module[0])) - 1);
    $module = array_reverse($module);

    $module = join('.', $module);
    return $module;
}

function tokens_to_module($tokens, $section)
{
    $module = implode('.', array_map(fn ($tokens) => implode('.', $tokens), $tokens));
    if ($section)
        $module = $section . ".". $module;
    return $module;
}
function module_to_lean($module, $section = null)
{
    if ($section) {
        $module = implode('.', array_map(fn ($tokens) => implode('.', $tokens), $module));
        $module = $section . ".". $module;
    }
    return module_to_path($module) . ".lean";
}

function module_to_path($theorem, $dirname = "Lemma")
{
    $theorem = str_replace(".", "/", $theorem);

    return dirname(dirname(__file__)) . "/$dirname/$theorem";
}

function read_all_lean($dir)
{
    foreach (std\list_all_files($dir, 'lean') as $lean) {
        if (!str_ends_with($lean, ".echo.lean"))
            yield $lean;
    }
}

function split_module($theorem)
{
    $index = strrpos($theorem, ".");
    $package = substr($theorem, 0, $index);
    $new = substr($theorem, $index + 1);
    return [
        $package,
        $new
    ];
}


// input is a lean file
function modify_codes($python_file, $_proveCodes, $applyCodes = null)
{
    $proveCodes = [];
    foreach ($_proveCodes as $code) {
        $proveCodes[] = implode("\n", array_map(fn($s) => "    $s", explode("\n", $code))) . "\n\n";
    }

    $proveCodes[] = "\n";

    $lean = file($python_file);

    $count = count($lean);
    if ($applyCodes === null) {
        $codes = [];
        for ($i = 0; $i < $count; ++$i) {
            $statement = $lean[$i];
            $codes[] = $statement;
            if (preg_match("/^def prove\(/", $statement, $matches)) {
                break;
            }
        }
    } else {
        $codes = [
            "from util import *\n\n\n",
            $applyCodes . "\n"
        ];

        for ($i = 0; $i < $count; ++$i) {
            $statement = $lean[$i];
            if (preg_match("/^@prove/", $statement, $matches)) {
                break;
            }
        }
    }

    for ($i; $i < $count; ++$i) {
        if (preg_match("/^if __name__ == '__main__':/", $lean[$i], $matches)) {
            break;
        }
    }

    $updatedTime = null;
    $codesAfterProve = [];
    for (; $i < $count; ++$i) {
        $comment = $lean[$i];
        if (preg_match("/ *# *(updated|created) on (\d\d\d\d-\d\d-\d\d)/i", $comment, $m)) {
            switch ($m[1]) {
                case 'updated':
                    $timestamp = date('Y-m-d', time());
                    $comment = "# updated on $timestamp\n";
                    $updatedTime = "$timestamp";
                    break;
                case 'created':
                    $createdTime = $m[2];
                    break;
            }
        }

        $codesAfterProve[] = $comment;
    }

    if (!$updatedTime) {
        $timestamp = date('Y-m-d', time());
        $updatedTime = "$timestamp";
        if ($updatedTime != $createdTime) {
            $codesAfterProve[] = "# updated on $timestamp\n";
        }
    }

    array_push($codes, ...$proveCodes, ...$codesAfterProve);

    $code = join('', $codes);
    file_put_contents($python_file, $code);
}

function detect_dependency_by_module($module, $unique = true)
{
    // error_log("module = " . $module);
    $lean = module_to_lean($module);
    // error_log("lean = " . $lean);

    $array = detect_dependency_from_py($lean);
    if ($unique) {
        // https://www.php.net/manual/en/function.array-flip.php

        // $array = array_flip(array_flip($array));
        // $array = array_values($array);

        $set = new Set();
        $set->addAll($array);
        return $set;
    }
    return $array;
}

// input is a lean file
function detect_dependency_from_py($lean)
{
    $axioms = [];

    foreach (yield_from_lean($lean) as $dict) {
        // error_log(jsonify($dict));

        if (array_key_exists('a', $dict)) {
            foreach ($dict['a'] as $index => &$axiom) {
                $axioms[] = $axiom;
            }
        }
    }
    return $axioms;
}

function establish_dialetic_graph($theorem)
{
    $setProcessed = new Set();

    $G = [];
    $queue = new Queue();
    $queue->push($theorem);

    while (! $queue->isEmpty()) {
        $theorem = $queue->pop();
        if ($setProcessed->contains($theorem))
            continue;

        $setProcessed->add($theorem);

        foreach (detect_dependency_by_module($theorem) as $child) {
            $queue->push($child);
            $G[$theorem][] = $child;
        }
    }

    return $G;
}

function look_for_executable_python()
{
    switch (PHP_OS) {
        case 'Unix':
        case 'FreeBSD':
        case 'NetBSD':
        case 'OpenBSD':
        case 'Linux':
            return "python";
        case 'WINNT':

        case 'WIN32':

        case 'Windows':
            // return "D:\Users\dell\AppData\Local\Programs\Python\Python36\python.exe";
            return "\"D:\Program Files\Python\Python36\python.exe\"";
            // exec("echo %PATH%", $array, $ret);
            // $array = $array[0];
            // $array = explode(';', $array);
            // foreach ($array as $path) {
            // $path = "$path\python.exe";
            // if (file_exists($path)) {
            // return "\"$path\"";
            // }
            // }

        case 'CYGWIN_NT':

        case 'Darwin':

        case 'IRIX64':

        case 'SunOS':

        case 'HP-UX':
            return "python";
    }

    return "python";
}

function project_directory()
{
    return dirname(dirname(__file__)) . "/";
}

function axiom_directory()
{
    return project_directory() . "Lemma/";
}

function select_lemma_by_type($user, $type, $limit = 100)
{
    $_t_matrix = _t_matrix($user);
    $sql = <<<EOT
with $_t_matrix
select 
    distinct module
from 
    _t_matrix 
where 
    type = '$type'
order by 
    module
limit $limit
EOT;
    return get_rows($sql);
}

function select_lemma_missing($user, $limit = 100)
{
    $sql = <<<EOT
select
    module
from
    lemma
where
    user = '$user' and json_length(imports) > 0 and json_length(lemma) = 0
limit $limit
EOT;
    return get_rows($sql);
}

function select_lemma_by_regex($user, $regex, $binary = false, $limit = 100, $replacement = null)
{
    if ($binary)
        $binary = 'COLLATE utf8mb4_bin';
    else
        $binary = '';
    $where = "user = '$user' and module regexp \"$regex\" $binary";
    if ($replacement)
        $where .= " and json_length(imports) > 0";
    return get_rows("select module from lemma where $where limit $limit");
}

function select_lemma_by_like($user, $keyword, $binary = false, $limit = 100)
{
    if ($binary)
        $binary = " binary ";
    else
        $binary = " ";

    $keyword = str_replace('_', '\_', $keyword);
    $sql = "select module from lemma where user = '$user' and module like$binary\"%$keyword%\" limit $limit";
    return get_rows($sql);
}

function _t_type($user)
{
    return <<<EOT
_t_type as (
    select
        distinct type
    from
        lemma
        cross join json_table(
            error,
            '$[*]' columns(type text path '$.type')
        ) as jt
    where
        user = '$user'
)
EOT;
}
function _t_matrix($user)
{
    return <<<EOT
_t_matrix as (
    select
        module,
        type
    from
        lemma
        cross join json_table(
            error,
            '$[*]' columns(type text path '$.type')
        ) as jt
    where
        user = '$user'
)
EOT;
}
function select_count($user, $type = null)
{
    if ($type) {
        $_t_matrix = _t_matrix($user);
        $sql = <<<EOT
with $_t_matrix
select 
    count(distinct module)
from 
    _t_matrix 
where 
    type = '$type'
EOT;
    } else
        $sql = "select count(*) from lemma where user = '$user' and json_length(imports) > 0";
    foreach (get_rows($sql, MYSQLI_NUM) as $count) {
        return $count[0];
    }
}

function select_lemma_by_error($user)
{
    $_t_type = _t_type($user);
    $_t_matrix = _t_matrix($user);
    $sql = <<<EOT
with $_t_type, $_t_matrix
select 
    _t_matrix.module,
    json_unquote(json_extract(json_arrayagg(_t_type.type), '$[0]'))
from 
    _t_matrix
    join _t_type using (type)
group by
    module
EOT;
    yield from get_rows($sql, MYSQLI_NUM);
}

function fetch_from_mysql($user, $module)
{
    foreach (get_rows("select * from lemma where user = '$user' and module = \"$module\"") as $code) {
        return $code;
    }
}

function select_hierarchy($user, $module, $reverse = false)
{
    if ($reverse) {
        foreach (get_rows("select module from lemma where user = '$user' and json_contains(imports, '\"Lemma.$module\"')", MYSQLI_NUM) as [$result])
            yield $result;
    }
    else {
        foreach (get_rows("select imports from lemma where user = '$user' and module = \"$module\"", MYSQLI_NUM) as [$result])
            foreach (json_decode($result) as &$result) {
                if (preg_match('/^Lemma\.(.+)/', $result, $matches)) {
                    $result = $matches[1];
                    if ($result != 'Basic')
                        yield $result;
                }
            }
    }
}

function establish_hierarchy($user, $node, $reverse = false)
{
    $G = [];
    $setProcessed = new Set();

    $queue = new Queue();
    $queue->push($node);

    while (! $queue->isEmpty()) {
        $node = $queue->pop();
        if ($setProcessed->contains($node))
            continue;

        $setProcessed->add($node);

        // error_log("theoremSetProcessed = " . std\encode($setProcessed));
        foreach (select_hierarchy($user, $node, $reverse) as $child) {
            $queue->push($child);
            $G[$node][] = $child;
        }
    }

    $graph = new std\Graph();
    foreach ($G as $key => $value) {
        foreach ($value as $node) {
            $graph->insert($key, $node);
        }
    }

    return $graph;
}

function delete_from_lemma($user, $old, $regex = false)
{
    if ($regex) {
        // using regex engine;
        $sql = "delete from lemma where user = '$user' and module regexp \"^$old\"";
        $rows_affected = mysql\execute($sql);
    } else {
        $sql = "delete from lemma where user = '$user' and module = \"$old\"";
        $rows_affected = mysql\execute($sql);
    }

    if (! $rows_affected)
        error_log("$sql");
}

function update_axiom($user, $old, $new, $is_folder = false)
{
    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);
        $sql = "update lemma set module = regexp_replace(module, \"^$old_regex\.(.+)\", \"$new.$1\") where user = '$user' and module like \"$old.%\"";
    } else {
        $sql = "update lemma set module = \"$new\" where user = '$user' and module = \"$old\"";
    }

    // error_log("sql = $sql");
    $rows_affected = mysql\execute($sql);
    if ($rows_affected < 1)
        error_log("error found in $sql");
    if ($is_folder)
        return;
    $old = "Lemma." . str_replace("'", "''", $old);
    $new = "Lemma." . str_replace("'", "''", $new);
    $sql = <<<EOT
UPDATE `lemma`
SET `imports` = JSON_REPLACE(
  `imports`,
  JSON_UNQUOTE(JSON_SEARCH(`imports`, 'one', '$old')),
  '$new'
)
WHERE
    user = '$user' and 
    JSON_CONTAINS(imports, JSON_QUOTE('$old'))
EOT;
    $rows_affected = mysql\execute($sql);
    if ($rows_affected < 1)
        error_log("error found in $sql");
}

function update_lemma($user, $old, $new, $is_folder, $fn)
{
    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);

        $replaceDict = [];
        foreach (get_rows("select module from lemma where user = '$user' and module like \"$old.%\"", MYSQLI_NUM) as [$axiom]) {
            $oldAxiom = $axiom;
            $newAxiom = preg_replace("/^$old_regex\.(.+)/", "$new.$1", $oldAxiom);

            $replaceDict[$oldAxiom] = $newAxiom;
        }

        foreach ($replaceDict as $old => $new) {
            try {
                error_log("replace $oldAxiom with $newAxiom");
                $fn($old, $new, $user);
            }
            catch (Exception $e) {
                error_log($e->getMessage());
            }
        }
    } else
        $fn($old, $new, $user);
}
