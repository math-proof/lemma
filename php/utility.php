<?php
// use the following regex to remove error_log prints:
// ^ *error_log
require_once 'std.php';
require_once 'mysql.php';

use std\Set, std\Text, std\Queue;

function get_user() {
    return basename(dirname(dirname(__file__)));
}

// to speed up the .php page rendering, disable error_log!!
function py_to_module($py)
{
    $module = [];
    $pythonFile = $py;
    for (;;) {
        $dirname = dirname($pythonFile);
        $basename = basename($pythonFile);
        if (std\equals($basename, 'Lemma')) {
            break;
        }

        $module[] = $basename;
        $pythonFile = $dirname;
    }

    $module[0] = substr($module[0], 0, - strlen(std\get_extension($module[0])) - 1);
    $module = array_reverse($module);

    if (std\equals(end($module), '__init__')) {
        array_pop($module);
    }

    $module = join('.', $module);
    return $module;
}

function php_to_py($php)
{
    // error_log("php file = $php");
    $py = str_replace('.php', '.py', $php);
    if (! file_exists($py)) {
        $py = str_replace('.php', '/__init__.py', $php);
    }
    // error_log("python file = $py");
    assert(file_exists($py), "file_exists($py)");

    return $py;
}

function module_to_py($theorem)
{
    $full_theorem_path = module_to_path($theorem);
    $py = $full_theorem_path . ".py";
    if (! file_exists($py)) {
        $py = $full_theorem_path . '/__init__.py';
    }

    return $py;
}

function module_to_path($theorem)
{
    $theorem = str_replace(".", "/", $theorem);

    return dirname(dirname(__file__)) . "/Lemma/$theorem";
}

function reference(&$value)
{
    if (is_array($value)) {
        foreach ($value as &$element) {
            $element = reference($element);
        }
        $value = join(', ', $value);
        return $value;
    }
    if (preg_match('/\d+/', $value, $matches)) {
        $value = (int) $value;
        if ($value < 0)
            return "plausible";
        return "Eq[$value]";
    } else {
        return "Eq.$value";
    }
}

function println($param, $file = null)
{
    if (is_array($param)) {
        $param = jsonify($param);
    }

    if ($file) {
        echo "called in $file:<br>";
    }
    print_r($param);
    print_r("<br>");
}

function read_all_axioms($dir)
{
    foreach (std\list_directory($dir) as $directory) {
        foreach (std\list_all_files($directory, 'py') as $py) {
            if (! std\equals(basename($py), "__init__.py")) {
                yield [
                    $py,
                    substr($py, 0, - 2) . 'php'
                ];
            } else {
                yield [
                    $py,
                    substr($py, 0, - strlen('/__init__.py')) . '.php'
                ];
            }
        }
    }
}

function retrieve_all_dependency()
{
    foreach (read_all_axioms(dirname(__file__)) as [$py, $php]) {
        $from = py_to_module($php);

        $count = [];
        foreach (detect_dependency_from_py($py) as $to) {
            if (! array_key_exists($to, $count)) {
                $count[$to] = 0;
            }

            ++ $count[$to];
        }

        yield [
            $from,
            $count
        ];
    }
}

function is_def_start($funcname, $statement)
{
    return preg_match("/^def +$funcname\([^)]*\) *: */", $statement);
}

function analyze_apply($py, &$i)
{
    $count = count($py);
    $provability = null;
    for (; $i < $count; ++ $i) {
        $statement = $py[$i];
        if (is_def_start('prove', $statement))
            break;

        if (preg_match('/^@prove(.+)/', $statement, $matches)) {
            if (preg_match('/^\((.+)=(.+)\)/', $matches[1], $matches))
                $provability = $matches[1];
        }
    }

    return $provability;
}

function detect_axiom(&$statement)
{
    // Eq << Eq.x_j_subset.apply(Discrete.Set.subset.nonempty, Eq.x_j_inequality, evaluate=False)
    if (preg_match('/\.apply\((.+)\)/', $statement, $matches)) {
        $theorem = preg_split("/\s*,\s*/", $matches[1], - 1, PREG_SPLIT_NO_EMPTY)[0];
        // error_log('create_a_tag: ' . __LINE__);
        return [
            $theorem
        ];
    } else {
        return [];
    }
}

function detect_axiom_given_theorem(&$theorem, &$statement)
{
    if (startsWith($theorem, '.') || startsWith($theorem, 'Eq')) {
        // consider the case
        // Eq[-2].this.args[0].apply(Algebra.Cond.Cond.to.And, invert=True, swap=True)
        return detect_axiom($statement);
    }

    if (strpos($theorem, 'Eq.') === false) {
        return [
            $theorem
        ];
    }

    return detect_axiom($statement);
}

// input is a py file
function yield_from_py($python_file)
{
    $py = file($python_file);
    $count = count($py);

    for ($i = 0; $i < $count; ++ $i) {
        $statement = $py[$i];
        if (preg_match('/^from +(.+) +import +(.*)/', $statement, $matches)) {

            $prefix = $matches[1];
            $namespaces = $matches[2];
            $namespaces = preg_split("/[\s,]+/", $namespaces, - 1, PREG_SPLIT_NO_EMPTY);

            if (end($namespaces) == '\\') {
                array_pop($namespaces);

                $statement = $py[++ $i];

                $namespaces_addition = preg_split("/[\s,]+/", $statement, - 1, PREG_SPLIT_NO_EMPTY);

                array_push($namespaces, ...$namespaces_addition);
            }
            continue;
        }

        if (preg_match('/^import +(.+)/', $statement, $matches)) {
            $packages = $matches[1];
            $packages = preg_split("/\s*,\s*/", $packages, - 1, PREG_SPLIT_NO_EMPTY);

            foreach ($packages as $package) {
                $package = preg_split("/\s+/", $package, - 1, PREG_SPLIT_NO_EMPTY);

                switch (count($package)) {
                    case 1:
                        $package = $package[0];
                        break;
                    default:
                        break;
                }
            }

            continue;
        }

        if (is_def_start('apply', $statement)) {
            yield [
                'line' => $i
            ];

            $provability = analyze_apply($py, $i);
            yield [
                'line' => $i,
                'provability' => $provability
            ];

            break;
        }
    }
    ++ $i;

    if ($i < $count) {
        $statement = $py[$i];

        if (preg_match('/^    from Lemma import (.+)/', $statement, $matches)) {
            $section = explode(", ", $matches[1]);
            yield [
                'line' => $i,
                'section' => $section
            ];;
            ++ $i;
        }

        for (; $i < $count; ++ $i) {
            $statement = $py[$i];
            $statement = rtrim($statement);
            // skip empty lines;
            if (preg_match('/^\s*$/', $statement)) {
                continue;
            }

            // the start of the next global statement other than def prove
            if (preg_match('/^\w/', $statement)) {
                break;
            }

            // stop analyzing if return statement is encountered.
            if (preg_match('/^    return\b.*$/', $statement)) {
                $statement = rtrim($statement);
                $statement = substr($statement, 4);

                yield [
                    'line' => $i,
                    'unused' => true,
                    'statement' => $statement
                ];

                for (++ $i; $i < $count; ++ $i) {
                    $statement = $py[$i];

                    $statement = rtrim($statement);
                    // skip empty lines;
                    if (preg_match('/^\s*$/', $statement)) {
                        continue;
                    }

                    // the start of the next global statement other than def prove
                    if (preg_match('/^\w/', $statement)) {
                        break;
                    }

                    $yield = [
                        'line' => $i,
                        'unused' => true
                    ];

                    // cope with comments starting with #
                    if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                        $yield['comment'] = true;
                        $yield['statement'] = "#" . $matches[1];
                        yield $yield;
                        continue;
                    }

                    $statement = substr($statement, 4);
                    $yield['statement'] = $statement;
                    yield $yield;
                }

                break;
            }

            $yield = [
                'line' => $i
            ];

            // cope with comments starting with #
            if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                $yield['comment'] = true;
                $yield['statement'] = "#" . $matches[1];

                yield $yield;
                continue;
            }

            $statement = substr($statement, 4);

            $yield['statement'] = $statement;

            if (preg_match('/(=|<<) *apply\(/', $statement, $matches)) {
                
                $yield['module'] = py_to_module($python_file);
            }            
            else if (match_section($statement, $matches)) {
                $index = 0;

                $dict = [];
                foreach ($matches as $module) {
                    $module = $module[0];
                    if (str_ends_with($module, '.apply')) {
                        $module = substr($module, 0, - 6);
                    }
                    assert(is_string($module), "module is not a string: $module, statement = $statement");
                    $index = strpos($statement, $module, $index);
                    $dict[$index] = $module;

                    $index += strlen($module);
                }
                $yield['a'] = $dict;
            }             
            yield $yield;
        }

        for (; $i < $count; ++ $i) {
            $statement = $py[$i];
            $statement = rtrim($statement);
            // cope with comments starting with #
            if (preg_match('/^\s*#(.*)/', $statement, $matches)) {
                if (preg_match('/(created|updated) on (\d\d\d\d-\d\d-\d\d)/', $matches[1], $matches)) {
                    yield [
                        'line' => $i,
                        'comment' => true,
                        'statement' => '',
                        $matches[1] => $matches[2]
                    ];
                }
            }
        }
    }
}

function match_section($statement, &$matches)
{
    $sections = std\listdir(dirname(dirname(__FILE__)) . "/Lemma/");
	$sectionRegex = implode('|', $sections);
    return preg_match_all("/\\b(?:$sectionRegex)(?:\\.\\w+)+/", $statement, $matches, PREG_SET_ORDER);
}

function has_unterminated_parantheses($statement) {
    return substr_count($statement, "(") > substr_count($statement, ")");
}

function insert_section(&$proveCodes)
{
    $from_axiom_import = determine_section($proveCodes);
    if ($from_axiom_import != "") {
        if (is_array($proveCodes)) {
            std\array_insert($proveCodes, 0, $from_axiom_import);
        } else {
            $proveCodes = "$from_axiom_import\n$proveCodes";
        }
    }
    return $proveCodes;
}

function determine_section($proveCodes)
{
    if (is_array($proveCodes)) {
        $proveCodes = implode("\n", $proveCodes);
    }

    $section = [];

    if (match_section($proveCodes, $matches)) {
        foreach ($matches as $module) {
            $section[] = explode(".", $module[0])[0];
        }
    }

    if (! count($section)) {
        return "";
    }

    $section = new std\Set($section);
    $section = $section->jsonSerialize();
    $section = implode(", ", $section);
    $section = "from Lemma import $section";
    return $section;
}

function replace_into_init($package, $old, $new)
{
    $folder = module_to_path($package);
    $__init__ = $folder . "/__init__.py";
    $__init__ = new Text($__init__);
    $lineNum = - 1;
    foreach ($__init__ as $line) {
        ++ $lineNum;

        if (! preg_match('/^from *. *import +(.+)/', $line, $m))
            continue;

        $theorems = preg_split('/\s*,\s*/', $m[1]);
        $index = array_search($old, $theorems);
        if ($index !== false) {
            $theorems[$index] = $new;
            $theorems = implode(', ', $theorems);

            $__init__->setitem($lineNum, "from . import $theorems");
            return;
        }
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

function insert_into_init($package, $new = null)
{
    error_log("insert into $package with $new");
    if ($new === null) {
        [$package, $new] = split_module($package);

        if (strpos($package, ".") !== false)
            insert_into_init($package);
    }

    $folder = module_to_path($package);

    $__init__ = $folder . "/__init__.py";
    $__init__ = new Text($__init__);

    foreach ($__init__ as $line) {
        if (! preg_match('/^from *. *import +(.+)/', $line, $m))
            continue;
        $theorems = preg_split('/\s*,\s*/', $m[1]);
        $index = array_search($new, $theorems);
        if ($index !== false) {
            return;
        }
    }

    if (! $__init__->isEmpty() && ! $__init__->endsWith("\n"))
        $__init__->append("");

    $__init__->append("from . import $new");
}

function delete_from_init($package, $theorem = null)
{
    if ($theorem === null)
        [$package, $theorem] = split_module($package);

    $folder = module_to_path($package);

    error_log("package = $package, theorem = $theorem");
    $initPy = $folder . "/__init__.py";

    $lineNum = - 1;

    $imports = 0;

    $lineNumIndex = - 1;
    $content = null;
    $emptyLines = 0;

    if (file_exists($initPy))
    {
        $__init__ = new Text($initPy);
        foreach ($__init__ as $line) {
            if (trim($line) == "")
                $emptyLines += 1;
            ++ $lineNum;
            if (! preg_match('/^from *. *import +(.+)/', $line, $m))
                continue;

            ++ $imports;
            $theorems = preg_split('/\s*,\s*/', $m[1]);
            error_log(std\encode($theorems));

            $index = array_search($theorem, $theorems);
            if ($index !== false) {

                error_log("index = $index");

                std\array_delete($theorems, $index);

                $theorems = implode(', ', $theorems);

                error_log("theorems = $theorems");

                if ($theorems != "") {
                    ++ $imports;
                    $content = "from . import $theorems";
                }

                $lineNumIndex = $lineNum;
            }
        }

        if ($content)
            $__init__->setitem($lineNum, $content);
        else
            $__init__->delitem($lineNumIndex);
    }

    if ($imports == 1) {
        error_log("imports = 1");
        
        error_log("folder = $folder");
        $subFolder = "$folder/$theorem";
        foreach (std\list_all_files($folder, 'py') as [$pyFile, $php]) {
//             if (str_starts_with($subFolder)){
//                 error_log("detect py file $pyFile within the deleted $subFolder, so continue the process!");
//                 continue;
//             }
            
//             if (file_exists($pyFile)){
                error_log("detect py file $pyFile within the folder $folder, so cease the deleting process!");
                return;            
//             }
        }
        
        $lineNum -= $emptyLines;
        if ($lineNum > 0) {
            rename($initPy, "$folder.py");
            std\deleteDirectory($folder);
        } else {
            std\deleteDirectory($folder);
            delete_from_init($package);
        }
    }
    
    return;
}

// input is a py file
function modify_codes($python_file, $_proveCodes, $applyCodes = null)
{
    $proveCodes = [];
    foreach ($_proveCodes as $code) {
        $proveCodes[] = implode("\n", array_map(fn ($s) => "    $s", explode("\n", $code))) . "\n\n";
    }

    $proveCodes[] = "\n";

    $py = file($python_file);

    $count = count($py);
    if ($applyCodes === null) {
        $codes = [];
        for ($i = 0; $i < $count; ++ $i) {
            $statement = $py[$i];
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

        for ($i = 0; $i < $count; ++ $i) {
            $statement = $py[$i];
            if (preg_match("/^@prove/", $statement, $matches)) {
                break;
            }
        }
    }

    for ($i; $i < $count; ++ $i) {
        if (preg_match("/^if __name__ == '__main__':/", $py[$i], $matches)) {
            break;
        }
    }

    $updatedTime = null;
    $codesAfterProve = [];
    for (; $i < $count; ++ $i) {
        $comment = $py[$i];
        if (preg_match("/ *# *(updated|created) on (\d\d\d\d-\d\d-\d\d)/i", $comment, $m)) {
            switch ($m[1]){
                case "updated":
                    $timestamp = date('Y-m-d', time());
                    $comment = "# updated on $timestamp\n";
                    $updatedTime = "$timestamp";
                    break;
                case "created":
                    $createdTime = $m[2];
                    break;
            }
        }

        $codesAfterProve[] = $comment;
    }

    if (!$updatedTime){
        $timestamp = date('Y-m-d', time());
        $updatedTime = "$timestamp";
        if ($updatedTime != $createdTime){
            $codesAfterProve[] = "# updated on $timestamp\n";            
        }
    }

    array_push($codes, ...$proveCodes, ...$codesAfterProve);

    $code = join('', $codes);
    file_put_contents($python_file, $code);
}

function read_all_php($dir)
{
    foreach (std\list_directory($dir) as $directory) {
        foreach (std\list_all_files($directory, 'php') as $php) {
            yield $php;
        }
    }
}

function detect_dependency_by_module($module, $unique = true)
{
    // error_log("module = " . $module);
    $py = module_to_py($module);
    // error_log("py = " . $py);

    $array = detect_dependency_from_py($py);
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

// input is a py file
function detect_dependency_from_py($py)
{
    $axioms = [];

    foreach (yield_from_py($py) as $dict) {
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

    return python;
}

function run($py)
{
    $module = py_to_module($py);
    $logs[] = "module = " . str_replace(".", "/", $module);
    $user = basename(dirname(dirname(__file__)));
    if (std\is_linux()) {
        $array = file_get_contents("http://localhost:8000/$user/run.py?module=$module", 0, stream_context_create([
            'http' => [
                'timeout' => 3000
            ]
        ]));
        $array = explode("\n", $array);
    } else {
        $array = file_get_contents("http://localhost/$user/run.py?module=$module", 0, stream_context_create([
            'http' => [
                'timeout' => 3000
            ]
        ]));
        $array = explode("\r\n", $array);
    }

    $data = null;
    foreach ($array as &$line) {
//         error_log("line = " . $line);
        if (preg_match('/^b([\'"])(.+)\1$/', $line, $m)) {
            $line = $m[2];
            if ($m[1] == "'"){
                $line = str_replace('"', '\\"', $line);
                $data = explode("\v", eval("return \"$line\";"));
                $index = count($data) - 1;
                $data[$index] = str_replace("\\'", "'", $data[$index]);
            }
            else{
                $data = explode("\v", eval("return \"$line\";"));
            }
            break;
        }
        else{
            $logs[] = $line;
        }
    }

    return [
        $logs,
        $data
    ];
}

function compile_python_file($py)
{
    $text = new std\Text($py);
    foreach ($text as $line) {
        error_log($line);
    }
    // $user = basename(dirname(dirname(__file__)));
    // if (std\is_linux()) {
    // $url = "https://www.axiom.top:5000/compile";
    // } else {
    // $url = "http://localhost:5000/compile";
    // }

    // $data = ["py"=> $py];
    return "error detected!";
}

function fetch_codes($module, $fetch_prove = false)
{
    $py = module_to_py($module);
    $py = file($py);
    $apply = [];

    $count = count($py);
    for ($i = 1; $i < $count; ++ $i) {
        $line = $py[$i];

        $apply[] = $line;

        if (preg_match('/^def prove\(/', $line, $matches)) {
            ++ $i;
            break;
        }
    }

    $apply = trim(implode("", $apply));

    if ($fetch_prove) {
        $prove = [];
        $line = $py[$i];
        if (preg_match('/^    from Lemma import \w+/', $line, $matches)) {
            ++ $i;
        }

        for (; $i < $count; ++ $i) {
            $line = $py[$i];
            if (preg_match('/^if +/', $line, $matches)) {
                break;
            }

            if (str_starts_with($line, '    ')) {
                $line = substr($line, 4);
            }

            $prove[] = $line;
        }

        $prove = rtrim(implode("", $prove));

        return [
            $apply,
            $prove
        ];
    }

    return $apply;
}

function axiom_directory()
{
    return dirname(dirname(__file__)) . "/Lemma/";
}

function select_axiom_by_state($user, $state, $limit=100)
{
    $result = get_rows("select axiom from axiom where user = '$user' and state = '$state' order by axiom limit $limit", MYSQLI_NUM);
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }
    return $array;
}

function select_axiom_by_regex($user, $regex, $binary = false, $limit=100)
{
    if ($binary)
        $binary = 'COLLATE utf8mb4_bin';
    else
        $binary = "";

    $sql = "select axiom from axiom where user = '$user' and axiom regexp '$regex' $binary limit $limit";
    error_log('sql = '.$sql);

    $result = get_rows($sql, MYSQLI_NUM);
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }
    return $array;
}

function select_axiom_by_like($user, $keyword, $binary = false, $limit=100)
{
    if ($binary) {
        $binary = " binary ";
    } else {
        $binary = " ";
    }

    $keyword = str_replace('_', '\_', $keyword);
    $sql = "select axiom from axiom where user = '$user' and axiom like$binary'%$keyword%' limit $limit";
    // echo $sql . "<br>";

    $result = get_rows($sql, MYSQLI_NUM);
    $array = [];
    foreach ($result as &$value) {
        $array[] = $value[0];
    }

    // echo "result = " . std\encode($result) . "<br>";
    // echo "array = " . std\encode($array) . "<br>";
    return $array;
}

function select_count($user, $state = null)
{
    $sql = "select count(*) from axiom where user = '$user'";
    if ($state) {
        $sql .= " and state = '$state'";
    }

    foreach (get_rows($sql, MYSQLI_NUM) as $count) {
        return $count[0];
    }
}

function select_axiom_by_state_not($user, $state)
{
    yield from get_rows("select axiom, state from axiom where user = '$user' and state != '$state'", MYSQLI_NUM);
}

function yield_from_mysql($user, $axiom)
{
    foreach (get_rows("select latex from axiom where user = '$user' and axiom = '$axiom'", MYSQLI_NUM) as [$latex]) {
        return explode("\n", $latex);
    }
}

function select_hierarchy($user, $axiom, $reverse = false)
{
    if ($reverse) {
        $callee = 'caller';
        $caller = 'callee';
    } else {
        $callee = 'callee';
        $caller = 'caller';
    }

    try {
        foreach (get_rows("select $callee from hierarchy where user = '$user' and $caller = '$axiom'", MYSQLI_NUM) as &$result) {
            yield $result[0];
        }
    } catch (Exception $e) {
        if (preg_match("/Table '(\w+).(\w+)' doesn't exist/", $e->getMessage(), $matches)) {
            assert(std\equals($matches[1], "axiom"));
            assert(std\equals($matches[2], "hierarchy"));
        } else {
            die($e->getMessage());
        }

        $sql = <<<EOT
        CREATE TABLE `hierarchy` (
          `user` varchar(32) NOT NULL,
          `caller` varchar(256) NOT NULL,
          `callee` varchar(256) NOT NULL,  
          `count` int default 0,
          PRIMARY KEY (`user`, `caller`, `callee`) 
        ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
        PARTITION BY KEY () PARTITIONS 8;
        EOT;

        execute($sql);

        foreach (retrieve_all_dependency() as [$caller, $counts]) {
            foreach ($counts as $callee => $count) {
                execute("insert into hierarchy values('$user', '$caller', '$callee', $count)");
            }
        }

        yield from select_hierarchy($user, $axiom, $reverse);
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

function suggest($user, $prefix, $phrase)
{
    $phrases = [];
    try {
        // $sql = "select phrase from suggest where user = '$user' and prefix = '$prefix' order by usage";
        $sql = "select phrase from suggest where user = '$user' and prefix = '$prefix'";
        if ($phrase) {
            $sql .= " and phrase like '%$phrase%'";
        }

        // error_log("in suggest: " . $sql);

        foreach (get_rows($sql, MYSQLI_NUM) as [$word]) {
            $phrases[] = $word;
        }
    } catch (Exception $e) {
        return [];
    }

    if ($phrase) {
        $dict = [];

        foreach ($phrases as &$word) {
            $dict[$word] = str_starts_with($word, $phrase);
        }

        arsort($dict);
        $phrases = array_keys($dict);
    }

    return $phrases;
}

function hint($prefix)
{
    $phrases = [];
    // error_log($prefix);
    try {
        // $sql = "select phrase from suggest where user = '$user' and prefix = '$prefix' order by usage";
        $sql = "select phrase from hint where prefix = binary'$prefix'";
        // error_log($sql);
        foreach (get_rows($sql, MYSQLI_NUM) as [$phrase]) {
            $phrases[] = $phrase;
        }
    } catch (Exception $e) {
        return [];
    }

    return $phrases;
}

function insert_into_suggest($user, $theorem)
{
    $phrases = explode('.', $theorem);
    $size = count($phrases);
    $phrases[] = 'apply';

    $prefix = '';

    $data = [];
    foreach (std\range(0, $size) as $i) {
        $prefix .= $phrases[$i] . ".";
        $data[] = [
            $user,
            $prefix,
            $phrases[$i + 1],
            1
        ];
    }

    $rows_affected = mysql\insertmany('suggest', $data);
}

function delete_from_suggest($user, $theorem, $__init__ = false, $regex = false)
{
    preg_match('/(.+\.)(\w+)$/', $theorem, $m);

    $prefix = $m[1];
    $phrase = $m[2];

    if ($regex) {
        // using regex engine;
        if ($__init__) {

            $sql = "delete from suggest where user = '$user' and prefix = '$theorem.' and phrase = 'apply'";

            $rows_affected = mysql\execute($sql);
            if ($rows_affected != 1)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        } else {
            $sql = "delete from suggest where user = '$user' and prefix = '$prefix.' and phrase = '$phrase'";

            $rows_affected = mysql\execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");

            $sql = "delete from suggest where user = '$user' and prefix regexp '^$theorem\..*'";

            $rows_affected = mysql\execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        }
    } else {

        if (! $__init__) {
            $sql = "delete from suggest where user = '$user' and prefix = '$prefix' and phrase = '$phrase'";

            $rows_affected = mysql\execute($sql);
            if (! $rows_affected)
                error_log("error found in $sql");
            else
                error_log("executing: $sql");
        }

        $sql = "delete from suggest where user = '$user' and prefix = '$theorem.' and phrase = 'apply'";

        $rows_affected = mysql\execute($sql);
        if (! $rows_affected)
            error_log("error found in $sql");
        else
            error_log("executing: $sql");
    }
}

function update_suggest($user, $package, $old, $new, $is_folder = false)
{
    if ($new == null) {
        $sql = "delete from suggest where user = '$user' and prefix = '$package.' and phrase = '$old'";
    } else if ($is_folder) {
        $package_regex = str_replace(".", "\\.", $package);
        $sql = "update suggest set prefix = regexp_replace(prefix, '^$package_regex\\.$old\\.(.+)', '$package.$new.$1') where user = '$user' and prefix like '$package.$old.%'";
    } else
        $sql = "update suggest set phrase = '$new' where user = '$user' and prefix = '$package' and phrase = '$old'";

    // error_log("sql = $sql");

    $rows_affected = mysql\execute($sql);
    if ($rows_affected < 1) {
        error_log("error found in $sql");
    }
}

function delete_from_axiom($user, $old, $regex = false)
{
    if ($regex) {
        // using regex engine;
        $sql = "delete from axiom where user = '$user' and axiom regexp '^$old'";
        $rows_affected = mysql\execute($sql);
    } else {
        $sql = "delete from axiom where user = '$user' and axiom = '$old'";
        $rows_affected = mysql\execute($sql);
    }

    if (! $rows_affected) {
        error_log("$sql");
    }
}

function update_axiom($user, $old, $new, $is_folder = false)
{
    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);
        $sql = "update axiom set axiom = regexp_replace(axiom, '^$old_regex\.(.+)', '$new.$1') where user = '$user' and axiom like '$old.%'";
    } else {
        $sql = "update axiom set axiom = '$new' where user = '$user' and axiom = '$old'";
    }

    // error_log("sql = $sql");
    $rows_affected = mysql\execute($sql);
    if ($rows_affected < 1) {
        error_log("error found in $sql");
    }
}

function replace_with_callee($user, $old, $new)
{
    $old_regex = str_replace('.', "\\.", $old);
    $old_regex_hierarchy = "$old_regex(?!\.)|$old_regex(?=\.apply\b)";
    foreach (get_rows("select caller from hierarchy where user = '$user' and callee = '$old'", MYSQLI_NUM) as [$caller]) {
        $pyFile = module_to_py($caller);
        $pyFile = new Text($pyFile);

        $pyFile->preg_replace($old_regex_hierarchy, $new);
    }

    $old_regex = "(?<=from Lemma\.)$old_regex(?= import \w+)";
    // php doesn't support variable-lenth looking-behind assertion
    // $old_regex = "(?<=^ *from Lemma\.)$old_regex(?= import \w+)";
    foreach (get_rows("select caller from `function` where user = '$user' and callee = '$old'", MYSQLI_NUM) as [$caller]) {
        $pyFile = module_to_py($caller);
        $pyFile = new Text($pyFile);

        $pyFile->preg_replace($old_regex, $new);
    }
}

function reaplce_axiom_in_hierarchy($user, $old, $new)
{
    error_log("sql = update hierarchy set caller = '$new' where user = '$user' and caller = '$old'");
    $rows_affected = mysql\execute("update hierarchy set caller = '$new' where user = '$user' and caller = '$old'");

    error_log("sql = update hierarchy set callee = '$new' where user = '$user' and callee = '$old'");
    $rows_affected = mysql\execute("update hierarchy set callee = '$new' where user = '$user' and callee = '$old'");

    error_log("sql = update `function` set caller = '$new' where user = '$user' and caller = '$old'");
    $rows_affected = mysql\execute("update `function` set caller = '$new' where user = '$user' and caller = '$old'");

    error_log("sql = update `function` set callee = '$new' where user = '$user' and callee = '$old'");
    $rows_affected = mysql\execute("update `function` set callee = '$new' where user = '$user' and callee = '$old'");
}

function update_hierarchy($user, $old, $new, $is_folder = false)
{
    if ($is_folder) {
        $old_regex = str_replace('.', "\\.", $old);

        $replaceDict = [];
        foreach (get_rows("select axiom from axiom where user = '$user' and axiom like '$old.%'", MYSQLI_NUM) as [$axiom]) {
            $oldAxiom = $axiom;
            $newAxiom = preg_replace("/^$old_regex\.(.+)/", "$new.$1", $oldAxiom);

            $replaceDict[$oldAxiom] = $newAxiom;
            error_log("replace $oldAxiom with $newAxiom");
        }

        foreach ($replaceDict as $old => $new) {
            replace_with_callee($user, $old, $new);
        }
        // these two for loop cannot be combined because results of replace_with_callee depend on reaplce_axiom_in_hierarchy
        foreach ($replaceDict as $old => $new) {
            reaplce_axiom_in_hierarchy($user, $old, $new);
        }
    } else {
        // update the python files that contains $old theorem!
        $sql = "select caller from hierarchy where user = '$user' and callee = '$old'";

        // error_log("sql = $sql");

        replace_with_callee($user, $old, $new);

        reaplce_axiom_in_hierarchy($user, $old, $new);
    }
}
?>
