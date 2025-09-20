<!DOCTYPE html>
<meta charset="UTF-8">
<link rel="stylesheet" href="static/css/style.css">
<?php
// ^ *error_log
require_once 'php/utility.php';
require_once 'php/mysql.php';


$key = array_keys($_GET);
switch (count($key)) {
    case 0:
        $key = array_keys($_POST);
        switch (count($key)) {
            case 0:
                require_once 'php/summary.php';
                exit();
            default:
                if (array_key_exists('module', $_POST)) {
                    $module = $_POST['module'];
                    break;
                } else {
                    require_once 'php/search.php';
                    exit();
                }
        }
        break;
    case 1:
        [$key] = $key;
        switch ($key) {
            case "symbol":
                require_once 'php/symbol.php';
                exit();
            case "module":
                $module = $_GET['module'];
                break;
            case "axiom":
                $sympy = $_GET['axiom'];
                require_once 'php/sympy.php';
                exit();
            case "sympy":
                $sympy = $_GET['sympy'];
                require_once 'php/sympy.php';
                exit();
            case "callee":
                require_once 'php/hierarchy.php';
                exit();
            case "caller":
                require_once 'php/hierarchy.php';
                exit();
            case "new":
                require_once 'php/new.php';
                exit();
            case "state":
            case "keyword":
            case "latex":
                require_once 'php/search.php';
                exit();
        }
        break;
    case 2:
        $module = $_GET['module'];
        break;
    default:
        break;
}

function piece_together(&$input)
{
    $code = implode("\n", $input);
    $input = null;
    return $code;
}

//(?:\( *Eq\.\w+ *(?:, (*Eq\.\w+|\*Eq\[-\d+:\]))+ *\)
//(?:, *(?:\( *Eq\.\w+ *(?:, *Eq\.\w+)+ *\)|Eq\.\w+|\[\*Eq\[-\d+:\]\]))
function is_latex_print($latex, &$res)
{
    // Eq.first, Eq.result = ...
    // Eq.first, result = ...
    // Eq.first, *result = ...
    // Eq.given, Eq.where, Eq.imply = ...
    // Eq.given, (Eq.where, Eq.where1), Eq.imply = ...
    // Eq[-2:], (Eq.where, *Eq[-2:]), Eq[-2:] = ...
    // (*Eq[-4:], Eq.eq_s, Eq.eq_x, Eq.eq_G), Eq[-1] = ...
    // *Eq[-5:], Eq.hypothesis = ...
    while (preg_match('/^(Eq\.\w+|\((Eq\.\w+|\*Eq\[-\d+:\]) *(, *Eq\.\w+)+ *\)|Eq\[-(\d+:|1)\]|\*Eq\[-\d+:\]|\*\w+|\w+)/u', $latex, $match)) {
        $res[] = $match[0];
        $latex = std\slice($latex, strlen($match[0]));
        if (preg_match('/^ *= */', $latex, $matchEqual))
            return true;

        if (!preg_match('/^ *, */', $latex, $matchComma))
            return false;

        $latex = std\slice($latex, strlen($matchComma[0]));
    }

    return false;
}

$module = str_replace('/', '.', $module);
$title = str_replace('.', '/', $module);

$path_info = substr(__FILE__, 0, -9) . "Lemma/" . $title;

$indexOfYield = -1;
if (! str_ends_with($path_info, '/')) {

    $py = $path_info . ".py";

    if (! file_exists($py)) {
        $__init__ = substr($py, 0, -3) . "/__init__.py";
        if (file_exists($__init__)) {
            $py = $__init__;
            $title .= "/";
        } elseif (file_exists($pyOf = str_replace('/of/', '/given/', $py)) || file_exists(substr($pyOf, 0, -3) . "/__init__.py")) {
            $user = get_user();
            $module = str_replace('.of.', '.given.', $module);
            header("location:?module=$module");
            exit;
        }
    }

    $logs = [];
    $ret = 1;

    if (array_key_exists('prove', $_POST)) {
        $applyCodes = array_key_exists('apply', $_POST) ? $_POST['apply'] : null;

        $proveCodes = $_POST['prove'];

        $proveCodes = insert_section($proveCodes);
        if (is_array($proveCodes))
            modify_codes($py, $proveCodes, $applyCodes);
        else {
            error_log("create new py file = $py");

            $base_py = dirname($py) . ".py";
            if (file_exists($base_py)) {
                $base_init = dirname($py) . "/__init__.py";
                error_log("change $base_py into $base_init");
                std\createDirectory(dirname($py));

                rename($base_py, $base_init);
            }

            $imports = [];
            if (file_exists($py)) {
                if (! str_ends_with($py, "/__init__.py"))
                    die("$py already exists!");
                else {
                    $file = new std\Text($py);
                    if ($file->search('from util import \S')) {
                        die("$py already exists!");
                    }
                    $imports = $file->preg_match('from \. import');
                }
            }

            $file = new std\Text($py);
            $code = "from util import *\n\n\n";

            $code .= $applyCodes . "\n";
            foreach (explode("\n", $proveCodes) as $line) {
                $code .= "    $line\n";
            }

            $code .= "\n\nif __name__ == '__main__':\n";
            $code .= "    run()\n";

            $timestamp = date('Y-m-d', time());
            $code .= "# created on $timestamp\n";

            if (count($imports)) {
                $code .= "\n\n";
                $code .= implode("\n", $imports);
            }

            $file->write($code);

            insert_into_init(py_to_module($py));
        }

        [$logs, $data] = run($py);
        if (count($data) == 6)
            array_pop($data);
    } else
        $data = null;

    $lengths = [];

    $counterOfLengths = 0;

    $inputs = [];
    $input = [];

    $numOfRequisites = preg_match('/([\w.]+)\.(of|given)\./', $module, $m) ? count(explode(".", $m[1])) - 1 : 0;

    foreach (yield_from_py($py) as $dict) {
        if (! array_key_exists('statement', $dict))
            continue;

        $statement = $dict['statement'];

        if (array_key_exists('module', $dict)) {
            $module = $dict['module'];
            $indexOfYield = $counterOfLengths;
            $input[] = $statement;
        } elseif (array_key_exists('a', $dict)) {
            if (! $input && $inputs && end($inputs)[-1] == '\\') {
                $length = count($inputs);
                $inputs[$length - 1] .= "\n$statement";
            } else
                $input[] = $statement;
        } else {
            unset($dict['statement']);
            if (array_key_exists('comment', $dict)) {
                unset($dict['comment']);

                if (array_key_exists('unused', $dict));
                elseif ($inputs && has_unterminated_parantheses(end($inputs))) {
                    $inputs[count($inputs) - 1] .= "\n$statement";
                    continue;
                } else {
                    if ($dict) {
                        foreach ($dict as $key => $value) {
                            switch ($key) {
                                case "created":
                                    $createdTime = $value;
                                    break;
                                case "updated":
                                    $updatedTime = $value;
                                    break;
                            }
                        }
                    }
                }

                $input[] = $statement;
                continue;
            }

            if (array_key_exists('unused', $dict)) {
                $input[] = $statement;
                continue;
            }

            $text = $statement;
            if (!$input && (str_starts_with($statement, '    ') || $statement == ")"))
                // starting with more than 4 spaces indicates this line is a continuation of the previous line of code!
                $inputs[count($inputs) - 1] .= "\n$text";
            else
                $input[] = $text;
        }

        if (preg_match('/^Eq *(<<|\[ *(- *\d+ *)?(: *)?\] *=) */', $statement, $matches)) {
            $inputs[] = piece_together($input);

            ++$counterOfLengths;
            $lengths[] = 1;
        } elseif (is_latex_print($statement, $matches)) {
            // https://www.php.net/manual/en/function.preg-match-all.php
            $regexp = '/Eq\.\w+|Eq\[-(\d+:|1)\]/u';
            if (array_key_exists('module', $dict)) {
                $count = count($matches);
                switch ($count) {
                    case 1:
                        $lengthOfGiven = $lengthOfWhere = 0;
                        break;
                    case 2:
                        if ($numOfRequisites) {
                            preg_match_all($regexp, $matches[0], $matchGiven, PREG_SET_ORDER);
                            $lengthOfGiven = count($matchGiven);
                            $lengthOfWhere = 0;
                        } else {
                            preg_match_all($regexp, $matches[0], $matchWhere, PREG_SET_ORDER);
                            $lengthOfWhere = count($matchWhere);
                            $lengthOfGiven = 0;
                        }
                        break;
                    case 3:
                        preg_match_all($regexp, $matches[0], $matchGiven, PREG_SET_ORDER);
                        $lengthOfGiven = count($matchGiven);

                        preg_match_all($regexp, $matches[1], $matchWhere, PREG_SET_ORDER);
                        $lengthOfWhere = count($matchWhere);
                        break;
                }

                preg_match_all($regexp, $matches[$count - 1], $matchImply, PREG_SET_ORDER);
                $lengthOfImply = count($matchImply);
                $lengths[] = $lengthOfGiven + $lengthOfWhere + $lengthOfImply;
            } else {
                $assgnment_count = 0;
                foreach ($matches as $text) {
                    preg_match_all($regexp, $text, $matches, PREG_SET_ORDER);
                    $assgnment_count += count($matches);
                }

                if (!$assgnment_count)
                    continue;

                $lengths[] = $assgnment_count;
            }

            $inputs[] = piece_together($input);
            ++$counterOfLengths;
        }
    }
}

require_once $indexOfYield < 0 ? 'php/package.php' : 'php/theorem.php';
?>