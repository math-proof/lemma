<?php
require_once dirname(__file__) . '/../std.php';
require_once dirname(__file__) . '/../itertools.php';
require_once dirname(__file__) . '/newline_skipping_comment.php';

ini_set('xdebug.max_nesting_level', 1024);

$token2classname = [
    '+' => 'LeanAdd',
    '-' => 'LeanSub',
    '*' => 'LeanMul',
    '/' => 'LeanDiv',
    '÷' => 'LeanEDiv',  // euclidean division
    '//' => 'LeanFDiv', // floor division
    '%' => 'LeanModular',
    '×' => 'Lean_times',
    '@' => 'LeanMatMul',
    '•' => 'Lean_bullet',
    '⬝' => 'Lean_cdotp',
    '∘' => 'Lean_circ',
    '▸' => 'Lean_blacktriangleright',
    '⊙' => 'Lean_odot',
    '⊕' => 'Lean_oplus',
    '⊖' => 'Lean_ominus',
    '⊗' => 'Lean_otimes',
    '⊘' => 'Lean_oslash',
    '⊚' => 'Lean_circledcirc',
    '⊛' => 'Lean_circledast',
    '⊜' => 'Lean_circleeq',
    '⊝' => 'Lean_circleddash',
    '⊞' => 'Lean_boxplus',
    '⊟' => 'Lean_boxminus',
    '⊠' => 'Lean_boxtimes',
    '⊡' => 'Lean_dotsquare',
    '∈' => 'Lean_in',
    '∉' => 'Lean_notin',
    '|' => 'LeanBitOr',
    '&' => 'LeanBitAnd',
    '||' => 'LeanLogicOr',
    '|||' => 'LeanBitwiseOr',
    '&&' => 'LeanLogicAnd',
    '&&&' => 'LeanBitwiseAnd',
    '^' => 'LeanPow',
    '^^' => 'LeanLogicXor',
    '^^^' => 'LeanBitwiseXor',
    '<' => 'Lean_lt',
    '<<' => 'Lean_ll',
    '<<<' => 'Lean_lll',
    '<=' => 'Lean_le',
    '>' => 'Lean_gt',
    '>>' => 'Lean_gg',
    '>>>' => 'Lean_ggg',
    '>=' => 'Lean_ge',
    '∨' => 'Lean_lor',
    '∧' => 'Lean_land',
    '∪' => 'Lean_cup',
    '∩' => 'Lean_cap',
    "\\" => 'Lean_setminus',
    '|>.' => 'LeanMethodChaining',
    '<|' => 'Lean_lazy',
    '⊆' => 'Lean_subseteq',
    '⊂' => 'Lean_subset',
    '⊇' => 'Lean_supseteq',
    '⊃' => 'Lean_supset',
    '⊔' => 'Lean_sqcup',
    '⊓' => 'Lean_sqcap',
    '++' => 'LeanAppend',
    '→' => 'Lean_rightarrow',
    '↦' => 'Lean_mapsto',
    '↔' => 'Lean_leftrightarrow',
    '≠' => 'Lean_ne',
    '≡' => 'Lean_equiv',
    '≢' => 'LeanNotEquiv',
    '≍' => 'Lean_asymp',
    '≃' => 'Lean_simeq',
    '≈' => 'Lean_approx',
    '∣' => 'LeanDvd',
];

preg_match_all("/'(\w+)'/", file_get_contents(dirname(__FILE__) . '/../../static/codemirror/mode/lean/tactics.js'), $tactics);
[, $tactics] = $tactics;

require_once dirname(__FILE__) . '/lean/base.php';

require_once dirname(__FILE__) . '/lean/atomic.php';

trait LeanMultipleLine
{
    public function set_line($line)
    {
        $this->line = $line;
        foreach ($this->args as $arg) {
            $line = $arg->set_line($line) + 1;
        }
        return $line - 1;
    }
}

require_once dirname(__FILE__) . '/lean/abstract.php';

require_once dirname(__FILE__) . '/lean/paired.php';

require_once dirname(__FILE__) . '/lean/range.php';

require_once dirname(__FILE__) . '/lean/property.php';

require_once dirname(__FILE__) . '/lean/colon.php';

require_once dirname(__FILE__) . '/lean/assign.php';

trait LeanProp
{
    public function isProp($vars)
    {
        return true;
    }
}

require_once dirname(__FILE__) . '/lean/boolean.php';

require_once dirname(__FILE__) . '/lean/relational.php';

require_once dirname(__FILE__) . '/lean/membership.php';

require_once dirname(__FILE__) . '/lean/arithmetic.php';

require_once dirname(__FILE__) . '/lean/lazy.php';

require_once dirname(__FILE__) . '/lean/pipeline.php';

trait LeanGetElemBase
{
    public function push_right($func)
    {
        if ($func == 'LeanBracket')
            return $this;
        return parent::push_right($func);
    }

    public function insert_comma($caret)
    {
        $new = new LeanCaret($this->indent, $caret->level);
        $this->rhs = new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level);
        return $new;
    }
}

trait LeanGetElemBaseBinary 
{
    use LeanGetElemBase;
    public function sep()
    {
        return '';
    }

    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 18;
            default:
                return parent::__get($vname);
        }
    }
}


require_once dirname(__FILE__) . '/lean/indexing.php';

class Lean_is extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
                return 'is';
            case 'command':
                return '{\color{blue}\text{is}}';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function latexFormat()
    {
        return "{%s}\\ $this->command\\ {%s}";
    }

    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

class Lean_is_not extends LeanBinary
{
    public static $input_priority = 62;
    public function __get($vname)
    {
        switch ($vname) {
            case 'command':
                return '{\color{blue}\text{is not}}';
            case 'operator':
                return 'is not';
            default:
                return parent::__get($vname);
        }
    }

    public function is_indented()
    {
        return $this->parent instanceof LeanStatements;
    }

    public function isProp($vars)
    {
        return true;
    }
    public function sep()
    {
        return ' ';
    }
    public function strFormat()
    {
        return "%s $this->operator %s";
    }

}

require_once dirname(__FILE__) . '/lean/logic.php';

require_once dirname(__FILE__) . '/lean/set.php';

class LeanStatements extends LeanArgs
{
    use LeanMultipleLine;
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return LeanColon::$input_priority;
            default:
                return parent::__get($vname);
        }
    }
    public function echo()
    {
        $args = &$this->args;
        $count = count($args);
        $void_lines = 0;
        // skip trailing carets and comments
        while (($last = $args[$count - 1]) instanceof LeanCaret || $last instanceof LeanLineComment || $last instanceof LeanBlockComment) {
            --$count;
            ++$void_lines;
        }
        for ($index = 0; $index < count($args) - $void_lines - 1; ++$index) {
            $result = $args[$index]->echo();
            if (is_array($result)) {
                // zero-th element is the length to be replaced
                $length = array_shift($result);
                if ($index + 1 < count($args) - $void_lines && $args[$index + 1] instanceof LeanTactic && $args[$index + 1]->func == 'try' && 
                    count($result) == 2 && $result[0] === $args[$index] && $result[1] instanceof LeanTactic && $result[1]->func == 'echo') {
                    // next tactic is 'try', so the current echo tactic should also be 'try echo ..'
                    $result[1] = new LeanTactic('try', $result[1], $result[1]->indent, $result[1]->level);
                }
                foreach ($result as $echo)
                    $echo->parent = $this;
                $increment = std\index($result, $args[$index]);
                array_splice($args, $index, $length, $result);
                $index += $increment;
            }
        }
        $tactic = $args[$index];
        if ($tactic instanceof LeanTactic || $tactic instanceof Lean_match) {
            if (($with = $tactic->with)) {
                if ($with->sep() == "\n") {
                    foreach ($with->args as $case)
                        $case->echo();
                } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator) {
                    if (($block = $sequential_tactic_combinator->arg) instanceof LeanTacticBlock)
                        $block->echo();
                    else
                        $sequential_tactic_combinator->echo();
                }
            } elseif ($sequential_tactic_combinator = $tactic->sequential_tactic_combinator)
                $sequential_tactic_combinator->echo();
            else if ($block = $tactic->repeat_block())
                $block->echo();
        } elseif ($tactic instanceof LeanTacticBlock || $tactic instanceof LeanIte || $tactic instanceof LeanCalc)
            $tactic->echo();
    }

    public function insert_if($caret)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->replace($caret, new LeanIte([$caret], $caret->indent, $caret->level));
                return $caret;
            }
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_newline($caret, $newline_count, $indent, $next)
    {
        if ($this->indent > $indent)
            return parent::insert_newline($caret, $newline_count, $indent, $next);

        if ($this->indent < $indent) {
            $wrapped = $this->push_args_indented($indent, $newline_count);
            if ($wrapped)
                return $wrapped;
            // Match JS LeanStatements.insert_newline: if the last arg cannot be
            // wrapped, fall through and append carets at the deeper indent.
        }

        for ($i = 0; $i < $newline_count; ++$i) {
            $caret = new LeanCaret($indent, $caret->level);
            $this->push($caret);
        }
        return $caret;
    }

    public function is_indented()
    {
        return false;
    }
    public function isProp($vars)
    {
        $args = &$this->args;
        if (count($args) == 1)
            return $args[0]->isProp($vars);
    }
    public function jsonSerialize(): mixed
    {
        $args = parent::jsonSerialize();
        if (end($this->args) instanceof LeanCaret)
            array_pop($args);
        if (count($args) == 1)
            [$args] = $args;
        return $args;
    }

    public function latexFormat()
    {
        $stmt = implode(
            "\\\\\n",
            array_fill(0, count($this->args), "&{%s}&& ")
        );
        if ($this->parent instanceof LeanBy)
            return $stmt;
        return "\\begin{align*}\n$stmt\n\\end{align*}";
    }

    public function relocate_last_comment()
    {
        for ($index = count($this->args) - 1; $index >= 0; --$index) {
            $end = $this->args[$index];
            if ($end->is_outsider()) {
                $self = $this;
                while ($self) {
                    $parent = $self->parent;
                    if ($parent instanceof LeanStatements)
                        break;
                    $self = $parent;
                }
                if ($parent) {
                    $last = array_pop($this->args); // $end === $last
                    std\array_insert(
                        $parent->args,
                        std\index($parent->args, $self) + 1,
                        $last
                    );
                    $last->parent = $parent;
                    $last->indent = $parent->indent;
                    $parent->relocate_last_comment();
                    break;
                }
            } else {
                if ($end->is_comment()) {
                    $lemma = null;
                    for ($j = $index - 1; $j >= 0; --$j) {
                        $stmt = $this->args[$j];
                        if ($stmt instanceof Lean_lemma) {
                            $lemma = $stmt;
                            break;
                        }
                        if ($stmt->is_comment())
                            continue;
                        else
                            break;
                    }
                    if ($lemma) {
                        $assignment = $lemma->assignment;
                        if ($assignment instanceof LeanAssign) {
                            $proof = $assignment->rhs;
                            if ($proof instanceof LeanBy || $proof instanceof LeanCalc) {
                                $proof = $proof->arg;
                                if ($proof instanceof LeanStatements) {
                                    for ($i = $j + 1; $i <= $index; ++$i)
                                        $proof->push($this->args[$i]);
                                    array_splice($this->args, $j + 1, $index - $j);
                                    break;
                                }
                            } elseif ($proof instanceof LeanArgsNewLineSeparated) {
                                for ($i = $j + 1; $i <= $index; ++$i)
                                    $proof->push($this->args[$i]);
                                array_splice($this->args, $j + 1, $index - $j);
                                break;
                            }
                        }
                    }
                }
                $end->relocate_last_comment();
                break;
            }
        }
    }

    public function strFormat()
    {
        $format = implode("\n", array_fill(0, count($this->args), '%s'));
        if ($this->parent instanceof LeanBrace)
            $format = "\n$format\n" . str_repeat(' ', $this->parent->indent);
        return $format;
    }

    public function swap_echo_star(&$syntax, &$statements) {
        $args = &$this->args;
        for ($i = 0; $i < count($args); ++$i) {
            if (($echo = $args[$i]) instanceof LeanTactic && $echo->func == 'echo' && ($token = $echo->arg) instanceof LeanToken && $token->text == '*') {
                # convert `echo * simp at *` =>  `simp at * echo *`
                [$args[$i], $args[$i + 1]] = [$args[$i + 1], $args[$i]];
                ++$i;
            }
        }
        foreach ($this->args as $stmt)
            array_push($statements, ...$stmt->split($syntax));
    }

}


/**
 * Semantic pass over signature binders: braces `{m : Measure T}` plus brackets
 * `[IsProbabilityMeasure m]` identify probability-space domains T, and explicit
 * binders `(v : T → U)` on such a domain are random variables.
 * @param object[] $binderRoots
 * @return string[]
 */
function collect_random_var_names(array $binderRoots)
{
    $nodes = [];
    $gather = function ($n) use (&$gather, &$nodes) {
        if (!$n || !is_object($n)) return;
        $nodes[] = $n;
        if (isset($n->args) && is_array($n->args))
            foreach ($n->args as $k) $gather($k);
    };
    foreach ($binderRoots as $r) $gather($r);

    /** @var array<string,string> measure name -> domain text */
    $measures = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanBrace)) continue;
        $cols = [];
        $a = $n->arg;
        if ($a instanceof LeanColon) $cols[] = $a;
        elseif ($a instanceof LeanArgsSpaceSeparated)
            foreach ($a->args as $c) if ($c instanceof LeanColon) $cols[] = $c;
        foreach ($cols as $col) {
            $rhs = $col->rhs->peelGroup();
            if ($rhs->headIs('Measure') && $rhs instanceof LeanArgsSpaceSeparated
                && count($rhs->args) >= 2) {
                $dom = trim((string)$rhs->args[1]->peelGroup());
                if ($dom !== '') $measures[trim((string)$col->lhs)] = $dom;
            }
        }
    }

    /** @var array<string,bool> */
    $probDomains = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanBracket)) continue;
        $a = $n->arg->peelGroup();
        if ($a instanceof LeanArgsSpaceSeparated && count($a->args) >= 2
            && $a->headIs('IsProbabilityMeasure')) {
            $m = trim((string)$a->args[1]->peelGroup());
            if (isset($measures[$m])) $probDomains[$measures[$m]] = true;
        }
    }

    /** @var array<string,bool> */
    $rvs = [];
    foreach ($nodes as $n) {
        if (!($n instanceof LeanParenthesis)) continue;
        $col = $n->arg instanceof LeanColon ? $n->arg : null;
        if (!$col) continue;
        $ty = $col->rhs->peelGroup();
        if (!($ty instanceof Lean_rightarrow)) continue;
        $dom = trim((string)$ty->lhs->peelGroup());
        if (!isset($probDomains[$dom])) continue;
        $addNames = function ($x) use (&$addNames, &$rvs) {
            $y = $x->peelGroup();
            if ($y instanceof LeanToken) $rvs[$y->text] = true;
            elseif ($y instanceof LeanArgsSpaceSeparated)
                foreach ($y->args as $z) $addNames($z);
        };
        $addNames($col->lhs);
    }
    return array_keys($rvs);
}

/** Mark a statement sequence; top-level `let q := …` hides `q` thereafter. */
function mark_random_var_sequence(array $stmts, array $rvNames)
{
    $letBound = [];
    foreach ($stmts as $st)
        $st->markRandomVarNames($rvNames, $letBound);
}


class LeanModule extends LeanStatements
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'root':
                return $this;
            case 'stack_priority':
                return -3;
            default:
                return parent::__get($vname);
        }
    }

    public function array_push(&$vars, $lhs, $rhs)
    {
        if ($lhs instanceof LeanToken) {
            $args = [$lhs, $rhs];
            while (($end = end($args)) instanceof Lean_rightarrow)
                array_splice($args, count($args) - 1, 2, [$end->lhs, $end->rhs]);
            $vars[] = $args;
        } elseif ($lhs instanceof LeanArgsSpaceSeparated) {
            foreach ($lhs->args as $lhs)
                $this->array_push($vars, $lhs, $rhs);
        }
    }
    public function create_property($module) {
        return array_reduce(
            explode('.', $module),
            function ($carry, $token) {
                $token = new LeanToken($token, 0, 0);
                return $carry ? new LeanProperty($carry, $token, 0, 0) : $token;
            },
        );
    }
    public function decode(&$json, &$latex)
    {
        [[$line, $latexFormat]] = std\entries($json);
        if (isset($latex[$line])) {
            if (!is_array($latex[$line]))
                $latex[$line] = [$latex[$line]];
            $latex[$line][] = $latexFormat;
        } else
            $latex[$line] = $latexFormat;
    }

    public function echo()
    {
        $args = &$this->args;
        $this->import('sympy.printing.echo');
        for ($index = 0; $index < count($args); ++$index)
            $args[$index]->echo();
    }
    public function echo2vue($leanFile)
    {
        $this->relocate_last_comment();
        $this->echo();
        $leanEchoFile = preg_replace('/\.lean$/', '.echo.lean', $leanFile);
        if (!file_exists($leanEchoFile)) {
            error_log("create new lean file = $leanEchoFile");
            std\createNewFile($leanEchoFile);
        }
        // create a block to write the code
        {
            $file = new std\Text($leanEchoFile);
            $codeStr = "$this";
            $file->writelines([$codeStr]);
        }

        chdir(dirname(dirname(dirname(__FILE__))));
        $imports = array_filter(
            $this->args,
            fn($import) =>
            $import instanceof Lean_import &&
                str_starts_with($package = "$import->arg", 'Lemma.') &&
                (
                    !file_exists($olean = ".lake/build/lib/lean/" . ($module = str_replace('.', '/', $package)) . ".olean") || 
                    filemtime($olean) < filemtime($module. ".lean")
                )
        );
        $lakePath = get_lake_path();
        if ($imports) {
            $imports = implode(' ', array_map(fn($import) => "$import->arg", $imports));
            $cmd = "$lakePath build $imports";
            // $cmd = $lakePath . " setup-file \"$leanEchoFile\"";
            error_log("executing cmd = $cmd");
            if (std\is_linux())
                shell_exec($cmd);
            else
                std\exec($cmd, $_, get_lean_env());
        }
        // 10000 heartbeats approximates 1 second
        $cmd = $lakePath . ' env lean -D"linter.unusedTactic=false" -D"linter.dupNamespace=false" -D"diagnostics.threshold=1000" -D"maxHeartbeats=4000000" '. std\escapeshellarg($leanEchoFile);
        if (std\is_linux())
            exec($cmd, $output_array);
        else
            std\exec($cmd, $output_array, get_lean_env());
        $latex = [];
        $error = [];
        $this->set_line(1);
        $end = end($this->args);
        if ($end->line != substr_count($codeStr, "\n") + 1) {
            $error[] = [
                'code' => '',
                'line' => $end->line,
                'type' => 'error',
                'info' => 'the line count of *.echo.lean file is not correct'
            ];
        }
        foreach ($output_array as $jsonline) {
            $json = std\decode($jsonline);
            if ($json)
                $this->decode($json, $latex);
            elseif (preg_match('#([/\w]+)\.lean:(\d+):(\d+): (\w+): (.+)#', $jsonline, $matches)) {
                $line = intval($matches[2]);
                $col = intval($matches[3]);
                if (!isset($echo_codes))
                    $echo_codes = file($leanEchoFile);
                $code = $echo_codes[$line - 1];
                $type = $matches[4];
                $info = $matches[5];
                $error[] = [
                    'code' => $code,
                    'line' => $line, // later I will adjust this value.
                    'col' => $col - 2,
                    'type' => $type,
                    'info' => $info
                ];
            } else
                $error[count($error) - 1]['info'] .= "\n" . $jsonline;
        }

        foreach ($this->traverse() as $node) {
            if ($node instanceof LeanTactic && $node->func == 'echo')
                if (is_int($node->line)) {
                    if (!array_key_exists($node->line, $latex))
                        $latex[$node->line] = null;
                    $node->line = $latex[$node->line];
                } else {
                    error_log("unexpected node = $node");
                }
        }

        $keys = array_keys($latex);
        $indicesToDelete = [];
        foreach (std\range(count($error)) as $i) {
            $err = &$error[$i];
            $line = &$err['line'];
            $code = &$err['code'];
            if (preg_match("/^ +echo /", $code)) {
                if ($err['type'] == 'error' && $err['info'] == "No goals to be solved")
                    $code = $echo_codes[$line];
                else {
                    $indicesToDelete[] = $i;
                    continue;
                }
            }
            $line -= count(array_filter($keys, fn($key) => $key < $line)) + 1;
        }
        if ($indicesToDelete) {
            foreach (array_reverse($indicesToDelete) as $i)
                array_splice($error, $i, 1);
        }

        array_shift($this->args);
        $codes = $this->render2vue(true);
        array_push($codes['meta']['error'], ...$error);
        return $codes;
    }

    public function import($module)
    {
        $this->unshift(new Lean_import($this->create_property($module), 0, 0));
    }

    public function insert($caret, $func, $type)
    {
        if (end($this->args) === $caret) {
            if ($caret instanceof LeanCaret) {
                $this->push(new $func($caret, $this->indent, $caret->level));
                return $caret;
            }
        }
        return $caret;
    }

    public function parse_vars($implicit)
    {
        $vars = [];
        foreach ($implicit as $brace) {
            if ($brace instanceof LeanBrace) {
                $colon = $brace->arg;
                if ($colon instanceof LeanColon)
                    $this->array_push($vars, ...$colon->args);
            }
        }
        $kwargs = [];
        foreach ($vars as $var) {
            std\setitem(
                $kwargs,
                ...array_map(fn($arg) => "$arg", $var)
            );
        }
        return $kwargs;
    }

    public function parse_vars_default($default)
    {
        $vars = [];
        foreach ($default as $parenthesis) {
            if ($parenthesis instanceof LeanParenthesis) {
                $colon = $parenthesis->arg;
                if ($colon instanceof LeanColon)
                    $this->array_push($vars, ...$colon->args);
            }
        }
        return $vars;
    }

    public function render2vue($echo, &$modify = null, &$syntax = null)
    {
        if (!$echo)
            $this->relocate_last_comment();
        $import = [];
        $open = [];
        $set_option = [];
        $preamble = [];
        $lemma = [];
        $date = [];
        $error = [];
        $comment = null;
        foreach ($this->args as $stmt) {
            if ($stmt instanceof Lean_import)
                $import[] = "$stmt->arg";
            elseif ($stmt instanceof Lean_lemma) {
                if ($stmt->assignment instanceof LeanAssign) {
                    $accessibility = $stmt->accessibility;
                    $declspec = $stmt->assignment->lhs;
                    if ($declspec instanceof LeanColon) {
                        if ($attribute = $stmt->attribute) {
                            $attribute = $attribute->arg;
                            if ($attribute instanceof LeanBracket) {
                                $attribute = $attribute->arg;
                                if ($attribute instanceof LeanArgsCommaSeparated)
                                    $attribute = array_map(fn($arg) => "$arg", $attribute->args);
                                elseif ($attribute instanceof LeanToken)
                                    $attribute = ["$attribute"];
                            }
                        }
                        $imply = $declspec->rhs->args;
                        if ($imply[0] instanceof LeanLineComment && $imply[0]->text == 'imply')
                            array_shift($imply);

                        // semantic pass: random variables are explicit binders
                        // on a probability-space domain; mark their free
                        // occurrences in the signature and imply statements
                        $rvNames = collect_random_var_names([$declspec->lhs]);
                        if ($rvNames) {
                            $declspec->lhs->markRandomVarNames($rvNames);
                            mark_random_var_sequence($imply, $rvNames);
                        }

                        $proof = $stmt->assignment->rhs;
                        $by = $proof instanceof LeanBy ? 'by' : ($proof instanceof LeanCalc ? 'calc' : '');
                        $implyLean = preg_replace("/^  /m", "", implode("\n", array_map(fn($stmt) => "$stmt", $imply)));

                        if (count($imply) > 1 && ($imply[0] instanceof Lean_let)) {
                            $implyLatex = implode(
                                "\\\\\n",
                                array_map(
                                    function ($stmt) use (&$syntax) {
                                        return "&" . $stmt->toLatex($syntax) . "&& ";
                                    },
                                    $imply
                                )
                            );
                            $implyLatex = "\\begin{align*}\n$implyLatex\n\\end{align*}";
                        } else
                            $implyLatex = implode(
                                "\n",
                                array_map(
                                    function ($stmt) use (&$syntax) {
                                        return $stmt->toLatex($syntax);
                                    },
                                    $imply
                                )
                            );
                        $assignment = ' :=' . ($by ? " $by" : '');
                        $implyLatex .= "\\tag*{{$assignment}}";

                        $implyLean .= $assignment;
                        $imply = ['lean' => $implyLean, 'latex' => $implyLatex];

                        $declspec = $declspec->lhs;
                        if ($declspec instanceof LeanToken || $declspec instanceof LeanProperty) {
                            $name = $declspec;
                            $declspec = [];
                        } else {
                            [$name, $declspec] = $declspec->args;
                            $declspec = $declspec->args;
                        }

                        $instImplicit = [];
                        $implicit = [];
                        $explicit = [];
                        $given = null;
                        $default = [];
                        $decidables = [];
                        $flattened = [];
                        foreach ($declspec as $s) {
                            if ($s instanceof LeanArgsSpaceSeparated) {
                                $hasParen = false;
                                foreach ($s->args as $a)
                                    if ($a instanceof LeanParenthesis) {
                                        $hasParen = true;
                                        break;
                                    }
                                if ($hasParen) {
                                    foreach ($s->args as $a)
                                        $flattened[] = $a;
                                    continue;
                                }
                            }
                            $flattened[] = $s;
                        }
                        $declspec = $flattened;
                        foreach ($declspec as $i => &$stmt) {
                            if ($stmt instanceof LeanBracket) {
                                $instImplicit[] = "$stmt";
                                if ($stmt->arg instanceof LeanArgsSpaceSeparated) {
                                    if (count($stmt->arg->args) == 2) {
                                        [$lhs, $rhs] = $stmt->arg->args;
                                        if ($lhs instanceof LeanToken && $lhs->text == 'Decidable' && $rhs instanceof LeanToken)
                                            $decidables[] = "$rhs";
                                    }
                                }
                            } elseif ($stmt instanceof LeanBrace) {
                                $stmt->toLatex($syntax);
                                $implicit[] = $stmt;
                            } elseif ($stmt instanceof LeanArgsSpaceSeparated) {
                                if ($stmt->args[0] instanceof LeanBracket)
                                    $instImplicit[] = "$stmt";
                                elseif ($stmt->args[0] instanceof LeanBrace)
                                    $implicit[] = $stmt;
                                else
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "lemma $name is not well-defined",
                                        'type' => 'linter'
                                    ];
                            } elseif ($stmt instanceof LeanLineComment) {
                                if ($stmt->text == 'given') {
                                    $given = $i + 1;
                                    break;
                                }
                                if ($implicit)
                                    $implicit[] = "$stmt";
                                else
                                    $instImplicit[] = "$stmt";
                            } elseif ($stmt instanceof LeanParenthesis) {
                                // the given comment is missing, try to add one
                                if ($stmt->arg instanceof LeanColon) {
                                    std\array_insert($stmt->parent->args, $i, new LeanLineComment('given', $stmt->indent, $stmt->parent));
                                    std\array_insert($declspec, $i, new LeanLineComment('given', $stmt->indent, $stmt->parent));
                                    $modify = true;
                                    ++$i;
                                }
                                $given = $i;
                                break;
                            }
                        }

                        if ($given !== null) {
                            $given = array_slice($declspec, $given);
                            $flattened = [];
                            foreach ($given as $s) {
                                if ($s instanceof LeanArgsSpaceSeparated) {
                                    foreach ($s->args as $a)
                                        $flattened[] = $a;
                                } else
                                    $flattened[] = $s;
                            }
                            $given = $flattened;
                            $latex = [];
                            $givenStart = null;
                            $givenStop = null;
                            $vars = null;
                            foreach (std\enumerate($given) as [$i, $stmt]) {
                                if ($stmt instanceof LeanParenthesis) {
                                    $colon = $stmt->arg;
                                    if ($colon instanceof LeanColon) {
                                        $prop = $colon->rhs;
                                        if (!isset($vars)) {
                                            $vars = $this->parse_vars($implicit);
                                            foreach ($decidables as $p)
                                                $vars[$p] = "Prop";
                                        }
                                        if ($prop->isProp($vars)) {
                                            $latex[] = [$prop->toLatex($syntax), latex_tag("$colon->lhs")];
                                            if ($givenStart === null)
                                                $givenStart = $i;
                                        } elseif ($givenStart !== null) {
                                            $givenStop = $i;
                                            break;
                                        }
                                    } elseif ($colon instanceof LeanAssign) {
                                        $pivot = $i;
                                        break;
                                    }
                                } elseif ($stmt->is_comment())
                                    $latex[] = null;
                                elseif ($stmt instanceof LeanBrace) {
                                    $pivot = $i;
                                    $given[$pivot] = new LeanParenthesis($stmt->arg, $stmt->indent, $stmt->parent);
                                    $given[$pivot]->is_closed = true;
                                    break;
                                } elseif ($stmt instanceof LeanCaret) {
                                } else {
                                    $error[] = [
                                        'code' => "$stmt",
                                        'line' => 0,
                                        'info' => "given statement must be of LeanParenthesis Type",
                                        'type' => 'linter'
                                    ];
                                }
                            }
                            $given = array_map(fn($stmt) => preg_replace("/^  /m", "", "$stmt"), $given);
                            if ($givenStart !== null) {
                                if ($givenStop !== null) {
                                    $explicit = array_slice($given, 0, $givenStart);
                                    $default = array_slice($given, $givenStop);
                                    $default[count($default) - 1] .= ' :';
                                    $given = array_slice($given, $givenStart, $givenStop);
                                } else {
                                    $explicit = array_slice($given, 0, $givenStart);
                                    $given = array_slice($given, $givenStart);
                                    $latex[count($latex) - 1][1] .= ' :';
                                    $given[count($given) - 1] .= ' :';
                                }
                            } else {
                                $explicit = $given;
                                $explicit[count($explicit) - 1] .= ' :';
                                $given = null;
                            }

                            if ($given) {
                                if (count($given) > count($latex))
                                    $given = [...array_filter($given)];
                                $latex = array_map(fn($stmt) => $stmt ? "$stmt[0]\\tag*{\$$stmt[1]\$}" : null, $latex);
                                $given = array_map(
                                    function ($args) {
                                        $obj = ['lean' => $args[0]];
                                        if ($args[1])
                                            $obj['latex'] = $args[1];
                                        else
                                            $obj['insert'] = true;
                                        return $obj;
                                    },
                                    std\zipped($given, $latex)
                                );
                            }
                        }
                        $proof = $by ? [$by => self::merge_proof($proof->arg, $echo, $syntax)] : self::merge_proof($proof, $echo, $syntax);
                        $implicit = array_map(fn($stmt) => "$stmt", $implicit);
                        $lemma[] = [
                            'comment' => $comment,
                            'accessibility' => "$accessibility",
                            'attribute' => $attribute,
                            'name' => "$name",
                            'instImplicit' => preg_replace("/^  /m", "", implode("\n", $instImplicit)),
                            'implicit' => preg_replace("/^  /m", "", implode("\n", $implicit)),
                            'explicit' => implode("\n", $explicit),
                            'given' => $given,
                            'default' => implode("\n", $default),
                            'imply' => $imply,
                            'proof' => $proof
                        ];
                        $comment = null;
                    } else
                        $error[] = [
                            'code' => "$declspec",
                            'line' => 0,
                            'info' => "declspec of lemma must be of LeanColon Type",
                            'type' => 'linter'
                        ];
                } else
                    $error[] = [
                        'code' => "$stmt",
                        'line' => 0,
                        'info' => "lemma must be of LeanAssign Type",
                        'type' => 'linter'
                    ];
            } elseif ($stmt instanceof Lean_def)
                $preamble[] = "$stmt";
            elseif ($stmt instanceof Lean_open) {
                $stmt = $stmt->arg;
                if ($stmt instanceof LeanArgsSpaceSeparated) {
                    if (count($stmt->args) == 2 && $stmt->args[1] instanceof LeanParenthesis) {
                        $defs = $stmt->args[1]->arg;
                        $open[] = [
                            $stmt->args[0]->__toString() =>
                            $defs instanceof LeanArgsSpaceSeparated ?
                                array_map(fn($arg) => "$arg", $defs->args) :
                                ["$defs->arg"]
                        ];
                    } else
                        $open[] = array_map(fn($arg) => "$arg", $stmt->args);
                } else
                    $open[] = ["$stmt->text"];
            } elseif ($stmt instanceof Lean_set_option) {
                $stmt = $stmt->arg;
                if ($stmt instanceof LeanArgsSpaceSeparated)
                    $set_option[] = array_map(fn($arg) => "$arg", $stmt->args);
            } elseif ($stmt instanceof LeanLineComment) {
                if (preg_match('/^(created|updated) on (\d\d\d\d-\d\d-\d\d)$/', "$stmt->text", $matches))
                    $date[$matches[1]] = $matches[2];
                else
                    $comment = "$stmt->text";
            } elseif ($stmt instanceof LeanBlockComment)
                $comment = "$stmt->text";
        }

        return [
            'imports' => $import,
            'open' => $open,
            'set_option' => $set_option,
            'preamble' => $preamble,
            'lemma' => $lemma,
            'date' => $date,
            'meta' => ['error' => $error],
        ];
    }

    static function merge_proof($proof, $echo, &$syntax = null)
    {
        $proof = $proof->args;
        if ($proof[0] instanceof LeanLineComment && $proof[0]->text == 'proof')
            array_shift($proof);

        $proof = array_filter($proof, fn($stmt) => !($stmt instanceof LeanCaret));
        $code = [];
        $last = [];
        $statements = [];
        foreach ($proof as $s)
            array_push($statements, ...$s->split($syntax));

        if ($echo) {
            foreach ($statements as $stmt) {
                if ($echo = $stmt->getEcho()) {
                    $code[] = [$last, is_int($echo->line) ? null : $echo->line];
                    $last = [];
                } else
                    $last[] = $stmt;
            }
        } else {
            foreach ($statements as $stmt) {
                if ($stmt instanceof Lean_let || $stmt instanceof LeanTactic) {
                    $last[] = $stmt;
                    $code[] = [$last, null];
                    $last = [];
                } else
                    $last[] = $stmt;
            }
        }
        if ($last)
            $code[] = [$last, null];
        return array_map(
            fn($code) =>
            [
                'lean' => implode("\n", array_map(fn($stmt) => preg_replace("/^  /m", "", rtrim("$stmt", "\n")), $code[0])),
                'latex' => $code[1]
            ],
            $code
        );
    }

}

abstract class LeanCommand extends LeanUnary
{
    public function is_indented()
    {
        return false;
    }

    public function jsonSerialize(): mixed
    {
        return [
            $this->func => $this->arg->jsonSerialize(),
        ];
    }
    public function latexFormat()
    {
        return "$this->command %s";
    }
    public function strFormat()
    {
        return "$this->operator %s";
    }

}

class Lean_import extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'import';

            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_open extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'open';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_set_option extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                return 27;
            case 'operator':
            case 'command':
                return 'set_option';
            default:
                return parent::__get($vname);
        }
    }

    public function append($func, $type)
    {
        if (is_string($func)) {
            $new = new LeanCaret($this->indent, $this->sql->level);
            $this->sql = new $func($new);
            $this->sql->parent = $this;
            return $new;
        }

        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function echo()
    {
        $arg = &$this->arg;
        if ($arg instanceof LeanArgsSpaceSeparated) {
            $args = &$arg->args;
            if (count($args) == 2 && $args[0] instanceof LeanToken && $args[1] instanceof LeanToken) {
                $value = &$args[1]->text;
                if ($args[0]->text == 'maxHeartbeats')
                    $value = strval(intval($value) * 5);
            }
        }
    }
    public function push_attr($caret)
    {
        if ($caret === $this->arg) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->arg = new LeanProperty($this->arg, $new, $this->indent, $caret->level);
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

}

class Lean_namespace extends LeanCommand
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'operator':
            case 'command':
                return 'namespace';
            default:
                return parent::__get($vname);
        }
    }
}


class LeanBar extends LeanUnary
{
    public function __get($vname)
    {
        switch ($vname) {
            case 'stack_priority':
                //must be >= LeanAssign::$input_priority
                return LeanAssign::$input_priority;
            case 'operator':
            case 'command':
                return '|';
            default:
                return parent::__get($vname);
        }
    }

    public function echo()
    {
        $this->arg->echo();
    }

    public function insert_comma($caret)
    {
        if ($caret === end($this->args)) {
            $new = new LeanCaret($this->indent, $caret->level);
            $this->replace($caret, new LeanArgsCommaSeparated([$caret, $new], $this->indent, $caret->level));
            return $new;
        }
        throw new Exception(__METHOD__ . " is unexpected for " . get_class($this));
    }

    public function insert_tactic($caret, $token)
    {
        return $this->insert_word($caret, $token);
    }
    public function is_indented()
    {
        return true;
    }

    public function latexFormat()
    {
        return "$this->command %s";
    }

    public function split(&$syntax = null)
    {
        $arrow = $this->arg;
        if ($arrow instanceof LeanRightarrow) {
            $self = clone $this;
            $statements[] = $self;
            $arrow = $self->arg;
            $stmts = $arrow->rhs;
            if ($stmts instanceof LeanStatements) {
                $arrow->rhs = new LeanCaret($arrow->indent, $arrow->level);
                $stmts->swap_echo_star($syntax, $statements);
            }
            return $statements;
        }
        return [$this];
    }

    public function strFormat()
    {
        return "$this->operator %s";
    }

}

require_once dirname(__FILE__) . '/lean/arrows.php';

require_once dirname(__FILE__) . '/lean/negation.php';

require_once dirname(__FILE__) . '/lean/match.php';

require_once dirname(__FILE__) . '/lean/ite.php';

require_once dirname(__FILE__) . '/lean/args.php';

require_once dirname(__FILE__) . '/lean/tactic.php';

require_once dirname(__FILE__) . '/lean/decl.php';

require_once dirname(__FILE__) . '/lean/fun.php';

require_once dirname(__FILE__) . '/lean/bigops.php';

require_once dirname(__FILE__) . '/lean/quantifier.php';

function compile($code) {
    return LeanParser::$instance->build($code);
}

class LeanParser extends AbstractParser {
    static $instance = null;
    private $root;
    public $tokens;
    public $start_idx;

    public function __construct() {
    }

    public function __toString() {
        return (string)$this->root;
    }

    public function build($text) {
        $this->init();
        if (!str_ends_with($text, "\n"))
            $text .= "\n";
        $this->tokens = array_map(fn($args) => $args[0][0], std\matchAll('/\w+|\W/u', $text));
        $tokens = &$this->tokens;
        $length = count($tokens);
        $this->start_idx = 0;
        $i = &$this->start_idx;
        for ($i = 0; $i < $length; $i++) {
            $this->parse($tokens[$i], $this);
            if (!$this->caret)
                break;
        }
        return $this->root;
    }
    public function init() {
        $caret = new LeanCaret(0, 0);
        $this->caret = $caret;
        $this->root = new LeanModule([$caret], 0, 0);
    }

}

LeanParser::$instance = new LeanParser();

function escape_specials($token)
{
    return preg_replace_callback(
        '/^(\w+?)_(.+)/',
        function($m) {
            $head = $m[1];
            $tail = preg_replace("/[{}_]/", "\\\\$0", $m[2]);
            return strlen($m[1]) == 1 ? "{$head}_{{$tail}}": "$head\\_$tail";
        },
        $token
    );
}

function latex_tag($tag)
{
    return implode(
        '.',
        array_map(
            fn($tag) => escape_specials($tag),
            explode(".", $tag)
        )
    );
}

function get_lake_path() {
    return std\is_linux() ? "~/.elan/bin/lake": escapeshellcmd(getenv('USERPROFILE') . "\\.elan\\bin\\lake.exe");
}

function get_lean_env()
{
    // add to the file D:\wamp64\bin\apache\apache2.4.54.2\conf\extra\httpd-vhosts.conf
    // SetEnv USERPROFILE "C:\Users\admin" / "C:\Users\Administrator"
    // Configure Git environment variables to trust the directory
    $cwd = getcwd();
    $repository = scandir("$cwd/.lake/packages");
    $repository = array_slice($repository, 2); // Remove . and ..
    $env = [
        'GIT_CONFIG_COUNT' => count($repository),
        // Preserve other important environment variables
        'PATH' => getenv('PATH'),
        // tricks for system profile user on Windows
        // Copy-Item -Path "$HOME\.elan" -Destination "C:\Windows\System32\config\systemprofile\.elan" -Recurse -Force
        'SystemRoot' => getenv('SystemRoot'),
        'HOME' => getenv('HOME')
    ];
    $cwd = str_replace("\\", "/", $cwd);
    foreach ($repository as $index => $directory) {
        $env["GIT_CONFIG_KEY_$index"] = "safe.directory";
        $env["GIT_CONFIG_VALUE_$index"] = "$cwd/.lake/packages/$directory";
    }
    return $env;
}

function transformExpr(string $s0, string $s): string {
    if ($s0 === '_') {
        return $s;
    }
    
    // Check if matches pattern: ^[A-Z][a-zA-Z0-9'!₀-₉]+?S
    if (preg_match('/^[A-Z]$/', $s0)) {
        if (preg_match('/^[a-zA-Z0-9\'!₀-₉]+?S/', $s)) {
            return $s0 . $s;
        }
    }
    
    return '_' . $s0 . $s;
}

function transformPrefix(string $s): string {
    // Pattern 1: EqX, NeX, OrX
    if (preg_match('/^(Eq|Ne|Or)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s2 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s2, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 2: SEqX, HEqX, IffX, AndX
    if (preg_match('/^([SH]Eq)(.)(.*)$/', $s, $matches) || preg_match('/^(Iff|And)(.)(.*)$/', $s, $matches)) {
        $prefix = $matches[1];
        $s3 = $matches[2];
        $rest = $matches[3];
        $transformed = transformExpr($s3, $rest);
        return $prefix . $transformed;
    }
    
    // Pattern 3: LtX, LeX, GtX, GeX (with additional characters)
    if (preg_match('/^(L|G)(t|e)(.)(.*)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $s2 = $matches[3];
        $rest = $matches[4];
        
        // Flip the first character
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        $transformed = transformExpr($s2, $rest);
        return $newS0 . $s1 . $transformed;
    }
    
    // Pattern 3 (short version): Lt, Le, Gt, Ge (no additional characters)
    if (preg_match('/^(L|G)(t|e)$/', $s, $matches)) {
        $s0 = $matches[1];
        $s1 = $matches[2];
        $newS0 = ($s0 === 'L') ? 'G' : 'L';
        return $newS0 . $s1;
    }
    
    // If no patterns matched, return original string
    return $s;
}

function is_symm_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne"], true);
}

function is_infix_operator(string $op): bool
{
    return in_array($op, ["eq", "is", "as", "ne", "lt", "le", "gt", "ge", "in", "ou", "et"], true);
}

function parseInfixSegments(array $list, $section = null): array
{
    if (!$section) {
        $section = $list[0];
        $list = array_slice($list, 1);
    }
    $n = count($list);
    if ($n === 0)
        return [];
    if ($n === 1)
        return [$list];

    $result = [];
    $i = 0;
    while ($i < $n) {
        if ($i + 2 >= $n) {
            // push remaining elements as singletons
            for (; $i < $n; $i++) {
                $result[] = [$list[$i]];
            }
            break;
        }
        $x  = $list[$i];
        $op = $list[$i + 1];
        $y  = $list[$i + 2];
        if (is_infix_operator($op)) {
            $result[] = [$x, $op, $y];
            $i += 3;
        } else {
            $result[] = [$x];
            ++$i;
        }
    }
    return [$section, $result];
}

function Not($token) {
    if (is_string($token)) {
        if (str_starts_with($token, 'Not'))
            return substr($token, 3);
        elseif (str_starts_with($token, 'Eq'))
            return "Ne" . substr($token, 2);
        elseif (str_starts_with($token, 'Ne'))
            return "Eq" . substr($token, 2);
        else
            return "Not" . $token;
    }
    if (count($token) == 1)
        return [Not($token[0])];
    return $token;
}
