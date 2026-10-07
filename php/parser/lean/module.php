<?php
/**
 * Source file (`LeanModule`).
 *
 * Loaded by lean.php after `statements.php`. Mirrors
 * static/js/parser/lean/module.js. `echo2vue` chdirs four directories up,
 * because this file lives in `lean/`. Later classes (`Lean_import`,
 * `LeanTactic`, …) are resolved when methods run.
 * Not a standalone entry point.
 */

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
        // `X : Ω → S`, or an indexed family `s : ℕ → Ω → S` (the last domain is Ω; mirrors module.js)
        $last = $ty;
        while ($last->rhs->peelGroup() instanceof Lean_rightarrow) $last = $last->rhs->peelGroup();
        $dom = trim((string)$ty->lhs->peelGroup());
        if (!isset($probDomains[$dom]) && !isset($probDomains[trim((string)$last->lhs->peelGroup())])) continue;
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

        chdir(dirname(dirname(dirname(dirname(__FILE__)))));
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
                            // one-line signature `name [A] {x : T} (h : P) :` puts the binders themselves in args
                            // (a multi-line one wraps them in one container, LeanArgsNewLineSeparated, ...);
                            // a one-line `name (x : T) [A] :` keeps the old lenient reading (as module.js)
                            $dargs = $declspec->args;
                            $name = $dargs[0];
                            $d1 = $dargs[1] ?? null;
                            if ($d1 instanceof LeanBracket || $d1 instanceof LeanBrace)
                                $declspec = array_slice($dargs, 1);
                            else
                                $declspec = $d1->args;
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

// END OF module family (LeanParser stays in lean.php)
