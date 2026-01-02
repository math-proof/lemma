<!DOCTYPE html>
<meta charset="UTF-8">
<?php
require_once 'utility.php';

$module = $_GET['new'];

$module = str_replace("/", ".", $module);

function fetch_codes($module)
{
    $leanFile = module_to_lean($module);
    if (file_exists($leanFile)) {
        $code = compile(file_get_contents($leanFile))->render2vue(false);
        $code['date']['created'] = date('Y-m-d');
        unset($code['date']['updated']);
        return $code;
    }
}

$code = fetch_codes($module);
if (!$code) {
    require_once 'init.php';
    $sql = <<<EOT
select 
    *
from 
    mathlib 
where 
    name = "$module"
EOT;
    [$lemma] = get_rows($sql);
    if ($lemma) {
        $lemma['imply'] = std\decode($lemma['imply']);
        $lemma['imply']['lean'] .= " :=";
        $lemma['imply']['latex'] .= "\\tag*{ :=}";
        $proof = $module;
        $vars = [];
        if ($explicit = $lemma['default'] ?? null) {
            unset($lemma['default']);
            $parser = compile($explicit);
            array_push($vars, ...$parser->parse_vars_default($parser->args));
            $explicit .= " :";
            $lemma['explicit'] = $explicit;
        }

        if ($given = $lemma['given'] ?? null) {
            $given = std\decode($given);
            foreach ($given as $g) {
                $parser = compile($g['lean']);
                array_push($vars, ...$parser->parse_vars_default($parser->args));
            }
            if (!$explicit)
                $given[count($given) - 1]['lean'] .= " :";
            $lemma['given'] = $given;
        }
        $proof .= implode("", array_map(fn($args) => " $args[0]", $vars));
        $lemma['proof'] = [
            [
                'lean' => $proof
            ]
        ];
    } else {
        $sql = <<<EOT
select 
    *
from 
    axiom
where 
    axiom = "$module"
EOT;
        function split_latex($latex)
        {
            preg_match_all('/\\\\\[.+?\\\\\]/', $latex, $match, PREG_SET_ORDER);
            foreach ($match as &$m)
                [$m] = $m;
            return $match;
        }
        function strip_latex($latex)
        {
            return preg_replace("/\\\\tag\*\{.*\}$/", "", std\substring($latex, 2, -2));
        }
        function join_lean($lean) {
            return implode(' ∧ ', array_map(fn($lean) => str_contains($lean, '∨')? "($lean)" : $lean, $lean));
        }

        function join_latex($latex){
            $latex = array_map(fn($latex) => strip_latex($latex), split_latex($latex));
            $latex = array_map(fn($latex) => str_contains($latex, '\vee ')? "\\left($latex\\right)" : $latex, $latex);
            return implode(' \land ', $latex);
        }

        $subscript_map = [
            '0' => '₀',
            '1' => '₁',
            '2' => '₂',
            '3' => '₃',
            '4' => '₄',
            '5' => '₅',
            '6' => '₆',
            '7' => '₇',
            '8' => '₈',
            '9' => '₉'
        ];
        function replace_latex($latex, $num)
        {
            return preg_replace("/(?<=\\\\tag\*\{).*(?=\}$)/", "\${h}$num\$", std\substring($latex, 2, -2));
        }

        function accumulate_given($lean, $latex)
        {
            global $subscript_map;
            $given = [];
            $count = count($lean);
            foreach (std\range($count) as $i) {
                $subscript_i = $count > 1 ? strtr("$i", $subscript_map) : '';
                $lean_i = "(h$subscript_i : " . $lean[$i] . ")";
                $subscript_i = $count > 1 ? "_$i" : '';
                if ($i == $count - 1) {
                    $lean_i .= " :";
                    $subscript_i .= " :";
                }
                $given[] = [
                    'lean' => $lean_i,
                    'latex' => replace_latex($latex[$i], $subscript_i)
                ];
            }
            return $given;
        }

        [$lemma] = get_rows($sql);
        $latex = $lemma['latex'];
        $latexs = explode("\n", $latex);
        $latex = $latexs[0];
        $lean = $lemma['lean'];
        $leans = std\decode($lean);
        $lean = $leans[0];
        $tokens = explode('.', $module);
        $of_index = array_search('of', $tokens);
        if ($of_index !== false) {
            $num_hypotheses = 0;
            for ($i = $of_index + 1; $i <= count($tokens); $i++) {
                if (ctype_upper($tokens[$i][0]))
                    $num_hypotheses++;
                else 
                    break;
            }
            if ($num_hypotheses > 0) {
                $lean = ["tab" => array_slice($leans, 0, $num_hypotheses + 1)];
                $latex = implode("\t", array_slice($latexs, 0, $num_hypotheses + 1));
            }
        }

        if (str_contains($module, '.given.')) {
            $module = str_replace('.given.', '.of.', $module);
            if (is_array($lean) && array_key_exists('tab', $lean)) {
                $lean = $lean['tab'];
                $latex = explode("\t", $latex);

                $end_lean = end($lean);
                $end_latex = end($latex);
                if (is_array($end_lean))
                    $end_latex = split_latex($end_latex);
                else {
                    $end_lean = [$end_lean];
                    $end_latex = [$end_latex];
                }
                $lemma['given'] = accumulate_given($end_lean, $end_latex);
                array_pop($lean);
                array_pop($latex);

                if (count($lean) == 1) {
                    $lean = $lean[0];
                    if (is_array($lean)) {
                        $lean = join_lean($lean);
                        $latex = join_latex($latex[0]);
                    }
                    else
                        $latex = strip_latex($latex[0]);
                } else {
                    $lean = join_lean($lean);
                    $latex = join_latex($latex);
                }
                $lemma['imply'] = [
                    'lean' => $lean,
                    'latex' => $latex
                ];
            } else
                $lemma['imply'] = [
                    'lean' => $lean,
                    'latex' => strip_latex($latex)
                ];
        } else {
            if (is_array($lean) && array_key_exists('tab', $lean)) {
                $lean = $lean['tab'];
                $latex = explode("\t", $latex);

                $end_lean = end($lean);
                $end_latex = end($latex);
                if (is_array($end_lean)) {
                    $end_lean = join_lean($end_lean);
                    $end_latex = join_latex($end_latex);
                } else
                    $end_latex = strip_latex($end_latex);
                $lemma['imply'] = [
                    'lean' => $end_lean,
                    'latex' => $end_latex
                ];
                array_pop($lean);
                array_pop($latex);
                if (count($lean) == 1 && is_array($lean[0])) {
                    $lean = $lean[0];
                    $latex = split_latex($latex[0]);
                }
                $lemma['given'] = accumulate_given($lean, $latex);
            } else
                $lemma['imply'] = [
                    'lean' => $lean,
                    'latex' => strip_latex($latex)
                ];
        }
        $lemma['imply']['lean'] .= " := by";
        $lemma['imply']['latex'] .= "\\tag*{ := by}";
        $proof = 'sorry';
        $lemma['proof'] = [
            'by' => [
                [
                    'lean' => $proof
                ]
            ]
        ];

        $module = preg_replace_callback('#(^\w+[./\\\\].+[./\\\\])(In|Is)(?=[./\\\\][A-Z])#', function($matches) {
            return $matches[1] . strtolower($matches[2]);
        }, $module);
    }
    $lemma['name'] = 'main';
    $lemma['accessibility'] = 'private';
    $lemma['attribute'] = ['main'];

    $code = [
        'imports' => [],
        'open' => [],
        'def' => [],
        'lemma' => [$lemma],
        'error' => [],
        'date' => [
            'created' => date('Y-m-d')
        ],
    ];
}
$code['name'] = $module;
?>

<title><?php echo $module; ?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<?php
include_once 'script.php';
?>
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script type=module>
    import * as codemirror from "./static/codemirror/lib/codemirror.js"
    import * as lean from "./static/codemirror/mode/lean/lean.js"
    import * as active_line from "./static/codemirror/addon/selection/active-line.js"
    import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
    import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"
    import * as comment from "./static/codemirror/addon/comment/comment.js"

    createApp('newTheorem', <?php echo std\encode($code) ?>);
</script>