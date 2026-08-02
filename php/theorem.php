<?php
// ^ *error_log
require_once 'init.php';
if ($input != null) {
    $inputs[] = piece_together($input);
}

$numOfReturnsFromApply = $lengths[$indexOfYield];

$latex = [];
$i = 0;
$statements = '';
$where = '';

function is_latex_with_tabs($latex, &$matches)
{
    if (std\contains($latex, "\t")) {
        $matches = [];
        foreach (explode("\t", $latex) as $tex) {
            if (preg_match_all('/\\\\\[.+?\\\\\]/', $tex, $match, PREG_SET_ORDER)) {
                foreach ($match as &$m) {
                    [$m] = $m;
                }
                $matches[] = join('', $match);
            }
            else 
                return false;
        }
        return true;
    }

    if (preg_match_all('/\\\\\[.+?\\\\\]/', $latex, $matches, PREG_SET_ORDER)) {
        foreach ($matches as &$args) {
            $args = $args[0];
        }
        return true;
    }
    
    return false;
}

$resultsFromApply = [];

foreach ($data ? explode("\n", end($data)) : yield_from_mysql(get_user(), $module) as $statement) {

    if ($i == $indexOfYield) {
        if ($numOfReturnsFromApply == 1) {
            
            -- $lengths[$i];
            if (!$lengths[$i]) {
                if (is_latex_with_tabs($statement, $matches)) {                    
                    switch (count($matches)) {
                        case 3:
                            [$given, $where, $imply] = $matches;
                            break;
                        case 2:
                            if ($numOfRequisites) {
                                [$given, $imply] = $matches;
                                $where = '';
                            } else {
                                [$where, $imply] = $matches;
                                $given = '';
                            }
                            break;
                        case 1:
                            $where = '';
                            $given = '';
                            [$imply] = $matches;
                            break;
                    }
                }

                $given = [
                    'py' => array_shift($inputs),
                    'latex' => $given
                ];

                $statements = '';
                ++ $i;
            }
        } else {
            $resultsFromApply[] = $statement;

            -- $lengths[$i];
            if (!$lengths[$i]) {
                $given = array_slice($resultsFromApply, 0, $lengthOfGiven);
                $given = join('', $given);
                $given = [
                    'py' => $inputs[0],
                    'latex' => $given
                ];

                if ($lengthOfWhere) {
                    $where = array_slice($resultsFromApply, $lengthOfGiven, $lengthOfWhere);
                    $where = join('', $where);
                } else {
                    $where = '';
                }

                $imply = array_slice($resultsFromApply, $lengthOfGiven + $lengthOfWhere);
                $imply = join('', $imply);

                $statements = '';
                $inputs = array_slice($inputs, 1);
                ++ $i;
            }
        }
    } else {
        $statements .= $statement;
        if ($i >= count($lengths))
            continue;

        -- $lengths[$i];
        if (!$lengths[$i]) {
            $latex[] = $statements;
            $statements = '';
            ++ $i;
        }
    }
}

$size = count($latex);
$unused = array_slice($inputs, $size);

$prove = array_map(fn($i) => [
    'py' => $inputs[$i],
    'latex' => $latex[$i]
], std\ranged($size));

$logStr = [];
foreach ($logs as $log) {
    $log = str_replace("\\", "\\\\", $log);
    $log = str_replace("'", "\\'", $log);
    $logStr[] = "'$log'";
}

$logStr = implode(",", $logStr);
$logStr = "[$logStr]";

?>

<title><?php echo $title;?></title>
<link rel=stylesheet href="static/codemirror/lib/codemirror.css">
<link rel=stylesheet href="static/codemirror/theme/eclipse.css">
<link rel=stylesheet href="static/codemirror/addon/hint/show-hint.css">
<link rel=stylesheet href="static/unpkg.com/katex@0.16.21/dist/katex.min.css">
<style>
div {
	caret-color: transparent;
}
</style>
<body></body>
<script src="static/unpkg.com/vue@3.2.47/dist/vue.global.prod.js"></script>
<script src="static/unpkg.com/vue3-sfc-loader@0.8.4/dist/vue3-sfc-loader.js"></script>

<script src="static/unpkg.com/axios@0.24.0/dist/axios.min.js"></script>
<script src="static/unpkg.com/qs@6.10.2/dist/qs.js"></script>
<script src="static/unpkg.com/clipboard@2.0.10/dist/clipboard.min.js"></script>

<script src='static/js/std.js'></script>
<script src='static/js/utility.js'></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/katex.min.js"></script>
<script defer src="static/unpkg.com/katex@0.16.21/dist/contrib/auto-render.min.js"></script>
<script type=module>
import * as codemirror from "./static/codemirror/lib/codemirror.js"
import * as python from "./static/codemirror/mode/python/python.js"
import * as active_line from "./static/codemirror/addon/selection/active-line.js"
import * as show_hint from "./static/codemirror/addon/hint/show-hint.js"
import * as matchbrackets from "./static/codemirror/addon/edit/matchbrackets.js"

var logs = <?php echo $logStr?>;
var error = [];

for (let i = 0; i < logs.length; ++i){
    var log = logs[i];
    if (log.startsWith('{') && log.endsWith('}')){
    	error.push(JSON.parse(log));
    	logs.delete(i);
        break;
    }
    
    if (log.startsWith('[') && log.endsWith(']')){
    	logs.delete(i);
        error = JSON.parse(log);
        break;
    }
}

createApp('render', {
	error : error,
    logs : logs,
    prove : <?php echo std\encode($prove)?>,
    unused : <?php echo std\encode($unused)?>,
    module: <?php echo std\encode($module)?>,
    given: <?php echo std\encode($given)?>,
    imply: <?php echo std\encode($imply)?>,
    where: <?php echo std\encode($where)?>,
    createdTime: `<?php echo $createdTime?>`,
    updatedTime: `<?php echo isset($updatedTime)? $updatedTime: ''?>`,
});

var data = <?php echo std\encode($data)?>;
if (data) {
    console.log(`update mysql data`);
    console.log(data);

    data = JSON.stringify(data);
    form_post("php/request/mysql/update.php", {data}).then(res => {
        console.log('success code = ');
        console.log(res);
    });
}

//http://codemirror.net/doc/manual.html
//http://docs.mathjax.org/en/latest/
</script>


