<?php
require dirname(__file__).'/../regexp/SyntaxMatcher.php';
require dirname(__file__).'/../xml/RichText.php';

if ($scanCriteria == null)
    $scanCriteria = [];

if (! $kwargs['limit'])
    $kwargs['limit'] = '40';

function join_condition($where, $cond) {
    return $where? "$where and $cond": $cond;
}

$set = $kwargs['set'];
if (isset($set['eq'])) {
    $eq = $set['eq'];
    $setter = $eq[0];
    [$lhs, $rhs] = $eq;
    if (is_array($lhs) && count($lhs) == 1)
        [[, $lhs]] = std\entries($lhs);
    $as = ["as" => [$rhs, $lhs]];
}
else {
    foreach ($set as &$assign) {
        $eq[] = $assign['eq'];
        $setter[] = $assign['eq'][0];
    }
    $as = [...$set];
    foreach ($as as &$assign) {
        $assign['as'] = $assign['eq'];
        unset($assign['eq']);
        [$lhs, $rhs] = $assign['as'];
        $assign['as'] = [$rhs, $lhs];
    }
}

$Field2Type = mysql\field_to_type($kwargs['update']);
$select = [];
foreach ($Field2Type as $Field => $Type) {
    if (str_starts_with($Field, "__") && str_ends_with($Field, "__"))
        continue;

    if (is_array($setter)) {
        $index = array_search($Field, $setter);
        if ($index !== false)
            $Field = is_string($index) ? $as : $as[$index];
    }
    elseif ($Field == $setter)
        $Field = $as;

    $select[] = $Field;
}

$return = [
    '__desc__' => [
        $database => [
            $table => $Field2Type
        ]
    ]
];
$Field2Type = ['__props__' => $props];
$kwargs_select = $kwargs; // create a copy of $kwargs
$kwargs_select['select'] = $select;
unset($kwargs_select['set']);

$kwargs_select['from'] = $kwargs_select['update'];
unset($kwargs_select['update']);

[$sql_select, $Field2Type] = parse_statement($kwargs_select, $Field2Type, $return);

if (std\is_list($setter)) {
    foreach($eq as $assign) {
        if (is_string($assign[1]))
            $functor[] = '';
        else {
            $functor[] = $assign[1];
            $scanCriteria = search_for_scan_criteria($kwargs, $Field2Type);
        }    
    }
}
else {
    if (is_string($eq[1]))
        $functor = '';
    else {
        [$functor] = array_keys($eq[1]);
        $scanCriteria = search_for_scan_criteria($kwargs, $Field2Type);
    }
}

$where = $return['where']?? '';

function detect_subquery(&$kwargs, $path=[]) {
    if (is_array($kwargs)) {
        if (std\is_list($kwargs)) {
            foreach (std\enumerate($kwargs) as [$i, $sub_kwargs]) {
                yield from detect_subquery($sub_kwargs, [...$path, $i]);
            }
        }
        elseif (isset($kwargs['from'])) {
            yield $path;
        }
        else {
            [[$func, $sub_kwargs]] = std\entries($kwargs);
            yield from detect_subquery($sub_kwargs, [...$path, $func]);
        }
    }
}

if ($functor) {
    if (is_array($functor)) {
        $update = parse_table($kwargs['update'], $Field2Type);
        $sql_update = "update $update set ";
        foreach(std\enumerate(std\zipped($functor, $setter, $eq)) as [$i, [$functor_i, $setter_i, $eq_i]]) {
            $sql_update .= $i? ", ": "";
            if ($functor_i)
                $sql_update .= "$setter_i = ".parse_expression($functor_i, $Field2Type);
            else {
                $new = $eq_i[1];
                $new = mysql\mysqlStr($new, $Field2Type[$setter_i]);
                $sql_update .= "$setter_i = $new";
                if ($Field2Type[$setter_i] != 'json') {
                    if (!mysql\is_numeric($Field2Type[$setter_i]))
                        $setter_i = "binary $setter_i";
                    $where = join_condition($where, "$setter_i != $new");
                }
            }
        }
        $sql_update .= ' ';
    }
    elseif (($with = $kwargs['with']) && ($as = $with['as']) && ($as[0] == $functor)) {
        $update = parse_table($kwargs['update'], $Field2Type);
        if (is_array($setter)) {
            [[$_t, $field]] = std\entries($setter);
            $sql_update = "update $update set $_t.$field = $functor.$field ";
        }
        else 
            $sql_update = "update $update set $setter = $functor.$setter ";
    }
    else {
        $update = parse_table($kwargs['update'], $Field2Type);
        $set = parse_expression($kwargs['set'], $Field2Type, ', ', $kwargs);
        $sql_update = "update $update set $set ";
    }
} else {
    $new = $eq[1];
    if ($scanCriteria) {

    } else {
        $paths = [];
        foreach (detect_subquery($kwargs['where']) as $path) {                
            if ($kwargs['update'] == std\getitem($kwargs['where'], ...$path)['from']) {
                $paths[] = $path;
            }
        }
        if ($paths) {
            if (!isset($return['with'])) {
                $with = [];
                foreach (std\enumerate($paths) as [$i, $path]) {
                    $sql = std\getitem($kwargs['where'], ...$path);
                    [$with[]] = parse_statement($sql, $Field2Type);
                    
                    $sql_kwargs = &std\getitem($kwargs_select['where'], ...$path);
                    $sql_kwargs['from'] = "_t$i";
                    unset($sql_kwargs['where']);
                }

                $as = implode(
                    ", ",
                    array_map(
                        fn ($args) => "_t$args[0] as ($args[1])",
                        iterator_to_array(std\enumerate($with))
                    )
                );

                $return['with'] = "with $as ";
                $return['where'] = parse_expression($kwargs_select['where'], $Field2Type);
            }
        }
        $update = parse_table($kwargs['update'], $Field2Type);
        $set = parse_expression($kwargs['set'], $Field2Type, ', ', $kwargs);
        $sql_update = "update $update set $set";
    }
}

if (count($scanCriteria) == 1) {
    if (! $functor && ! mysql\is_numeric($Field2Type[$setter]))
        $scanCriteria[] = [$setter, '!=', $new];
}

$primary_key = $Field2Type['__primary_key__'];
if (count($scanCriteria) > 1) {
    scan_data($sql_select, $Field2Type, $kwargs, true);
    [[$textField, [$regexp, $indexCaptured]], [$entityField, $op, $entityValue]] = $scanCriteria;

    $sql_update = [];
    foreach ($data as &$inst) {
        $primary_key_value = mysql\mysqlStr($inst[$primary_key], '', false);

        $setterValueStr = $inst[$setter];
        if (mysql\is_json($Field2Type[$setter]))
            $setterValueStr = std\encode($setterValueStr);

        $setterValueStr = mysql\mysqlStr($setterValueStr, $Field2Type[$setter], false);

        $sql_update[] = "update $database.$table set $setter = $setterValueStr where $primary_key = $primary_key_value";

        $training = array_key_exists('training', $inst) ? (int)$inst['training'] : 0;

        if ($setter != $table)
            $training |= 64;

        $inst['training'] = ~ $training;
    }
    // $sql_replace = array_map(fn ($args) => "($args[0], $args[1])");
    $sql = implode(";\n", $sql_update);
} else {
    if ($with = $return['with'])
        $sql_update = $with.$sql_update;

    $sql = $sql_select;
    load_data($sql, $Field2Type);

    if ($return['order'] || $return['offset']) {
        $kwargs_select['select'] = $primary_key;
        [$sql_select] = parse_statement($kwargs_select, $Field2Type);
        if ($return['limit']) {
            $sql_select = "select _$table.$primary_key from ($sql_select) as _$table";
            unset($return['limit']);
        }
        $return['where'] = "$primary_key in ($sql_select)";
    }

    if ($where = $return['where'])
        $sql_update .= " where $where";

    if ($limit = $return['limit'])
        $sql_update .= " limit $limit";

    $sql = $sql_update;
    foreach ($data as &$inst) {
        if (is_array($setter)) {
            foreach ($setter as $setter_i) {
                if (mysql\is_json($Field2Type[$setter_i]) && is_string($inst[$setter_i]))
                    $inst[$setter_i] = std\decode($inst[$setter_i]);
            }
        }
        elseif (mysql\is_json($Field2Type[$setter]) && is_string($inst[$setter]))
            $inst[$setter] = std\decode($inst[$setter]);

        $training = array_key_exists('training', $inst) ? (int)$inst['training'] : 0;

        if ($setter != $table)
            $training |= 64;

        $inst['training'] = ~ $training;
    }
}
?>