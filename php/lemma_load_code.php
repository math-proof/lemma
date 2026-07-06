<?php

function lemma_contains_module(string $parentModule, string $module, int $depth = 0): bool
{
    if ($depth > 10)
        return false;
    $filePath = module_to_path($parentModule, '') . '.lean';
    if (!file_exists($filePath))
        return false;
    $fileObject = new SplFileObject($filePath, 'r');
    foreach ($fileObject as $line) {
        $line = rtrim($line);
        if (str_starts_with($line, 'import')) {
            $m = substr($line, strlen('import '));
            if ($m == $module)
                return true;
            if (lemma_contains_module($m, $module, $depth + 1))
                return true;
        } else
            break;
    }
    return false;
}

function load_lemma_code(string $module, string $leanFile): ?array
{
    $modify = false;
    $code = fetch_from_mysql(get_project_name(), $module);
    if ($code) {
        $code['imports'] = std\decode($code['imports']);
        $code['open'] = std\decode($code['open']);
        $code['def'] = std\decode($code['def']);
        $code['lemma'] = std\decode($code['lemma']);
        $code['error'] = std\decode($code['error']);
        $code['date'] = std\decode($code['date']);
    }

    if (!$code || !$code['lemma'] || !$code['date']) {
        $leanCode = compile(file_get_contents($leanFile));
        $syntax = [];
        $code = $leanCode->render2vue(false, $modify, $syntax);
        $import_syntax = function ($import) use ($leanCode, &$code, $module) {
            if (!in_array($import, $imports = $code['imports'])) {
                $prefix = 'Lemma.';
                $imports = array_filter($imports, fn ($m) => str_starts_with($m, $prefix));
                $imports = [...$imports];
                $offset = strlen($prefix);
                $imports = array_map(fn ($m) => substr($m, $offset), $imports);
                $imports = std\encode($imports);
                $imports = mysql\mysqlStr($imports);
                $sql = <<<EOF
WITH RECURSIVE dependencies AS (
	select 
		* 
	from 
		json_table(
			$imports,
			'$[*]' columns(module text path '$')
		) as jt
	UNION ALL
	SELECT
		SUBSTRING(jt.module, LOCATE('.', jt.module) + 1)
	FROM
		dependencies
		JOIN axiom.lemma as _t using(module)
		CROSS JOIN JSON_TABLE(
			_t.imports,
			'$[*]' COLUMNS (module text PATH '$')
		) AS jt
	WHERE
		jt.module LIKE 'Lemma.%'
)
select 
    count(*)
from dependencies 
    JOIN axiom.lemma as _t using(module)
    cross join json_table(
        imports,
        '$[*]' columns(module text path '$')
    ) as jt
where 
	jt.module = "$import"
EOF;
                [[$count]] = get_rows($sql, MYSQLI_NUM);
                if (!intval($count)) {
                    $imports = $code['imports'];
                    $hit = false;
                    foreach ($imports as $parent) {
                        if (lemma_contains_module($parent, $import)) {
                            $hit = true;
                            break;
                        }
                    }
                    if ($hit)
                        return false;
                    array_unshift($code['imports'], $import);
                    $leanCode->import($import);
                    return true;
                }
            }
            return false;
        };

        foreach ($syntax as $tac => $_) {
            switch ($tac) {
            case 'denote':
                $modify |= $import_syntax('sympy.core.relational');
                break;
            case 'mp':
            case 'mpr':
                $modify |= $import_syntax('sympy.core.logic');
                break;
            case '²':
            case '³':
            case '⁴':
                $modify |= $import_syntax('sympy.core.power');
                break;
            case 'Ici':
            case 'Iic':
            case 'Ioi':
            case 'Iio':
            case 'Ioc':
            case 'Ioo':
            case 'Icc':
            case 'Ico':
            case 'range':
                $modify |= $import_syntax('sympy.sets.sets');
                break;
            case 'setOf':
                $modify |= $import_syntax('sympy.concrete.quantifier');
                break;
            case 'LeanStack':
                $modify |= $import_syntax('sympy.tensor.stack');
                break;
            case 'Tensor':
                if (array_search('sympy.tensor.tensor', $code['imports']) === false &&
                    array_search('sympy.tensor.stack', $code['imports']) === false)
                    $modify |= $import_syntax('sympy.tensor.Basic');
                break;
            case 'IntegerRing':
                $modify |= $import_syntax('sympy.polys.domains');
                break;
            case 'KroneckerDelta':
                $modify |= $import_syntax('sympy.functions.special.tensor_functions');
                break;
            case 'eye':
                $modify |= $import_syntax('sympy.matrices.expressions.special');
                break;
            case '≃':
                $modify |= $import_syntax('stdlib.SEq');
                break;
            case 'softmax':
                $modify |= $import_syntax('sympy.tensor.functions');
                break;
            case 'sigmoid':
                $modify |= $import_syntax('sympy.vector.functions');
                break;
            }
        }
        if ($modify) {
            $file = new std\Text($leanFile);
            $file->write("$leanCode");
        }
    }

    if ($code)
        $code['module'] = $module;

    return $code;
}
