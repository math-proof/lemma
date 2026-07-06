<?php

function lemma_decode_code(?array $code): ?array
{
    if (!$code)
        return null;
    $code['imports'] = std\decode($code['imports']);
    $code['open'] = std\decode($code['open']);
    $code['def'] = std\decode($code['def']);
    $code['lemma'] = std\decode($code['lemma']);
    $code['error'] = std\decode($code['error']);
    $code['date'] = std\decode($code['date']);
    return $code;
}

function load_lemma_code(string $module, string $leanFile, ?array $code = null): ?array
{
    if ($code === null)
        $code = lemma_decode_code(fetch_from_mysql(get_project_name(), $module));
    else
        $code = lemma_decode_code($code);

    if (!$code || !$code['lemma'] || !$code['date']) {
        if (!is_readable($leanFile))
            return null;
        $leanCode = compile(file_get_contents($leanFile));
        $code = $leanCode->render2vue(false);
    }

    if ($code)
        $code['module'] = $module;

    return $code;
}
