with mp as (
  select
    module,
    regexp_replace(module, '^(\\w+)\\.(.+)\\.is\\.(.+)(\\.of\\..+)?', '$1.$3.of.$2$4') as module_mp,
    regexp_replace(module, '^(\\w+)\\.(.+)\\.is\\.(.+)(\\.of\\..+)?', '$1.$2.of.$3$4') as module_mpr
  from
    lemma
  where
    module regexp '^(\\w+)\\.(.+)\\.is\\.(.+)(\\.of\\..+)?' and json_length(imports) > 0
  having
    module_mp != module_mpr
),
distinct_mp as (
  select 
    mp.module,
    ANY_VALUE(module_mp) as module_mp,
    ANY_VALUE(module_mpr) as module_mpr
  from
    mp
  join
    lemma 
    on 
      lemma.module = mp.module_mp or lemma.module = mp.module_mpr
  where
    json_length(imports) > 0
  group by mp.module
)
select
  concat(
    -- 1st option
    'rm -f Lemma/', replace(module_mp, '.', '/'), '.lean\n', 
    'sed -i -E ''s/^@\\[(main[^]]*)\\]/@[\\1, mp]/'' ', concat('Lemma/', replace(module, '.', '/'), '.lean'), '\n',
    'find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/\\b', replace(module_mp, '.', '\\.'), '(\\b[^.]|$)/', module, '\\1/g" {} +\n\n',
    -- 2nd option
    'rm -f Lemma/', replace(module_mpr, '.', '/'), '.lean\n', 
    'sed -i -E ''s/^@\\[(main[^]]*)\\]/@[\\1, mpr]/'' ', concat('Lemma/', replace(module, '.', '/'), '.lean'), '\n',
    'find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/\\b', replace(module_mpr, '.', '\\.'), '(\\b[^.]|$)/', module, '\\1/g" {} +\n\n',
    -- postprocess
    concat('grep -Erl ''\\b', replace(module, '.', '\\.'), '(\\b[^.]|$)'' Lemma sympy | while read -r file; do gawk -i inplace ''/(^|[^[:alnum:]_])', replace(module, '.', '\\.'), '([^[:alnum:]_.]|$)/ { if (seen[$0]++) next } { print }'' "$file"; done\n'),
    'bash sh/run.sh\n\n'
  )
from
  distinct_mp
