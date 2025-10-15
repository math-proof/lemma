with relational as (
  select
    regexp_replace(module, '^(\\w+)\\.([A-Z][\\w''!₀-₉]+)\\.(eq|as|ne)\\.([A-Z][\\w''!₀-₉]+)(.*)', '$1.$4.$3.$2$5') as module,
    module as original_module,
    substring_index(substring_index(module, '.', 2), '.', -1) as first,
    substring_index(substring_index(module, '.', 4), '.', -1) as second
  from
    lemma
  where
    module regexp '^(\\w+)\\.([A-Z][\\w''!₀-₉]+)\\.(eq|as|ne)\\.([A-Z][\\w''!₀-₉]+)(.*)' and json_length(imports) > 0
  having
    first != second and (char_length(first) < char_length(second) or char_length(first) = char_length(second) and first < second)
),
equation as (
  select
    regexp_replace(module, '^(\\w+)\\.(S?Eq)_([A-Z][\\w''!₀-₉]+)(.*)', '$1.$2$3$4') as module,
    module as original_module
  from
    lemma
  where
    module regexp '^(\\w+)\\.S?Eq_([A-Z][\\w''!₀-₉]+)(.*)' and json_length(imports) > 0
),
equivalence as (
  select
    regexp_replace(module, '^(\\w+)\\.(.+)\\.(is)\\.(.+)(\\.of\\..+)?', '$1.$4.$3.$2$5') as module,
    module as original_module,
    regexp_replace(module, '^(\\w+)\\.(.+)\\.(is)\\.(.+)(\\.of\\..+)?', '$2') as first,
    regexp_replace(module, '^(\\w+)\\.(.+)\\.(is)\\.(.+)(\\.of\\..+)?', '$4') as second
  from
    lemma
  where
    module regexp '^(\\w+)\\.(.+)\\.(is)\\.(.+)(\\.of\\..+)?' and json_length(imports) > 0
  having
    first != second and (char_length(first) < char_length(second) or char_length(first) = char_length(second) and first < second)
),
symm as (
  select 
    module,
    original_module
  from 
    relational
  union all
  select
    module,
    original_module
  from
    equation
  union all
  select
    module,
    original_module
  from
    equivalence
)
select
  concat(
    -- 1st option
    'rm Lemma/', replace(module, '.', '/'), '.lean\n', 
    'sed -i ''s/^@\\[main\\]/@[main, comm]/'' ', concat('Lemma/', replace(original_module, '.', '/'), '.lean'), '\n',
    'find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/\\b', replace(module, '.', '\\.'), '(\\b[^.]|$)/', original_module, '\\1/g" {} +\n',
    concat('grep -Erl ''\\b', replace(original_module, '.', '\\.'), '(\\b[^.]|$)'' Lemma sympy | while read -r file; do gawk -i inplace ''/(^|[^[:alnum:]_])', replace(original_module, '.', '\\.'), '([^[:alnum:]_.]|$)/ { if (seen[$0]++) next } { print }'' "$file"; done\n'),
    'bash sh/run.sh\n\n',
    -- 2nd option
    'rm Lemma/', replace(original_module, '.', '/'), '.lean\n', 
    'sed -i ''s/^@\\[main\\]/@[main, comm]/'' ', concat('Lemma/', replace(module, '.', '/'), '.lean'), '\n',
    'find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/\\b', replace(original_module, '.', '\\.'), '(\\b[^.]|$)/', module, '\\1/g" {} +\n',
    concat('grep -Erl ''\\b', replace(module, '.', '\\.'), '(\\b[^.]|$)'' Lemma sympy | while read -r file; do gawk -i inplace ''/(^|[^[:alnum:]_])', replace(module, '.', '\\.'), '([^[:alnum:]_.]|$)/ { if (seen[$0]++) next } { print }'' "$file"; done\n'),
    'bash sh/run.sh\n\n'
  )
from
  lemma
join
  symm using (module)
where
  json_length(imports) > 0
