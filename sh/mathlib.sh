# usage: bash sh/mathlib.sh

if [ ! -f "json/mathlib.jsonl" ]; then
  time lake build Mathlib
  time lake env lean sympy/printing/mathlib.lean > json/mathlib.jsonl
fi

if [ ! -f "json/mathlib.tsv" ]; then
  jq -r '[.name, .type] | @tsv' json/mathlib.jsonl > json/mathlib.tsv
fi


mysql --local-infile=1 -p$MYSQL_PWD -P$MYSQL_PORT -D axiom < sql/insert/mathlib.sql 2>&1 | tee test.log
grep -P "ERROR \d+ \(\w+\) at line \d+: Table 'axiom.mathlib' doesn't exist" test.log
if [ $? -eq 0 ]; then
  mysql -p$MYSQL_PWD -P$MYSQL_PORT -D axiom < sql/create/mathlib.sql
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Table 'mathlib' created successfully."
    bash $0 $*
  else
    echo "Failed to create table 'mathlib'."
    exit 1
  fi
fi
