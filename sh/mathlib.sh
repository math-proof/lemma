# usage: bash sh/mathlib.sh

if [ ! -f "json/mathlib.jsonl" ]; then
  time lake build Mathlib
  # each lean process needs ~7GB RAM; keep parallel chunks low
  chunks=${MATHLIB_CHUNKS:-2}
  for ((i = 0; i < chunks; i++)); do
    CHUNK_IDX=$i NUM_CHUNKS=$chunks lake env lean sympy/printing/mathlib.lean > "json/mathlib.$i.jsonl" &
  done
  wait
  cat $(seq -f "json/mathlib.%g.jsonl" 0 $((chunks - 1))) > json/mathlib.jsonl
  rm -f $(seq -f "json/mathlib.%g.jsonl" 0 $((chunks - 1)))
fi

if [ ! -f "json/mathlib.tsv" ]; then
  jq -r '[.name, .type] | @tsv' json/mathlib.jsonl > json/mathlib.tsv
fi


MYSQL_PORT=${MYSQL_PORT:-3306}

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
