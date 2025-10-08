# usage :
# bash sh/run.sh
start_time=$(date +%s)
source ./sh/utility.sh

user=$(basename $(dirname $(cd $(dirname $0) && pwd)))
echo "user = $user"

> test.lean

declare -A imports_dict
function echo_import {
  file=$1
  lemma=${file%.lean}
  module=${lemma////.}
  echo "import $module" >> test.lean
  # extract import statements from the lean file
  module=${module#Lemma.}
  mapfile -t lines < <(grep -E '^import[[:space:]]+' $file | sed -E 's/^import[[:space:]]+//')
  if [ ${#lines[@]} -eq 0 ]; then
    imports_dict[$module]="[]"
  else
    imports_dict[$module]=$(printf '%s\n' "${lines[@]}" | jq -R . | jq -s .)
  fi
}

while read -r file; do
  echo_import "$file"
done < <(find Lemma -type f -name "*.lean" -not -name "*.echo.lean") 

touch test.log
lake setup-file test.lean 2>&1 | tee test.log

sed -i -E "s/^import //" test.lean
imports=$(cat test.lean)
> test.lean

imports=($imports)
echo "modules:"
touch test.sql

echo "INSERT INTO lemma (user, module, imports, open, def, lemma, error, date) VALUES " > test.sql
for module in ${imports[*]}; do
  # echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [ -z "${imports_dict[$module]}" ]; then
    echo "imports_dict[$module] = " ${imports_dict[$module]}
    continue
  fi
  submodules=${imports_dict[$module]}
  submodules=${submodules//\'/\'\'}
  echo "  ('$user', \"$module\", '$submodules', '[]', '[]', '[]', '[]', '[]')," >> test.sql
done
grep -rl --include='*.lean' --exclude='*.echo.lean' -E "^@\[main, [^]]+\]" Lemma | while read -r file; do
  module=${file#Lemma/}
  module=${module//\//.}
  module=${module%.lean}
  if grep -q -E '^@\[main, .*\bcomm( [0-9]+)?\b' "$file"; then
    IFS='.' read -ra tokens <<< $module
    deBruijn=$(grep -Eo '^@\[main, .*\bcomm( [0-9]+)?\b' "$file")
    case "${tokens[2]}" in
      eq|is|as|ne)
        tmp=${tokens[1]}
        tokens[1]=${tokens[3]}
        tokens[3]=$tmp
        ;;
      *)
        first=${tokens[1]}
        if [[ $first == Eq_* ]]; then
          first="Eq${first:3}"
        elif [[ $first == Eq* ]]; then
          first="Eq_${first:2}"
        elif [[ $first == SEq_* ]]; then
          first="SEq${first:4}"
        elif [[ $first == SEq* ]]; then
          first="SEq_${first:3}"
        else
          echo "panic! Expected the operator to be 'S?Eq.*', got: $first"
        fi
        tokens[1]=$first
        ;;
    esac
    new_module=$(IFS='.'; echo "${tokens[*]}")
    echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> test.sql
  fi
  if grep -q -E '^@\[main, .*\bmp\b' "$file"; then
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$ ]]; then
      new_module="${BASH_REMATCH[1]}.${BASH_REMATCH[3]}.of.${BASH_REMATCH[2]}${BASH_REMATCH[4]}"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> test.sql
    fi
  fi
  if grep -q -E '^@\[main, .*\bmpr\b' "$file"; then
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$ ]]; then
      new_module="${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.of.${BASH_REMATCH[3]}${BASH_REMATCH[4]}"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> test.sql
    fi
  fi
  if grep -q -E '^@\[main, .*\bmp\.comm\b' "$file"; then
    IFS='.' read -ra tokens <<< $module
    echo "@[mp.comm] at $file"
  fi
  if grep -q -E '^@\[main, .*\bmpr\.comm\b' "$file"; then
    IFS='.' read -ra tokens <<< $module
    echo "@[mpr.comm] at $file"
  fi
done
sed -i '$ s/,$/\nON DUPLICATE KEY UPDATE imports = VALUES(imports), error = VALUES(error);/' test.sql

echo "plausible:"
sorryModules=($(grep -P "^warning: (\./)*[\w'/]+\.lean:\d+:\d+: declaration uses 'sorry'" test.log | sed -E 's#^warning: ([.]/)*##' | sed -E "s/\.lean:[0-9]+:[0-9]+: declaration uses 'sorry'//" | sed 's#/#.#g' | sort -u))
for module in ${sorryModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [[ $module =~ ^sympy ]]; then
    continue
  fi
  echo "UPDATE lemma set error = '[{\"code\": \"\", \"file\": \"\", \"info\": \"declaration uses ''sorry''\", \"line\": 0, \"type\": \"warning\"}]' where user = '$user' and module = \"$module\";" >> test.sql
done

echo "failed:"
failingModules=($(awk '/Some required builds logged failures:/{flag=1;next}/^[^-]/{flag=0}flag' test.log | sed 's/^- //'))
for module in ${failingModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [[ $module =~ ^sympy ]]; then
    continue
  fi
  echo "UPDATE lemma set error = '[{\"code\": \"\", \"file\": \"\", \"info\": \"\", \"line\": 0, \"type\": \"error\"}]' where user = '$user' and module = \"$module\";" >> test.sql
done

if [ -z "$MYSQL_USER" ]; then
  echo "MYSQL_USER is not set, acquiring it from ~/.bash_profile"
  source ~/.bash_profile
fi
MYSQL_PORT=${MYSQL_PORT:-3306}
# Create a temporary config file with .cnf extension
tempConfigPath=$(mktemp)
mv "$tempConfigPath" "${tempConfigPath}.cnf"
tempConfigPath="${tempConfigPath}.cnf"
cat > "$tempConfigPath" << EOF
[client]
user = $MYSQL_USER
password = $MYSQL_PASSWORD
port = $MYSQL_PORT
EOF

mysql --defaults-extra-file="$tempConfigPath" -D axiom -e "update lemma set error = NULL" 2>&1 | tee test.log

grep -P "ERROR \d+ \(\d+\): Unknown database 'axiom'" test.log
if [ $? -eq 0 ]; then
  echo "CREATE DATABASE axiom;"
  mysql --defaults-extra-file="$tempConfigPath" -e "CREATE DATABASE axiom;"
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Database 'axiom' created successfully."
    bash $0 $*
    exit 0
  else
    echo "Failed to create database 'axiom'."
    exit 1
  fi
fi
mysql --defaults-extra-file="$tempConfigPath" -D axiom < test.sql 2>&1 | tee test.log
grep -P "ERROR \d+ \(\w+\) at line \d+: Table 'axiom.lemma' doesn't exist" test.log
if [ $? -eq 0 ]; then
  mysql --defaults-extra-file="$tempConfigPath" -D axiom < sql/create/lemma.sql
  # Check if the mysql command was successful
  if [ $? -eq 0 ]; then
    echo "Table 'lemma' created successfully."
    bash run.sh
    exit 0
  else
    echo "Failed to create table 'lemma'."
    exit 1
  fi
fi
mysql --defaults-extra-file="$tempConfigPath" -D axiom -e "delete from lemma where error is NULL" 2>&1 | tee test.log
end_time=$(date +%s)
time_cost=$((end_time - start_time))

# post-processing

function remove_invalid_ir_file {
  module=${1#*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, since $module doesn't exist"
    rm $1
  fi
}

find .lake/build/ir -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
    remove_invalid_ir_file $file
done

function remove_invalid_lib_file {
  module=${1#*/*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, since $module doesn't exist"
    rm $1
  fi
}

find .lake/build/lib -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
    remove_invalid_lib_file $file
done

function remove_invalid_echo_file {
  module=${1%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    echo "rm $1, since $module doesn't exist"
    rm $1
  fi
}

find Lemma -type f -regex '.*\.echo\.lean$' | while read -r file; do
    remove_invalid_echo_file $file
done

find . -type d -empty -exec rmdir {} +
find .lake/build -type d -empty -exec rmdir {} +

echo "seconds cost    = $time_cost"
echo "total theorems  = ${#imports[@]}"
echo "total plausible = ${#sorryModules[@]}"
echo "total failed    = ${#failingModules[@]}"
bash sh/delete_open.sh
bash sh/delete_import.sh
rm -f "$tempConfigPath"
