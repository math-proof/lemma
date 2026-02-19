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

transformExpr() {
  local s0="$1"
  local s="$2"
  # If s0 == '_', return s
  if [[ "$s0" == "_" ]]; then
    printf '%s\n' "$s"
    return
  fi
  # If s0 matches [A-Z]
  if [[ "$s0" =~ [A-Z] ]]; then
    # If s matches ^[a-zA-Z0-9'!₀-₉]+?S
    if printf '%s' "$s" | grep -Pq "^[a-zA-Z0-9'!₀-₉]+?S"; then
      printf '%s\n' "${s0}${s}"
      return
    fi
  fi
  # Default case
  printf '%s\n' "_${s0}${s}"
}

transformPrefix() {
  local s="$1"
  local prefix s0 s1 s2 rest transformed
  # Pattern 1: EqX, NeX, OrX
  if [[ "$s" =~ ^(Eq|Ne|Or)(.)(.*)$ ]]; then
    prefix="${BASH_REMATCH[1]}"
    s2="${BASH_REMATCH[2]}"
    rest="${BASH_REMATCH[3]}"
    transformed=$(transformExpr "$s2" "$rest")
    echo "${prefix}${transformed}"
    return
  fi
  # Pattern 2: SEqX, HEqX, IffX, AndX
  if [[ "$s" =~ ^([SH]Eq|Iff|And)(.)(.*)$ ]]; then
    prefix="${BASH_REMATCH[1]}"
    s2="${BASH_REMATCH[2]}"
    rest="${BASH_REMATCH[3]}"
    transformed=$(transformExpr "$s2" "$rest")
    echo "${prefix}${transformed}"
    return
  fi
  # Pattern 3: LtX, LeX, GtX, GeX
  if [[ "$s" =~ ^(L|G)(t|e)(.)(.*)$ ]]; then
    s0="${BASH_REMATCH[1]}"
    s1="${BASH_REMATCH[2]}"
    s2="${BASH_REMATCH[3]}"
    rest="${BASH_REMATCH[4]}"
    # Flip the first character
    if [[ "$s0" == "L" ]]; then
      newS0="G"
    else
      newS0="L"
    fi
    transformed=$(transformExpr "$s2" "$rest")
    echo "${newS0}${s1}${transformed}"
    return
  fi
  # Pattern 3 (short version): Lt, Le, Gt, Ge
  if [[ "$s" =~ ^(L|G)(t|e)$ ]]; then
    s0="${BASH_REMATCH[1]}"
    s1="${BASH_REMATCH[2]}"
    if [[ "$s0" == "L" ]]; then
      newS0="G"
    else
      newS0="L"
    fi
    echo "${newS0}${s1}"
    return
  fi
  # If no patterns matched, return original string
  echo "$s"
}

Not() {
  local token="$1"
  if [[ "$token" == Not* ]]; then
    # Remove leading "Not"
    printf '%s\n' "${token:3}"
  elif [[ "$token" == Eq* ]]; then
    # Replace leading "Eq" with "Ne"
    printf '%s\n' "Ne${token:2}"
  elif [[ "$token" == Ne* ]]; then
    # Replace leading "Ne" with "Eq"
    printf '%s\n' "Eq${token:2}"
  else
    # Prepend "Not"
    printf '%s\n' "Not${token}"
  fi
}

# Find all .lean files except *.echo.lean under Lemma/
find Lemma -type f -name "*.lean" ! -name "*.echo.lean" | while read -r file; do
  # Get relative path
  rel_file="${file#./}"
  content=$(<"$file")
  # Match main attribute and optional constructor order comment
  if [[ $content =~ $'\n/--\n(.*)\n-/' ]]; then
    constructor_comment="${BASH_REMATCH[1]}"
  else
    constructor_comment=""
  fi
  if [[ $content =~ $'\n@\[[[:space:]]*main,[[:space:]]*([^\]]+)\]' ]]; then
    attributes="${BASH_REMATCH[1]}"
  else
    continue
  fi
  # Convert file path to module name
  module="${rel_file#Lemma/}"
  module="${module//\\/.}"
  module="${module%.lean}"
  constructor_order=false
  if [[ $constructor_comment == *"constructor order"* ]]; then
    constructor_order=true
  fi
  # Handle comm attribute
  if [[ $attributes =~ \bcomm([[:space:]]*([0-9]+))?\b ]]; then
    deBruijn="${BASH_REMATCH[2]}"
    IFS='.' read -ra tokens <<< "$module"
    case "${tokens[2]}" in
      eq|is|as|ne|lt|le|gt|ge)
        tmp="${tokens[1]}"
        tokens[1]="${tokens[3]}"
        tokens[3]="$tmp"
        ;;
      *)
        deBruijn=${deBruijn:-0}
        index=$((${#tokens[@]}-1))
        increment=-1
        while [[ $deBruijn -gt 0 ]]; do
          if ((deBruijn & 1)); then
            tokens[$index]=$(transformPrefix "${tokens[$index]}")
          fi
          deBruijn=$((deBruijn >> 1))
          index=$((index + increment))
        done
        tokens[1]=$(transformPrefix "${tokens[1]}")
        ;;
    esac
    new_module=$(IFS=. ; echo "${tokens[*]}")
    echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
  fi
  # Handle mp attribute
  if [[ $attributes =~ \bmp\b ]]; then
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$ ]]; then
      new_module="${BASH_REMATCH[1]}.${BASH_REMATCH[3]}.of.${BASH_REMATCH[2]}${BASH_REMATCH[4]}"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    fi
  fi
  # Handle mpr attribute
  if [[ $attributes =~ \bmpr\b ]]; then
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)(\.of\..+)?$ ]]; then
      new_module="${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.of.${BASH_REMATCH[3]}${BASH_REMATCH[4]}"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    fi
  fi
  # Handle mp.comm
  if [[ $attributes =~ \bmp\.comm\b ]]; then
    IFS='.' read -ra tokens <<< "$module"
    if [[ "${tokens[2]}" == "is" ]]; then
      new_tokens=()
      for t in "${tokens[@]}"; do
        [[ "$t" != "of" ]] && new_tokens+=("$t")
      done
      tmp=$(transformPrefix "${new_tokens[1]}")
      new_tokens[1]=$(transformPrefix "${new_tokens[3]}")
      new_tokens[2]="of"
      new_tokens[3]="$tmp"
      new_module=$(IFS=. ; echo "${new_tokens[*]}")
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    else
      echo "Ignoring @\[main, mp.comm] at $file"
    fi
  fi
  # Handle mpr.comm
  if [[ $attributes =~ \bmpr\.comm\b ]]; then
    IFS='.' read -ra tokens <<< "$module"
    if [[ "${tokens[2]}" == "is" ]]; then
      new_tokens=()
      for t in "${tokens[@]}"; do
        [[ "$t" != "of" ]] && new_tokens+=("$t")
      done
      new_tokens[1]=$(transformPrefix "${new_tokens[1]}")
      new_tokens[2]="of"
      new_tokens[3]=$(transformPrefix "${new_tokens[3]}")
      new_module=$(IFS=. ; echo "${new_tokens[*]}")
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    else
      echo "Ignoring @\[main, mpr.comm] at $file"
    fi
  fi
  # Handle comm.is
  if [[ $attributes =~ \bcomm\.is\b ]]; then
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+?)(\.of\..+)?$ ]]; then
      section="${BASH_REMATCH[1]}"
      given=$(transformPrefix "${BASH_REMATCH[2]}")
      imply=$(transformPrefix "${BASH_REMATCH[3]}")
      arguments="${BASH_REMATCH[4]}"
      new_module="$section.$given.is.$imply$arguments"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    fi
  fi
  # Handle mt attributes
  while [[ $attributes =~ \bmt[[:space:]]*([0-9]*)\b ]]; do
    mt_val="${BASH_REMATCH[1]}"
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.of\.(.+)$ ]]; then
      section="${BASH_REMATCH[1]}"
      imply="${BASH_REMATCH[2]}" # Placeholder, Not operation missing
      given="${BASH_REMATCH[3]}"
      given_array=(${given//./ })
      # Compute index
      if [[ -n "$mt_val" ]]; then
        i=$((${#given_array[@]}-1-$(echo "l($mt_val)/l(2)" | bc -l | awk '{printf("%d\n",$1+0.5)}')))
      else
        i=0
      fi
      if $constructor_order; then
        i=$((${#given_array[@]}-1-$i))
      fi
      new_imply="$imply"  # Not operation placeholder
      arguments=("${given_array[@]}")
      arguments[$i]="$imply"
      new_given=$(IFS=. ; echo "${arguments[*]}")
      new_module="$section.$new_imply.of.$new_given"
      echo "  ('$user', \"$new_module\", '[]', '[]', '[]', '[]', '[]', '[]')," >> "$output_file"
    fi
    # Remove matched mt to avoid infinite loop
    attributes="${attributes/${BASH_REMATCH[0]}/}"
  done
done
sed -i '$ s/,$/\nON DUPLICATE KEY UPDATE imports = VALUES(imports), error = VALUES(error);/' test.sql

echo "plausible:"
sorryModules=($(grep -P "^warning: (\./)*[\w'!₀-₉/]+\.lean:\d+:\d+: declaration uses 'sorry'" test.log | sed -E 's#^warning: ([.]/)*##' | sed -E "s/\.lean:[0-9]+:[0-9]+: declaration uses 'sorry'//" | sed 's#/#.#g' | sort -u))
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
    bash sh/run.sh
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

echo "total lines     = $(find Lemma -type f -name '*.lean' -not -name '*.echo.lean' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}')"

