# usage :
# bash sh/run.sh
# process only the given module(s)
# bash sh/run.sh -Modules Nat.Mul,Real.LtIntegralS.of.All_Lt
# batch size for `lake setup-file` runs
# bash sh/run.sh -limit 4096
start_time=$(date +%s)
source ./sh/utility.sh

# Split test.lean into batches of this many imports per `lake setup-file` run.
limit=4096
# Process only modules matching one of these patterns (empty = all modules).
MODULES=()
while [ $# -gt 0 ]; do
  case "$1" in
    -Modules|-modules)
      IFS=',' read -ra MODULES <<< "$2"
      shift 2
      ;;
    -limit|-Limit)
      limit="$2"
      shift 2
      ;;
    *)
      shift
      ;;
  esac
done

if [ -z "$LEAN_NUM_THREADS" ]; then
  export LEAN_NUM_THREADS=4
fi

user=$(basename $(dirname $(cd $(dirname $0) && pwd)))
echo "user = $user"

# SQL string-literal list ('v1','v2', ...) with ' doubled; empty when no args.
sql_in_list() {
  local out="" m
  for m in "$@"; do
    m=${m//\'/\'\'}
    out+="${out:+,}'$m'"
  done
  printf '%s' "$out"
}

# Compact JSON array of strings. Import names are validated in echo_import to
# [\w.'] form, so no JSON escaping is ever needed; avoids a jq dependency.
json_array() {
  local out="[" e
  for e in "$@"; do out+="\"$e\","; done
  printf '%s]' "${out%,}"
}

# When `-Modules` is supplied, keep only files whose dotted module name matches.
module_included() {
  local module=$1 m
  if [ ${#MODULES[@]} -eq 0 ]; then return 0; fi
  for m in "${MODULES[@]}"; do
    [[ "$module" == $m ]] && return 0
  done
  return 1
}

# Date comments are always in the last 3 lines of a lemma file.
get_lemma_date_json() {
  local file=$1 created="" updated="" line json
  if [ ! -f "$file" ]; then
    echo "'[]'"
    return
  fi
  while IFS= read -r line; do
    if [[ "$line" =~ ^[[:space:]]*--[[:space:]]*created\ on\ ([0-9]{4}-[0-9]{2}-[0-9]{2})[[:space:]]*$ ]]; then
      created="${BASH_REMATCH[1]}"
    elif [[ "$line" =~ ^[[:space:]]*--[[:space:]]*updated\ on\ ([0-9]{4}-[0-9]{2}-[0-9]{2})[[:space:]]*$ ]]; then
      updated="${BASH_REMATCH[1]}"
    fi
  done < <(tail -n 3 "$file")
  if [ -z "$created" ]; then
    echo "'[]'"
    return
  fi
  # dates are digits and dashes only, so no JSON escaping is needed here
  if [ -n "$updated" ] && [ "$updated" != "$created" ]; then
    json="{\"created\":\"$created\",\"updated\":\"$updated\"}"
  else
    json="{\"created\":\"$created\"}"
  fi
  json=${json//\'/\'\'}
  echo "'$json'"
}

> test.lean

declare -A imports_dict
declare -A syntheticModules
function echo_import {
  file=$1
  lemma=${file%.lean}
  module=${lemma////.}
  if ! module_included "${module#Lemma.}"; then return; fi
  echo "import $module" >> test.lean
  # extract import statements from the lean file
  module=${module#Lemma.}
  mapfile -t lines < <(grep -E '^import[[:space:]]+' $file | sed -E 's/^import[[:space:]]+//; s/\r$//')
  if [ ${#lines[@]} -eq 0 ]; then
    imports_dict[$module]="[]"
  else
    for line in "${lines[@]}"; do
      case "$line" in
        *'"'*|*'\'*|'') echo "ERROR: unexpected import name '$line' in $file" >&2; exit 1;;
      esac
    done
    # compact JSON array, matching what run.ps1 and py/delete_import.py write
    imports_dict[$module]=$(json_array "${lines[@]}")
  fi
}

while read -r file; do
  echo_import "$file"
done < <(find Lemma -type f -name "*.lean" -not -name "*.echo.lean")

> test.log

# Split test.lean into batches of $limit imports and elaborate each with lake
i=0
n=0
: > "test.$i.lean"
while IFS= read -r line; do
  if [ "$n" -ge "$limit" ]; then
    i=$((i + 1))
    n=0
    : > "test.$i.lean"
  fi
  printf '%s\n' "$line" >> "test.$i.lean"
  n=$((n + 1))
done < test.lean
batch_count=$((i + 1))

# Elaborate each batch; drop the last (summary) line of each lake run
j=0
while [ "$j" -lt "$batch_count" ]; do
  if [ "$limit" -eq 1 ]; then
    echo "executing: $(tr '\n' ' ' < "test.$j.lean")"
  fi
  lake setup-file "test.$j.lean" 2>&1 | sed '$d' | tee -a test.log
  j=$((j + 1))
done

sed -i -E "s/^import //" test.lean
imports=$(cat test.lean)
> test.lean

imports=($imports)
echo "modules:"
touch test.sql

output_file=test.sql
echo "INSERT INTO lemma (user, module, imports, open, set_option, preamble, lemma, meta, date) VALUES " > test.sql
for module in ${imports[*]}; do
  # echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [ -z "${imports_dict[$module]}" ]; then
    echo "imports_dict[$module] = " ${imports_dict[$module]}
    continue
  fi
  submodules=${imports_dict[$module]}
  submodules=${submodules//\'/\'\'}
  date_json=$(get_lemma_date_json "Lemma/${module//./\/}.lean")
  echo "  ('$user', \"$module\", '$submodules', '[]', '[]', '[]', '[]', '{\"error\":[]}', $date_json)," >> test.sql
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

NotToken() {
  local token="$1"
  if [[ "$token" == Not* ]]; then
    printf '%s\n' "${token:3}"
  elif [[ "$token" == Eq* ]]; then
    printf '%s\n' "Ne${token:2}"
  elif [[ "$token" == Ne* ]]; then
    printf '%s\n' "Eq${token:2}"
  else
    printf '%s\n' "Not${token}"
  fi
}

# Match Lean `List.Not` / `String.Not`: a lone token flips Eq/Ne/Not,
# while `X.eq.Y` / `X.ne.Y` flip the infix (so `Sub.eq.Zero` → `Sub.ne.Zero`).
Not() {
  local token="$1"
  local -a parts
  IFS='.' read -ra parts <<< "$token"
  if [[ ${#parts[@]} -eq 1 ]]; then
    NotToken "$token"
    return
  fi
  if [[ "${parts[1]}" == "eq" ]]; then
    parts[1]=ne
    local IFS='.'
    printf '%s\n' "${parts[*]}"
    return
  fi
  if [[ "${parts[1]}" == "ne" ]]; then
    parts[1]=eq
    local IFS='.'
    printf '%s\n' "${parts[*]}"
    return
  fi
  if [[ "${parts[1]}" == "ou" ]]; then
    local left right
    left=$(Not "${parts[0]}")
    if [[ ${#parts[@]} -gt 2 ]]; then
      local IFS='.'
      right=$(Not "${parts[*]:2}")
      printf '%s\n' "${left}.${right}"
    else
      printf '%s\n' "$left"
    fi
    return
  fi
  NotToken "$token"
}

emit_synthetic() {
  # Record synthetic dual rows so the orphan DELETE and the
  # deleted-module detection below do not treat them as gone.
  syntheticModules[$1]=1
  echo "  ('$user', \"$1\", '[]', '[]', '[]', '[]', '[]', '{\"error\":[]}', '[]')," >> test.sql
}

# Mirror List.andLeftTokens / List.andRightTokens / Name.andProjName from sympy/Basic.lean:
# Section.Type1.Type2.of.Givens -> Section.Type1.of.Givens (left) or Section.Type2.of.Givens (right);
# when Type1 = Type2, append .fst / .snd.
and_proj_module() {
  local module=$1 left=$2
  local -a tokens pre rest leftTokens rightTokens
  IFS='.' read -ra tokens <<< "$module"
  local ofIdx=-1 i
  for i in "${!tokens[@]}"; do
    if [[ "${tokens[$i]}" == "of" ]]; then ofIdx=$i; break; fi
  done
  if [ "$ofIdx" -lt 2 ]; then return 1; fi
  pre=("${tokens[@]:0:$ofIdx}")
  rest=("${tokens[@]:$ofIdx}")
  if [ "${#pre[@]}" -lt 3 ]; then return 1; fi
  leftTokens=("${pre[@]:0:$((${#pre[@]} - 1))}" "${rest[@]}")
  rightTokens=("${pre[@]:0:$((${#pre[@]} - 2))}" "${pre[@]:$((${#pre[@]} - 1))}" "${rest[@]}")
  local IFS=.
  local leftModule="${leftTokens[*]}" rightModule="${rightTokens[*]}"
  if [ "$leftModule" == "$rightModule" ]; then
    if [ "$left" == "true" ]; then
      echo "${leftModule}.fst"
    else
      echo "${rightModule}.snd"
    fi
  elif [ "$left" == "true" ]; then
    echo "$leftModule"
  else
    echo "$rightModule"
  fi
}

# Replace the first `Iff` occurrence inside the first token that has one.
replace_iff_token() {
  local module=$1 replacement=$2
  local -a tokens
  IFS='.' read -ra tokens <<< "$module"
  local i tok prefix
  for i in "${!tokens[@]}"; do
    tok="${tokens[$i]}"
    prefix="${tok%%Iff*}"
    if [ "$prefix" != "$tok" ]; then
      tokens[$i]="${tok:0:${#prefix}}${replacement}${tok:$((${#prefix} + 3))}"
      local IFS=.
      printf '%s\n' "${tokens[*]}"
      return 0
    fi
  done
  return 1
}

# Sets _section _lhs _rhs _of_suffix _of_args for `Section.LHS.is.RHS[.of.Args]`.
parse_is_module() {
  local module="$1"
  if [[ ! "$module" =~ ^([a-zA-Z0-9_]+)\.(.+)\.is\.(.+)$ ]]; then
    return 1
  fi
  _section="${BASH_REMATCH[1]}"
  _lhs="${BASH_REMATCH[2]}"
  local rest="${BASH_REMATCH[3]}"
  if [[ "$rest" == *".of."* ]]; then
    _rhs="${rest%%.of.*}"
    _of_args=".of.${rest#*.of.}"
    _of_suffix=".${rest#*.of.}"
  else
    _rhs="$rest"
    _of_args=""
    _of_suffix=""
  fi
  return 0
}

# Swap the two sides of `is` (`List.comm` / `commutateIs`).
comm_swap_is() {
  local module="$1"
  local -a tokens rest first afterIs new_tokens prefix ofPart restIs
  IFS='.' read -ra tokens <<< "$module"
  local ofIdx=-1 isIdx=-1 i
  for i in "${!tokens[@]}"; do
    if [[ "${tokens[$i]}" == "of" ]]; then
      ofIdx=$i
      break
    fi
  done
  if [[ $ofIdx -lt 0 ]]; then
    rest=("${tokens[@]:1}")
    for i in "${!rest[@]}"; do
      if [[ "${rest[$i]}" == "is" ]]; then
        isIdx=$i
        break
      fi
    done
    if [[ $isIdx -gt 0 ]]; then
      first=("${rest[@]:0:$isIdx}")
    else
      first=()
    fi
    if [[ $isIdx -ge 0 && $((isIdx + 1)) -lt ${#rest[@]} ]]; then
      afterIs=("${rest[@]:$((isIdx + 1))}")
    else
      afterIs=()
    fi
    new_tokens=("${tokens[0]}" "${afterIs[@]}" is "${first[@]}")
  else
    prefix=("${tokens[@]:0:$ofIdx}")
    ofPart=("${tokens[@]:$ofIdx}")
    restIs=("${prefix[@]:1}")
    for i in "${!restIs[@]}"; do
      if [[ "${restIs[$i]}" == "is" ]]; then
        isIdx=$i
        break
      fi
    done
    if [[ $isIdx -gt 0 ]]; then
      first=("${restIs[@]:0:$isIdx}")
    else
      first=()
    fi
    if [[ $isIdx -ge 0 && $((isIdx + 1)) -lt ${#restIs[@]} ]]; then
      afterIs=("${restIs[@]:$((isIdx + 1))}")
    else
      afterIs=()
    fi
    new_tokens=("${prefix[0]}" "${afterIs[@]}" is "${first[@]}" "${ofPart[@]}")
  fi
  local IFS='.'
  printf '%s\n' "${new_tokens[*]}"
}

# Find all .lean files except *.echo.lean under Lemma/
while read -r file; do
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
  if ! module_included "$module"; then continue; fi
  constructor_order=false
  if [[ $constructor_comment == *"constructor order"* ]]; then
    constructor_order=true
  fi
  # Handle comm attribute (`comm` / `comm N`, not `comm.is` / `mp.comm`)
  re_comm='(^|,[[:space:]]*)comm([[:space:]]+([0-9]+))?(,|$)'
  if [[ $attributes =~ $re_comm ]]; then
    deBruijn="${BASH_REMATCH[3]}"
    IFS='.' read -ra tokens <<< "$module"
    found=false
    has_is=false
    for t in "${tokens[@]:1}"; do
      if [[ "$t" == "is" ]]; then
        has_is=true
        break
      fi
    done
    # `A.eq.B.is.C` has tokens[2] = eq, but comm still swaps around `is`.
    if $has_is; then
      found=true
      if [[ -z "$deBruijn" ]]; then
        new_module=$(comm_swap_is "$module")
      elif [[ "${tokens[2]}" == "is" ]]; then
        tmp="${tokens[1]}"
        tokens[1]="${tokens[3]}"
        tokens[3]="$tmp"
        new_module=$(IFS=. ; echo "${tokens[*]}")
      else
        new_module=$(comm_swap_is "$module")
      fi
    else
      case "${tokens[2]}" in
        eq|as|ne|lt|le|gt|ge)
          found=true
          tmp="${tokens[1]}"
          tokens[1]="${tokens[3]}"
          tokens[3]="$tmp"
          new_module=$(IFS=. ; echo "${tokens[*]}")
          ;;
        *)
          ofIdx=-1
          for i in "${!tokens[@]}"; do
            if [[ "${tokens[$i]}" == "of" ]]; then ofIdx=$i; break; fi
          done
          deBruijn=${deBruijn:-0}
          if [ "$ofIdx" -ge 0 ] && [ "$ofIdx" -lt $((${#tokens[@]} - 1)) ]; then
            # flip the first popCount(deBruijn) tokens after `of`
            ofTokens=("${tokens[@]:$((ofIdx + 1))}")
            d=$deBruijn
            popCount=0
            while [ "$d" -gt 0 ]; do
              if (( d & 1 )); then popCount=$((popCount + 1)); fi
              d=$(( d >> 1 ))
            done
            flipCount=$popCount
            if [ "$flipCount" -gt "${#ofTokens[@]}" ]; then flipCount=${#ofTokens[@]}; fi
            for (( k = 0; k < flipCount; k++ )); do
              newTok=$(transformPrefix "${ofTokens[$k]}")
              if [ "$newTok" != "${ofTokens[$k]}" ]; then
                found=true
                ofTokens[$k]="$newTok"
              fi
            done
            for (( k = 0; k < ${#ofTokens[@]}; k++ )); do
              tokens[$((ofIdx + 1 + k))]="${ofTokens[$k]}"
            done
          else
            index=$((${#tokens[@]} - 1))
            increment=-1
            while [ "$deBruijn" -gt 0 ]; do
              if (( deBruijn & 1 )); then
                found=true
                tokens[$index]=$(transformPrefix "${tokens[$index]}")
              fi
              deBruijn=$(( deBruijn >> 1 ))
              index=$(( index + increment ))
            done
          fi
          first=$(transformPrefix "${tokens[1]}")
          if [[ "${tokens[1]}" != "$first" ]]; then
            found=true
            tokens[1]="$first"
          fi
          new_module=$(IFS=. ; echo "${tokens[*]}")
          ;;
      esac
    fi
    if $found; then
      emit_synthetic "$new_module"
    fi
  fi
  # Handle mp attribute
  re_mp='(^|,[[:space:]]+)mp(,|$)'
  if [[ $attributes =~ $re_mp ]]; then
    if parse_is_module "$module"; then
      emit_synthetic "${_section}.${_rhs}.of.${_lhs}${_of_suffix}"
    elif new_module=$(replace_iff_token "$module" "Imp_"); then
      emit_synthetic "$new_module"
    fi
  fi
  # Handle mpr attribute
  re_mpr='(^|,[[:space:]]+)mpr(,|$)'
  if [[ $attributes =~ $re_mpr ]]; then
    if parse_is_module "$module"; then
      emit_synthetic "${_section}.${_lhs}.of.${_rhs}${_of_suffix}"
    elif new_module=$(replace_iff_token "$module" "Imp"); then
      emit_synthetic "$new_module"
    fi
  fi
  # Handle mp.left: apply `mp` (commutateIs "of") then And.left projection.
  if [[ $attributes == *mp.left* ]]; then
    IFS='.' read -ra tokens <<< "$module"
    rest=("${tokens[@]:1}")
    isIdx=-1
    for i in "${!rest[@]}"; do
      if [[ "${rest[$i]}" == "is" ]]; then isIdx=$i; break; fi
    done
    if [ "$isIdx" -ge 0 ]; then
      first=()
      if [ "$isIdx" -gt 0 ]; then first=("${rest[@]:0:$isIdx}"); fi
      afterIs=()
      if [ $((isIdx + 1)) -lt ${#rest[@]} ]; then afterIs=("${rest[@]:$((isIdx + 1))}"); fi
      # commutateIs "of": section + afterIs + "of" + first
      mpTokens=("${tokens[0]}" "${afterIs[@]}" of "${first[@]}")
      mpModule=$(IFS=. ; echo "${mpTokens[*]}")
      if new_module=$(and_proj_module "$mpModule" true); then
        emit_synthetic "$new_module"
      else
        echo "Ignoring @[main, mp.left] at $file"
      fi
    else
      printf 'Ignoring @[main, mp.left] at %s (no `is` segment)\n' "$file"
    fi
  fi
  # Handle mp.right: apply `mp` (commutateIs "of") then And.right projection.
  if [[ $attributes == *mp.right* ]]; then
    IFS='.' read -ra tokens <<< "$module"
    rest=("${tokens[@]:1}")
    isIdx=-1
    for i in "${!rest[@]}"; do
      if [[ "${rest[$i]}" == "is" ]]; then isIdx=$i; break; fi
    done
    if [ "$isIdx" -ge 0 ]; then
      first=()
      if [ "$isIdx" -gt 0 ]; then first=("${rest[@]:0:$isIdx}"); fi
      afterIs=()
      if [ $((isIdx + 1)) -lt ${#rest[@]} ]; then afterIs=("${rest[@]:$((isIdx + 1))}"); fi
      # commutateIs "of": section + afterIs + "of" + first
      mpTokens=("${tokens[0]}" "${afterIs[@]}" of "${first[@]}")
      mpModule=$(IFS=. ; echo "${mpTokens[*]}")
      if new_module=$(and_proj_module "$mpModule" false); then
        emit_synthetic "$new_module"
      else
        echo "Ignoring @[main, mp.right] at $file"
      fi
    else
      printf 'Ignoring @[main, mp.right] at %s (no `is` segment)\n' "$file"
    fi
  fi
  # Handle mp.comm
  if [[ $attributes == *mp.comm* ]]; then
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
      emit_synthetic "$new_module"
    else
      echo "Ignoring @\[main, mp.comm] at $file"
    fi
  fi
  # Handle mpr.comm
  if [[ $attributes == *mpr.comm* ]]; then
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
      emit_synthetic "$new_module"
    else
      echo "Ignoring @\[main, mpr.comm] at $file"
    fi
  fi
  # Handle mp.mt
  if [[ $attributes == *mp.mt* ]]; then
    if parse_is_module "$module"; then
      emit_synthetic "${_section}.$(Not "$_lhs").of.$(Not "$_rhs")${_of_suffix}"
    fi
  fi
  # Handle mpr.mt
  if [[ $attributes == *mpr.mt* ]]; then
    if parse_is_module "$module"; then
      emit_synthetic "${_section}.$(Not "$_rhs").of.$(Not "$_lhs")${_of_suffix}"
    fi
  fi
  # Handle is.mt
  if [[ $attributes == *is.mt* ]]; then
    if parse_is_module "$module"; then
      emit_synthetic "${_section}.$(Not "$_lhs").is.$(Not "$_rhs")${_of_args}"
    fi
  fi
  # Handle comm.is
  if [[ $attributes == *comm.is* ]]; then
    if parse_is_module "$module"; then
      given=$(transformPrefix "$_lhs")
      imply=$(transformPrefix "$_rhs")
      emit_synthetic "${_section}.${given}.is.${imply}${_of_args}"
    fi
  fi
  # Handle is.comm
  if [[ $attributes == *is.comm* ]]; then
    if parse_is_module "$module"; then
      given=$(transformPrefix "$_lhs")
      imply=$(transformPrefix "$_rhs")
      emit_synthetic "${_section}.${imply}.is.${given}${_of_args}"
    fi
  fi
  # Handle mt attributes (not `mp.mt` / `mpr.mt`)
  attr_mt="${attributes//mp.mt/}"
  attr_mt="${attr_mt//mpr.mt/}"
  re_mt='(^|[^[:alnum:].])mt([[:space:]]+([0-9]+))?([^[:alnum:]]|$)'
  while [[ $attr_mt =~ $re_mt ]]; do
    mt_val="${BASH_REMATCH[3]}"
    if [[ $module =~ ^([a-zA-Z0-9_]+)\.(.+)\.of\.(.+)$ ]]; then
      section="${BASH_REMATCH[1]}"
      imply=$(Not "${BASH_REMATCH[2]}")
      given="${BASH_REMATCH[3]}"
      IFS='.' read -ra given_array <<< "$given"
      if [[ -n "$mt_val" ]]; then
        # floor(log2(mt_val)), matching BitOperations.Log2 in run.ps1
        l2=0
        v=$mt_val
        while [ "$v" -gt 1 ]; do l2=$((l2 + 1)); v=$((v >> 1)); done
        i=$((${#given_array[@]} - 1 - l2))
      else
        i=0
      fi
      if $constructor_order; then
        i=$((${#given_array[@]}-1-$i))
      fi
      new_imply=$(Not "${given_array[$i]}")
      arguments=("${given_array[@]}")
      arguments[$i]="$imply"
      new_given=$(IFS=. ; echo "${arguments[*]}")
      emit_synthetic "$section.$new_imply.of.$new_given"
    fi
    attr_mt="${attr_mt/${BASH_REMATCH[0]}/}"
  done
  # Handle subst N
  attr_subst="$attributes"
  re_subst='subst[[:space:]]+([0-9]+)'
  while [[ $attr_subst =~ $re_subst ]]; do
    b="${BASH_REMATCH[1]}"
    if [[ "$module" == *".of."* ]]; then
      emit_synthetic "${module}.Eq_${b}"
    else
      emit_synthetic "${module}.of.Eq_${b}"
    fi
    attr_subst="${attr_subst/${BASH_REMATCH[0]}/}"
  done
  # Handle And.left / And.right projections
  if [[ $attributes == *And.left* ]]; then
    if new_module=$(and_proj_module "$module" true); then
      emit_synthetic "$new_module"
    else
      echo "Ignoring @[main, And.left] at $file"
    fi
  fi
  if [[ $attributes == *And.right* ]]; then
    if new_module=$(and_proj_module "$module" false); then
      emit_synthetic "$new_module"
    else
      echo "Ignoring @[main, And.right] at $file"
    fi
  fi
done < <(find Lemma -type f -name "*.lean" ! -name "*.echo.lean")
sed -i '$ s/,$/\nON DUPLICATE KEY UPDATE imports = VALUES(imports), date = VALUES(date);/' test.sql

# Clear error for all disk modules (preserves meta.callee via JSON_SET)
diskModuleList=$(sql_in_list "${!imports_dict[@]}")
if [ -n "$diskModuleList" ]; then
  echo "UPDATE lemma SET meta = JSON_SET(IFNULL(meta, '{}'), '\$.error', CAST('[]' AS JSON)) WHERE user = '$user' AND module IN ($diskModuleList);" >> test.sql
fi

echo "plausible:"

sorryModules=($(grep -P "^warning: (\./)*[\w'!₀-₉/]+\.lean:\d+:\d+: declaration uses 'sorry'" test.log | sed -E 's#^warning: ([.]/)*##' | sed -E "s/\.lean:[0-9]+:[0-9]+: declaration uses 'sorry'//" | sed 's#/#.#g' | sort -u))
for module in ${sorryModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [[ $module =~ ^sympy ]]; then
    continue
  fi
  cat >> test.sql << EOF
UPDATE lemma set meta = JSON_SET(IFNULL(meta, '{}'), '\$.error', CAST('[{"code": "", "file": "", "info": "declaration uses ''sorry''", "line": 0, "type": "warning"}]' AS JSON)) where user = '$user' and module = "$module";
EOF
done

echo "failed:"

failingModules=($(awk '/Some required (targets|builds) logged failures:/{flag=1;next}/^[^-]/{flag=0}flag' test.log | sed 's/^- //'))
for module in ${failingModules[*]}; do
  echo "${module//.//}.lean"
  module=${module#Lemma.}
  if [[ $module =~ ^sympy ]]; then
    continue
  fi
  cat >> test.sql << EOF
UPDATE lemma set meta = JSON_SET(IFNULL(meta, '{}'), '\$.error', CAST('[{"code": "", "file": "", "info": "", "line": 0, "type": "error"}]' AS JSON)) where user = '$user' and module = "$module";
EOF
done

MYSQL_PORT=${MYSQL_PORT:-3306}
# Create a temporary config file with .cnf extension
tempConfigPath=$(mktemp)
mv "$tempConfigPath" "${tempConfigPath}.cnf"
tempConfigPath="${tempConfigPath}.cnf"
cat > "$tempConfigPath" << EOF
[client]
password = $MYSQL_PWD
port = $MYSQL_PORT
default-character-set = utf8mb4
EOF

# Query existing modules and imports for change detection
declare -A dbImports
while IFS=$'\t' read -r mod imps; do
  case "$mod" in ""|ERROR*) continue ;; esac
  [ -n "$imps" ] || continue  # skip mysql warnings and other non-tab lines
  dbImports[$mod]="$imps"
done < <(mysql --defaults-extra-file="$tempConfigPath" --batch --skip-column-names -D axiom -e "SELECT module, imports FROM lemma WHERE user = '$user'" 2>&1 | tee test.log)

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

# Delete orphan modules (in DB but no longer on disk).
# Skipped for -Modules runs: imports_dict only holds the filtered subset, so
# everything outside the filter would look like an orphan. Synthetic dual rows
# are kept explicitly — they are regenerated above but are not in imports_dict.
if [ ${#MODULES[@]} -eq 0 ]; then
  keepList=$(sql_in_list "${!imports_dict[@]}" "${!syntheticModules[@]}")
  if [ -n "$keepList" ]; then
    # piped via stdin: with thousands of modules the IN list overflows the
    # per-argument execve limit (~128KB) when passed with -e
    echo "DELETE FROM lemma WHERE user = '$user' AND module NOT IN ($keepList)" | mysql --defaults-extra-file="$tempConfigPath" -D axiom 2>&1 | tee test.log
  fi
else
  echo "-Modules set: skipping orphan delete"
fi

# Detect changes: deleted, new, and modified-imports modules
declare -A invalidate
for m in "${!dbImports[@]}"; do
  [ -n "${syntheticModules[$m]}" ] && continue      # dual row, still generated above
  if [ ${#MODULES[@]} -gt 0 ] && ! module_included "$m"; then continue; fi  # outside -Modules scope
  [ -z "${imports_dict[$m]+x}" ] && invalidate[$m]=1  # deleted
done
for m in "${!imports_dict[@]}"; do
  if [ -z "${dbImports[$m]+x}" ]; then
    invalidate[$m]=1  # new
  else
    diskImports=${imports_dict[$m]//[[:space:]]/}
    oldImports=${dbImports[$m]//[[:space:]]/}
    [ "$diskImports" != "$oldImports" ] && invalidate[$m]=1  # modified
  fi
done

# Invalidate meta.callee for affected modules and ALL their transitive callers.
# Direct importer lists are built once from the normalized (unprefixed) import
# sets, then walked outward — the same fixpoint run.ps1 computes, without
# re-scanning the whole graph once per layer.
declare -A callers
for m in "${!imports_dict[@]}"; do
  s=${imports_dict[$m]}
  s=${s:1:${#s}-2}  # strip [ ]
  [ -n "$s" ] || continue
  IFS=',' read -ra elems <<< "$s"
  for e in "${elems[@]}"; do
    imp=${e:1:${#e}-2}  # strip surrounding quotes
    callers[${imp#Lemma.}]+="$m"$'\n'
  done
done

queue=("${!invalidate[@]}")
qi=0
while [ "$qi" -lt "${#queue[@]}" ]; do
  a=${queue[$qi]}
  qi=$((qi + 1))
  while IFS= read -r m; do
    [ -n "$m" ] || continue
    if [ -z "${invalidate[$m]+x}" ]; then
      invalidate[$m]=1
      queue+=("$m")
    fi
  done <<< "${callers[$a]:-}"
done

if [ ${#invalidate[@]} -gt 0 ]; then
  invalidateList=$(sql_in_list "${!invalidate[@]}")
  # piped via stdin: the IN list can exceed the per-argument execve limit
  echo "UPDATE lemma SET meta = JSON_SET(IFNULL(meta, '{}'), '\$.callee', CAST('null' AS JSON)) WHERE user = '$user' AND module IN ($invalidateList)" | mysql --defaults-extra-file="$tempConfigPath" -D axiom 2>&1 | tee test.log
  echo "invalidated meta.callee for ${#invalidate[@]} module(s)"
fi
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
rm -f "$tempConfigPath"

echo "total lines     = $(find Lemma -type f -name '*.lean' -not -name '*.echo.lean' -exec awk 'END{print NR}' {} + 2>/dev/null | awk '{s+=$1} END{print s}')"
