source sh/utility.sh

# ---------------------------------------------------------------------------
# Keep MySQL callee hierarchy in sync with the filesystem rename.
# Same UPDATEs as mjs/lean/renameLemma.mjs → updateAxiomModuleRow.
# Reverse edges on /?callee= come from lemma.imports (JSON), not meta.callee.
# Idempotent: a second pass (or Node calling updateAxiomModuleRow after us)
# affects 0 rows and is not an error.
# ---------------------------------------------------------------------------
sql_quote() {
  # SQL string literal: wrap in '…' and double any embedded single quotes.
  local s=$1
  s=${s//\'/\'\'}
  printf "'%s'" "$s"
}

update_axiom_module_row() {
  local old_mod=$1
  local new_mod=$2
  local project_user host port database
  local candidates cand u p login_user login_pass
  local old_q new_q user_q lemma_old_q lemma_new_q
  local out module_rows import_rows

  if ! command -v mysql >/dev/null 2>&1; then
    echo "warning: mysql client not found; skipped axiom.lemma hierarchy update" >&2
    return 0
  fi

  # Project user = LEAN_PROJECT_USER, else basename of the repo (parent of sh/),
  # matching mjs/run.mjs (`LEAN_PROJECT_USER || path.basename(REPO_ROOT)`).
  _sh_dir=$(CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]}")" && pwd)
  _repo_root=$(CDPATH= cd -- "$_sh_dir/.." && pwd)
  project_user=${LEAN_PROJECT_USER:-$(basename "$_repo_root")}
  host=${MYSQL_HOST:-127.0.0.1}
  port=${MYSQL_PORT:-3306}
  database=axiom

  candidates=()
  if [ -n "${MYSQL_HOST:-}" ] && [ -n "${MYSQL_PWD+x}" ]; then
    candidates+=("${MYSQL_USER:-${USER:-prod}}:${MYSQL_PWD}")
  fi
  candidates+=("prod:prod" "user:user")

  login_user= login_pass=
  for cand in "${candidates[@]}"; do
    u=${cand%%:*}
    p=${cand#*:}
    if MYSQL_PWD="$p" mysql -h"$host" -P"$port" -u"$u" -D"$database" -N -e "SELECT 1" >/dev/null 2>&1; then
      login_user=$u
      login_pass=$p
      break
    fi
  done

  if [ -z "$login_user" ]; then
    echo "warning: could not connect to MySQL ($host/$database); skipped axiom.lemma hierarchy update" >&2
    return 0
  fi

  old_q=$(sql_quote "$old_mod")
  new_q=$(sql_quote "$new_mod")
  user_q=$(sql_quote "$project_user")
  lemma_old_q=$(sql_quote "Lemma.$old_mod")
  lemma_new_q=$(sql_quote "Lemma.$new_mod")

  echo "MySQL axiom.lemma: user=$project_user module $old_mod -> $new_mod (login $login_user@$host)"

  out=$(MYSQL_PWD="$login_pass" mysql -h"$host" -P"$port" -u"$login_user" -D"$database" -N -e "
UPDATE lemma SET module = ${new_q} WHERE user = ${user_q} AND module = ${old_q};
SELECT ROW_COUNT();
UPDATE lemma SET imports = JSON_REPLACE(
  imports,
  JSON_UNQUOTE(JSON_SEARCH(imports, 'one', ${lemma_old_q})),
  ${lemma_new_q}
) WHERE user = ${user_q} AND JSON_CONTAINS(imports, JSON_QUOTE(${lemma_old_q}));
SELECT ROW_COUNT();
" 2>&1) || {
    echo "warning: MySQL hierarchy update failed:" >&2
    echo "$out" >&2
    return 0
  }

  module_rows=$(printf '%s\n' "$out" | sed -n '1p')
  import_rows=$(printf '%s\n' "$out" | sed -n '2p')
  echo "MySQL rows affected: module=$module_rows imports=$import_rows"
}


src=$(normalize $1)
echo src = $src

dst=$(normalize $2)
echo dst = $dst

# Last dotted segment matching @[path] / moduleResolve lowercase suffix → sublemma merge.
# Charset aligned with mjs/lean/moduleResolve.mjs: /^[a-z]+$/
dst_last=${dst##*.}
sublemma=
real_dst=$dst
if [[ "$dst" == *.* && "$dst_last" =~ ^[a-z]+$ ]]; then
  sublemma=$dst_last
  real_dst=${dst%.*}
  echo sublemma = $sublemma
  echo real_dst = $real_dst
fi

srcFile=Lemma/${src//.//}.lean
echo srcFile = $srcFile

dstFile=Lemma/${real_dst//.//}.lean
echo dstFile = $dstFile

if [ ! -f $srcFile ]; then
  echo "error: $srcFile does not exist"
  exit 1
fi

parent_path=$(dirname $dstFile)
echo mkdir -p $parent_path
mkdir -p $parent_path

if [ -n "$sublemma" ]; then
  # Merge source lemma into parent module as private lemma <sublemma> with @[path].
  if ! grep -qE "^private lemma main([[:space:]:]|\$)" "$srcFile" \
    && ! grep -qE "^private lemma ${sublemma}([[:space:]:]|\$)" "$srcFile"; then
    echo "error: $srcFile has no private lemma main (or $sublemma) to merge as sublemma"
    exit 1
  fi
  if [ -f "$dstFile" ] && grep -qE "^private lemma ${sublemma}([[:space:]:]|\$)" "$dstFile"; then
    echo "error: $dstFile already contains private lemma $sublemma"
    exit 1
  fi

  body_file=$(mktemp)
  awk -v name="$sublemma" '
    /^import / { next }
    /^open / { next }
    /^-- created on / { next }
    /^-- updated on / { next }
    {
      line = $0
      if (line ~ /^private lemma main([[:space:]:]|$)/)
        sub(/^private lemma main/, "private lemma " name, line)
      buf[n++] = line
    }
    END {
      start = 0
      while (start < n && buf[start] ~ /^[[:space:]]*$/) start++
      end = n - 1
      while (end >= start && buf[end] ~ /^[[:space:]]*$/) end--
      for (i = start; i <= end; i++) print buf[i]
    }
  ' "$srcFile" > "$body_file"

  today=$(date +%Y-%m-%d)

  if [ -f "$dstFile" ]; then
    echo "merge $srcFile -> $dstFile as private lemma $sublemma"
    merged_file=$(mktemp)
    awk -v body_file="$body_file" -v today="$today" -v srcFile="$srcFile" '
      BEGIN {
        while ((getline line < srcFile) > 0) {
          if (line ~ /^import /) src_imports[++ni] = line
        }
        close(srcFile)
        while ((getline line < body_file) > 0) body[++nb] = line
        close(body_file)
      }
      /^import / {
        imports[++nimp] = $0
        seen_import[$0] = 1
        next
      }
      /^-- created on / {
        flush_body()
        created = $0
        next
      }
      /^-- updated on / {
        flush_body()
        next
      }
      /^[[:space:]]*$/ {
        flush_imports()
        pending_blank++
        next
      }
      {
        flush_imports()
        while (pending_blank > 0) { print ""; pending_blank-- }
        print
      }
      END {
        flush_imports()
        flush_body()
        if (created != "") print created
        else print "-- created on " today
        print "-- updated on " today
      }
      function flush_imports(   i) {
        if (imports_flushed) return
        for (i = 1; i <= nimp; i++) print imports[i]
        for (i = 1; i <= ni; i++) {
          if (!(src_imports[i] in seen_import)) {
            print src_imports[i]
            seen_import[src_imports[i]] = 1
          }
        }
        imports_flushed = 1
      }
      function flush_body(   i) {
        if (body_flushed) return
        flush_imports()
        pending_blank = 0
        if (nb > 0) {
          print ""
          print ""
          for (i = 1; i <= nb; i++) print body[i]
          print ""
        }
        body_flushed = 1
      }
    ' "$dstFile" > "$merged_file"
    mv "$merged_file" "$dstFile"
  else
    echo "create $dstFile from $srcFile as private lemma $sublemma"
    sed -E "s/^private lemma main([[:space:]:]|\$)/private lemma ${sublemma}\\1/" "$srcFile" > "$dstFile"
    if grep -qE '^-- updated on ' "$dstFile"; then
      sed -i -E "s/^-- updated on .*/-- updated on ${today}/" "$dstFile"
    else
      echo "-- updated on ${today}" >> "$dstFile"
    fi
  fi

  rm -f "$body_file"
  echo rm $srcFile
  rm -f "$srcFile"

  # Imports must point at the parent module (no .../reward.lean).
  src_import_pat="Lemma.${src//./\\.}"
  real_import="Lemma.${real_dst}"
  real_import_pat="Lemma.${real_dst//./\\.}"
  echo "rewrite imports $src_import_pat -> $real_import (dedupe)"
  find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -print0 |
    while IFS= read -r -d '' file; do
      if grep -qE "^import ${src_import_pat}\b" "$file"; then
        if grep -qE "^import ${real_import_pat}\b" "$file"; then
          sed -i -E "/^import ${src_import_pat}\b/d" "$file"
        else
          sed -i -E "s/^import ${src_import_pat}\b/import ${real_import}/" "$file"
        fi
      fi
    done
else
  echo mv $srcFile $dstFile
  if [ -f $dstFile ]; then
    echo "error: $dstFile already exists"
    exit 1
  fi

  mv $srcFile $dstFile
fi

srcReg=${src//./\\.}
srcReg="\b$srcReg"
echo srcReg = $srcReg
submodule="((\.[a-z_]+)*(\b[^.]|$))"
echo find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/$srcReg$submodule/$dst\1/g" {} +
find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -exec sed -i -E "s/$srcReg$submodule/$dst\1/g" {} +

package_src=$(echo $src | cut -d'.' -f1)
echo package_src = $package_src

package_dst=$(echo $dst | cut -d'.' -f1)
echo package_dst = $package_dst

lemmaNameSrcOrig=$(echo "$src" | cut -d'.' -f2-)
lemmaNameSrc=${lemmaNameSrcOrig//./\\.}
echo lemmaNameSrc = $lemmaNameSrc

lemmaNameDstOrig=$(echo "$dst" | cut -d'.' -f2-)
lemmaNameDst=${lemmaNameDstOrig//\'/\\\'}
echo lemmaNameDst = $lemmaNameDst

if [ $package_dst != $package_src ]; then
  echo "package_dst != package_src"
  find Lemma -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZP "\b$lemmaNameSrc$submodule" | while IFS= read -r -d $'\0' file; do
    temp_file="${file}.tmp"
    awk -v package_src="$package_src" -v package_dst="$package_dst" '
    $1 == "open" {
      has_package_src = 0
      has_package_dst = 0
      for (i=2; i<=NF; i++) {
        if ($i == package_src)
          has_package_src = 1
        else if ($i == package_dst)
          has_package_dst = 1
      }
      if (has_package_src && !has_package_dst) {
        # Append package_dst to existing modules
        # $0 = $0 " " package_dst
        $(NF+1) = package_dst
      }
    }
    { print }
    ' "$file" > "$temp_file" && mv "$temp_file" "$file"
  done

  if [ $lemmaNameSrcOrig == $lemmaNameDstOrig ]; then
    echo "lemmaNameSrcOrig == lemmaNameDstOrig, no need to rename short names"
  else
    # xargs: unmatched single quote; by default quotes are special to xargs unless you use the -0 option
    find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZE "open( [[:alnum:]_.]+)* $package_dst\b" | xargs -0 sed -i -E "s/([^.]\b|^)$lemmaNameSrc$submodule/\1$lemmaNameDst\2/g"
  fi
else
  # same package: rewrite short names under `open <package>`
  # xargs: unmatched single quote; by default quotes are special to xargs unless you use the -0 option
  find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZE "open( [[:alnum:]_.]+)* $package_dst\b" | xargs -0 sed -i -E "s/([^.]\b|^)$lemmaNameSrc$submodule/\1$lemmaNameDst\2/g"
fi

# Module path on disk / in imports is the real destination (parent module when merging a sublemma).
# Matches Node renameLemma when new_ has no lowercase sublemma suffix; for sublemma merges,
# Lean imports already point at real_dst, so hierarchy must follow real_dst (not the @path suffix).
update_axiom_module_row "$src" "$real_dst"
