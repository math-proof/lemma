source sh/utility.sh

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
    echo "lemmaNameSrcOrig == lemmaNameDstOrig, no need to rename"
    exit
  fi
fi

# xargs: unmatched single quote; by default quotes are special to xargs unless you use the -0 option
find Lemma sympy -type f -name "*.lean" -not -name "*.echo.lean" -print0 | xargs -0 grep -lZE "open( [[:alnum:]_.]+)* $package_dst\b" | xargs -0 sed -i -E "s/([^.]\b|^)$lemmaNameSrc$submodule/\1$lemmaNameDst\2/g"
