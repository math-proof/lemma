#!/bin/bash
# Rename a lemma module, the bash counterpart of php/request/rename.php.
#
#   sh/rename.sh [-n] [-u USER] [--no-db] OLD NEW
#
#   OLD / NEW  dotted module names, e.g. Bool.Eq  or  Bool.Eq.Add (slashes and a
#              leading "Lemma." / trailing ".py" are accepted too).
#   -n         dry run: do everything on a scratch copy of Lemma/, print the
#              changes and the SQL, touch neither the repo nor the database.
#   -u USER    value of the `user` column (default: basename of the repo, as get_user()).
#   --no-db    rename the files only, leave the MySQL tables alone.
#
# What it does (same cases as rename.php):
#   * NEW already a package   -> OLD's code is merged into NEW/__init__.py
#   * NEW does not exist      -> OLD.py is moved to NEW.py (parents that are plain files
#                                become packages); a package OLD hands its code to NEW.py
#                                and keeps only its `from . import ...` lines
#   * the parent __init__.py files are updated (removed packages are cleaned up)
#   * tables suggest / axiom / hierarchy / function are updated, and every caller
#     file listed in hierarchy/function gets OLD replaced by NEW.
# Database: database `axiom`, host/password from MYSQL_HOST / MYSQL_PWD (see ~/.bashrc).

set -u -o pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LEMMA="$ROOT/Lemma"
USER_NAME=$(basename "$ROOT")
DB=axiom
DRY=0
USE_DB=1

log() { echo "$*" >&2; }
die() { echo "error: $*" >&2; [ -n "${SCRATCH:-}" ] && rm -rf "$SCRATCH"; exit 1; }

usage() { sed -n '2,22p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    -n|--dry-run) DRY=1 ;;
    --no-db) USE_DB=0 ;;
    -u|--user) shift; USER_NAME=${1:?-u needs a value} ;;
    -h|--help) usage 0 ;;
    --) shift; ARGS+=("$@"); break ;;
    -*) echo "unknown option $1" >&2; usage 1 ;;
    *) ARGS+=("$1") ;;
  esac
  shift
done
[ ${#ARGS[@]} -eq 2 ] || usage 1

normalize() {
  local m=$1
  m=${m//\\//}; m=${m//\//.}
  m=${m#Lemma.}; m=${m%.py}; m=${m%.__init__}
  echo "$m"
}
OLD=$(normalize "${ARGS[0]}")
NEW=$(normalize "${ARGS[1]}")
IDENT='[A-Za-z_][A-Za-z0-9_]*'
for m in "$OLD" "$NEW"; do
  [[ $m =~ ^$IDENT(\.$IDENT)+$ ]] || die "'$m' is not a dotted module name with a package (e.g. Bool.Eq)"
done
[ "$OLD" != "$NEW" ] || die "old and new names are the same"
case "$NEW." in "$OLD."*) [ -d "$LEMMA/${OLD//.//}" ] || true ;; esac

# ---------------------------------------------------------------- database
mysql_run() { # $1 = sql
  local args=(-N -B -D "$DB")
  [ -n "${MYSQL_USER:-}" ] && args+=(-u "$MYSQL_USER")
  [ -n "${MYSQL_HOST:-}" ] && args+=(-h "$MYSQL_HOST")
  mysql "${args[@]}" -e "$1"
}
if [ $USE_DB -eq 1 ] && [ -z "${MYSQL_PWD:-}" ] && [ -f ~/.bash_profile ]; then
  # same trick as sh/run.sh
  source ~/.bash_profile 2>/dev/null || true
fi
sql_write() { # mutating statement
  if [ $DRY -eq 1 ] || [ $USE_DB -eq 0 ]; then echo "SQL> $1"; return 0; fi
  mysql_run "$1" || log "warning: failed: $1"
}
sql_read() { # read-only statement, run even on a dry run
  [ $USE_DB -eq 1 ] || return 0
  mysql_run "$1" 2>/dev/null || true
}

# ------------------------------------------------------------------ dry run
# Lemma/ has tens of thousands of files (and often lives on a slow drive), so a dry
# run does not copy it.  It builds a scratch tree in which the sections involved
# consist of empty placeholder files (enough for the existence checks) and copies the
# real content only of the files whose text matters: OLD, NEW, their ancestors and
# the callers that get rewritten.
SCRATCH=""
STAGED=()
stage_file() { # path relative to Lemma/
  [ $DRY -eq 1 ] || return 0
  [ -f "$REAL_LEMMA/$1" ] || return 0
  [ -s "$LEMMA/$1" ] && return 0
  mkdir -p "$(dirname "$LEMMA/$1")"; cp -p "$REAL_LEMMA/$1" "$LEMMA/$1"; STAGED+=("$1")
}
stage_module() { # a.b.c -> a.py a/__init__.py a/b.py a/b/__init__.py ...
  [ $DRY -eq 1 ] || return 0
  local parts p="" m i; IFS=. read -r -a parts <<< "$1"
  for ((i = 0; i < ${#parts[@]}; i++)); do
    p+="${p:+/}${parts[i]}"; stage_file "$p.py"; stage_file "$p/__init__.py"
  done
}
if [ $DRY -eq 1 ]; then
  SCRATCH=$(mktemp -d)
  REAL_LEMMA=$LEMMA
  LEMMA="$SCRATCH/Lemma"; mkdir -p "$LEMMA"
  log "dry run: scanning sections ${OLD%%.*} ${NEW%%.*} ..."
  for sec in $(printf '%s\n' "${OLD%%.*}" "${NEW%%.*}" | sort -u); do
    [ -d "$REAL_LEMMA/$sec" ] || continue
    (cd "$REAL_LEMMA" && find "$sec" -name __pycache__ -prune -o -type d -print0) | (cd "$LEMMA" && xargs -0 -r mkdir -p)
    (cd "$REAL_LEMMA" && find "$sec" -name __pycache__ -prune -o -type f -print0) | (cd "$LEMMA" && xargs -0 -r touch)
  done
  (cd "$LEMMA" && find . -type f | sort) > "$SCRATCH/before.list"
  stage_module "$OLD"; stage_module "$NEW"
fi

# ---------------------------------------------------------- path helpers
module_to_path() { echo "$LEMMA/${1//.//}"; }
module_to_py() {
  local p; p=$(module_to_path "$1")
  if [ -f "$p.py" ]; then echo "$p.py"; else echo "$p/__init__.py"; fi
}
is_init() { [[ $1 == */__init__.py ]]; }
IMPORT_RE='^from +\. +import +'

# ------------------------------------------------------------ __init__.py
init_has() { # file name -> 0 when some `from . import a, b` line lists name
  [ -f "$1" ] || return 1
  awk -v t="$2" '
    /^from +\. +import +/ {
      s = $0; sub(/^from +\. +import +/, "", s)
      n = split(s, a, /[ \t]*,[ \t]*/)
      for (i = 1; i <= n; i++) { x = a[i]; gsub(/[ \t\r]+$/, "", x); if (x == t) f = 1 }
    }
    END { exit f ? 0 : 1 }' "$1"
}

insert_into_init() { # package name   (no recursion)
  local init; init="$(module_to_path "$1")/__init__.py"
  mkdir -p "$(dirname "$init")"; [ -f "$init" ] || : > "$init"
  init_has "$init" "$2" && return 0
  if [ -s "$init" ] && [ "$(tail -c1 "$init" | wc -l)" -eq 0 ]; then echo >> "$init"; fi
  echo "from . import $2" >> "$init"
}

insert_module_into_init() { # a.b.c -> "from . import c" in a/b, and b in a, ...
  local pkg=${1%.*} name=${1##*.}
  [[ $pkg == *.* ]] && insert_module_into_init "$pkg"
  insert_into_init "$pkg" "$name"
}

replace_in_init() { # package old new
  local init; init="$(module_to_path "$1")/__init__.py"
  [ -f "$init" ] || return 0
  awk -v o="$2" -v n="$3" '
    /^from +\. +import +/ && !done {
      s = $0; sub(/^from +\. +import +/, "", s)
      c = split(s, a, /[ \t]*,[ \t]*/); hit = 0
      for (i = 1; i <= c; i++) { gsub(/[ \t\r]+$/, "", a[i]); if (a[i] == o) { a[i] = n; hit = 1 } }
      if (hit) { out = a[1]; for (i = 2; i <= c; i++) out = out ", " a[i]; print "from . import " out; done = 1; next }
    }
    { print }' "$init" > "$init.tmp" && mv "$init.tmp" "$init"
}

clean_folder() { # remove __pycache__ and the folder itself when it is empty
  find "$1" -depth -name __pycache__ -type d -exec rm -rf {} + 2>/dev/null
  rmdir "$1" 2>/dev/null || log "note: $1 is not empty, left in place"
}

delete_from_init() { # package name
  local pkg=$1 name=$2 folder init removed=0
  folder=$(module_to_path "$pkg"); init="$folder/__init__.py"
  [ -f "$init" ] || return 0
  init_has "$init" "$name" && removed=1
  awk -v t="$name" '
    /^from +\. +import +/ {
      s = $0; sub(/^from +\. +import +/, "", s)
      c = split(s, a, /[ \t]*,[ \t]*/); k = 0; hit = 0
      for (i = 1; i <= c; i++) { gsub(/[ \t\r]+$/, "", a[i]); if (a[i] == t) hit = 1; else keep[++k] = a[i] }
      if (hit) {
        if (k > 0) { out = keep[1]; for (i = 2; i <= k; i++) out = out ", " keep[i]; print "from . import " out }
        delete keep; next
      }
      delete keep
    }
    { print }' "$init" > "$init.tmp" && mv "$init.tmp" "$init"

  # the package lost its last import: drop it, unless real modules remain inside
  [ $removed -eq 1 ] || return 0
  grep -Eq "$IMPORT_RE" "$init" && return 0
  [ -z "$(find "$folder" -name '*.py' ! -path "$init" -print -quit)" ] || return 0
  local code; code=$(grep -Evc '^[[:space:]]*$' "$init" || true)
  if [ "${code:-0}" -gt 0 ]; then
    # the package still holds a theorem of its own: turn it back into a plain module
    if [ -e "$folder.py" ]; then log "note: $folder.py exists, package kept"; return 0; fi
    mv "$init" "$folder.py"; clean_folder "$folder"
  else
    rm -f "$init"; clean_folder "$folder"
    [[ $pkg == *.* ]] && delete_from_init "${pkg%.*}" "${pkg##*.}"
  fi
}

delete_module_from_init() { delete_from_init "${1%.*}" "${1##*.}"; }

# ------------------------------------------------------------ file moves
split_init() { # init-file code-out -> keep only import lines in the file, code lines to code-out
  grep -Ev "^from \. import \w+" "$1" > "$2" || true
  grep -E "^from \. import \w+" "$1" > "$1.tmp" || true
  mv "$1.tmp" "$1"
}

OLD_PY=$(module_to_py "$OLD")
[ -f "$OLD_PY" ] || die "$OLD does not exist ($OLD_PY)"
NEW_FILE="$(module_to_path "$NEW").py"
NEW_INIT="$(module_to_path "$NEW")/__init__.py"

if [ -f "$NEW_FILE" ]; then
  [ ! -s "$NEW_FILE" ] || die "$NEW_FILE already exists"
  rm -f "$NEW_FILE"
fi

TMPCODE=$(mktemp)
trap 'rm -f "$TMPCODE"; [ -n "$SCRATCH" ] && rm -rf "$SCRATCH"' EXIT

if [ -f "$NEW_INIT" ]; then
  # --- NEW is already a package: merge OLD into its __init__.py
  grep -Eq '^@apply\b' "$NEW_INIT" && die "$NEW_INIT already contains an @apply theorem"
  if is_init "$OLD_PY"; then
    log "merging the code of package $OLD into $NEW_INIT"
    split_init "$OLD_PY" "$TMPCODE"
  else
    log "merging $OLD_PY into $NEW_INIT, then deleting it"
    cp "$OLD_PY" "$TMPCODE"
  fi
  { cat "$TMPCODE"; cat "$NEW_INIT"; } > "$NEW_INIT.tmp" && mv "$NEW_INIT.tmp" "$NEW_INIT"
  if ! is_init "$OLD_PY"; then
    rm -f "$OLD_PY"
    delete_module_from_init "$OLD"
  fi
  insert_module_into_init "$NEW"
else
  # --- NEW does not exist yet
  mkdir -p "$(dirname "$NEW_FILE")"
  if is_init "$OLD_PY"; then
    log "moving the code of package $OLD to $NEW_FILE (the package keeps its imports)"
    split_init "$OLD_PY" "$TMPCODE"
    cp "$TMPCODE" "$NEW_FILE"
    insert_module_into_init "$NEW"
  else
    NEW_PARENT=${NEW%.*}
    PARENT_PY=$(module_to_py "$NEW_PARENT")
    if ! is_init "$PARENT_PY"; then
      # the new parent is a plain module: it has to become a package first
      PARENT_INIT="$(module_to_path "$NEW_PARENT")/__init__.py"
      if [ "$(dirname "$PARENT_INIT").py" = "$OLD_PY" ]; then
        # OLD is that very module: its code moves down into the package
        echo "from . import ${NEW##*.}" > "$PARENT_INIT"
      else
        mv "$PARENT_PY" "$PARENT_INIT" || die "failed to turn $PARENT_PY into $PARENT_INIT"
      fi
    fi
    log "renaming $OLD_PY -> $NEW_FILE"
    mv "$OLD_PY" "$NEW_FILE" || die "failed to rename $OLD_PY to $NEW_FILE"
    delete_module_from_init "$OLD"
    insert_module_into_init "$NEW"
  fi
fi

# ------------------------------------------------------- suggest table
delete_from_suggest() {
  local pkg=${1%.*} name=${1##*.}
  sql_write "delete from suggest where user = '$USER_NAME' and prefix = '$pkg.' and phrase = '$name'"
  sql_write "delete from suggest where user = '$USER_NAME' and prefix = '$1.' and phrase = 'apply'"
}
insert_into_suggest() {
  local parts IFS=. i prefix="" rows=""
  read -r -a parts <<< "$1"; parts+=(apply)
  for ((i = 0; i < ${#parts[@]} - 1; i++)); do
    prefix+="${parts[i]}."
    rows+="${rows:+, }('$USER_NAME', '$prefix', '${parts[i+1]}', 1)"
  done
  sql_write "insert ignore into suggest (user, prefix, phrase, \`usage\`) values $rows"
}
delete_from_suggest "$OLD"
insert_into_suggest "$NEW"

# --------------------------------------------- hierarchy / function / axiom
CALLERS=$( { sql_read "select caller from hierarchy where user = '$USER_NAME' and callee = '$OLD'"
             sql_read "select caller from \`function\` where user = '$USER_NAME' and callee = '$OLD'"; } | sort -u)
for caller in $CALLERS; do
  [ "$caller" = "$OLD" ] && caller=$NEW
  stage_module "$caller"
  f=$(module_to_py "$caller")
  if [ ! -f "$f" ]; then log "note: caller $caller has no file ($f)"; continue; fi
  OLD_NAME=$OLD NEW_NAME=$NEW perl -pi -e '
    s/(?<![\w.])\Q$ENV{OLD_NAME}\E(?!\w)(?!\.(?!apply\b))/$ENV{NEW_NAME}/g;
    s/(?<=from Lemma\.)\Q$ENV{OLD_NAME}\E(?= import \w+)/$ENV{NEW_NAME}/g;' "$f"
  log "updated caller $f"
done

sql_write "update axiom set axiom = '$NEW' where user = '$USER_NAME' and axiom = '$OLD'"
for t in hierarchy '`function`'; do
  sql_write "update $t set caller = '$NEW' where user = '$USER_NAME' and caller = '$OLD'"
  sql_write "update $t set callee = '$NEW' where user = '$USER_NAME' and callee = '$OLD'"
done

# --------------------------------------------------------------- report
if [ $DRY -eq 1 ]; then
  echo "== dry run: nothing was written =="
  (cd "$LEMMA" && find . -type f | sort) > "$SCRATCH/after.list"
  printf '%s\n' "${STAGED[@]}" | sed 's#^#./#' | sort > "$SCRATCH/staged.list"
  # files of other sections exist in the scratch tree only because they were staged
  grep -v -F -x -f "$SCRATCH/after.list" "$SCRATCH/before.list" | sed 's#^\./#removed: Lemma/#'
  grep -v -F -x -f "$SCRATCH/before.list" "$SCRATCH/after.list" | grep -v -F -x -f "$SCRATCH/staged.list" | sed 's#^\./#added:   Lemma/#'
  echo "== content changes =="
  for rel in "${STAGED[@]}" $(grep -v -F -x -f "$SCRATCH/before.list" "$SCRATCH/after.list" | grep -v -F -x -f "$SCRATCH/staged.list" | sed 's#^\./##'); do
    if [ -f "$LEMMA/$rel" ]; then
      if [ -f "$REAL_LEMMA/$rel" ]; then diff -u --label "Lemma/$rel" --label "Lemma/$rel" "$REAL_LEMMA/$rel" "$LEMMA/$rel"
      else diff -u --label /dev/null --label "Lemma/$rel (new)" /dev/null "$LEMMA/$rel"; fi
    else
      echo "--- Lemma/$rel (removed or moved away)"
    fi
  done | head -300
else
  echo "renamed $OLD -> $NEW"
fi
