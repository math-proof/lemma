#!/usr/bin/env bash
# Delete a Lemma/*.lean file and drop its axiom.lemma row plus inverted postings.
#
# Usage (from repo root):
#   bash sh/delete.sh Random.Eq.Expect.Foo
#   bash sh/delete.sh Lemma/Random/Eq/Expect/Foo.lean
#
# inverted is keyed by lemma.id, not module name. Look up the id first,
# DELETE FROM inverted WHERE id = ?, then delete the lemma row.
# MySQL failure is a warning, not a hard error: the file is already gone.

source sh/utility.sh

sql_quote() {
  local s=$1
  s=${s//\'/\'\'}
  printf "'%s'" "$s"
}

if [ $# -lt 1 ]; then
  echo "usage: bash sh/delete.sh <module-or-lean-path>" >&2
  exit 2
fi

src=$(normalize "$1")
srcFile=Lemma/${src//.//}.lean
srcEchoFile=${srcFile%.lean}.echo.lean

echo src = "$src"
echo srcFile = "$srcFile"

if [ ! -f "$srcFile" ]; then
  echo "error: $srcFile does not exist"
  exit 1
fi

echo rm "$srcFile"
rm -f "$srcFile"

if [ -f "$srcEchoFile" ]; then
  echo rm "$srcEchoFile"
  rm -f "$srcEchoFile"
fi

delete_axiom_module_row() {
  local module=$1
  local _sh_dir _repo_root host port database
  local candidates cand u p login_user login_pass login_ok
  local module_q out id
  local -a mysql_env mysql_login

  _sh_dir=$(CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]}")" && pwd)
  _repo_root=$(CDPATH= cd -- "$_sh_dir/.." && pwd)

  if command -v node >/dev/null 2>&1 && [ -f "$_repo_root/mjs/leanInvertedIndex.mjs" ]; then
    echo "MySQL axiom.lemma: delete module $module (via node)"
    if (CDPATH= cd -- "$_repo_root" && node mjs/leanInvertedIndex.mjs --delete-module "$module"); then
      return 0
    fi
    echo "warning: node delete of axiom.lemma / inverted failed; trying mysql client" >&2
  fi

  if ! command -v mysql >/dev/null 2>&1; then
    echo "warning: mysql client not found; skipped axiom.lemma / inverted delete" >&2
    return 0
  fi

  host=${MYSQL_HOST:-127.0.0.1}
  port=${MYSQL_PORT:-3306}
  database=axiom

  candidates=()
  if [ -n "${MYSQL_HOST:-}" ] && [ -n "${MYSQL_PWD+x}" ]; then
    candidates+=("${MYSQL_USER:-${USER:-prod}}:${MYSQL_PWD}")
  fi
  candidates+=("prod:prod" "user:user" "")

  login_user= login_pass= login_ok=0
  for cand in "${candidates[@]}"; do
    u=${cand%%:*}
    p=${cand#*:}
    if [ -z "$u" ]; then
      if env -u MYSQL_PWD -u LD_LIBRARY_PATH mysql -h"$host" -P"$port" -D"$database" -N -e "SELECT 1" >/dev/null 2>&1; then
        login_user= login_pass= login_ok=1
        break
      fi
    elif MYSQL_PWD="$p" env -u LD_LIBRARY_PATH mysql -h"$host" -P"$port" -u"$u" -D"$database" -N -e "SELECT 1" >/dev/null 2>&1; then
      login_user=$u
      login_pass=$p
      login_ok=1
      break
    fi
  done

  if [ "$login_ok" -ne 1 ]; then
    echo "warning: could not connect to MySQL ($host/$database); skipped axiom.lemma / inverted delete" >&2
    return 0
  fi

  if [ -n "$login_user" ]; then
    mysql_env=(env -u LD_LIBRARY_PATH MYSQL_PWD="$login_pass")
    mysql_login=(-u"$login_user")
  else
    mysql_env=(env -u MYSQL_PWD -u LD_LIBRARY_PATH)
    mysql_login=()
  fi

  module_q=$(sql_quote "$module")
  echo "MySQL axiom.lemma: delete module $module (login ${login_user:-passwordless}@$host)"

  out=$("${mysql_env[@]}" mysql -h"$host" -P"$port" "${mysql_login[@]}" -D"$database" -N -e "
SELECT id FROM lemma WHERE module = ${module_q};
" 2>&1) || {
    echo "warning: MySQL lemma lookup failed:" >&2
    echo "$out" >&2
    return 0
  }

  id=$(printf '%s\n' "$out" | tr -d '\r' | sed -n '1p')
  if [ -z "$id" ]; then
    echo "MySQL: no axiom.lemma row for module=$module"
    return 0
  fi

  out=$("${mysql_env[@]}" mysql -h"$host" -P"$port" "${mysql_login[@]}" -D"$database" -N -e "
DELETE FROM inverted WHERE id = ${id};
SELECT ROW_COUNT();
DELETE FROM lemma WHERE id = ${id};
SELECT ROW_COUNT();
" 2>&1) || {
    echo "warning: MySQL lemma / inverted delete failed:" >&2
    echo "$out" >&2
    return 0
  }

  local inv_rows lemma_rows
  inv_rows=$(printf '%s\n' "$out" | sed -n '1p')
  lemma_rows=$(printf '%s\n' "$out" | sed -n '2p')
  echo "MySQL rows affected: inverted=$inv_rows lemma=$lemma_rows (id=$id)"
}

delete_axiom_module_row "$src"

