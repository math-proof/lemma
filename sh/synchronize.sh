#!/usr/bin/env bash
# ensure the remote git repo is up to date before sync:
# ssh "${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}" "git -C github/lean pull"
# ssh "${env:REMOTE_MYSQL_USER}@${env:REMOTE_MYSQL_HOST}" "git -C github/py pull"
# Scoped upsert of lemma rows from the local MySQL (axiom.lemma) to the remote server.
#
# usage:
#   bash sh/synchronize.sh Real.Eq_0.Lim.of.LtAbs.IsFinite Lemma/Tensor/Eq/Foo/of/Bar.lean ...
#   bash sh/synchronize.sh -n <modules...>     # dry run: only report what would change
#
# - modules: dotted names or Lemma/....lean paths (*.echo.lean is rejected)
# - only rows with user = $LEAN_PROJECT_USER (default: name of the repo directory, as in sh/run.sh)
#   and the given modules are sent, as INSERT ... ON DUPLICATE KEY UPDATE inside one transaction.
#   Nothing is deleted, dropped, truncated or copied as a file (unlike ps1/synchronize.ps1).
# - after the push the row checksums (MD5 over all non-key columns, and over `lemma`) of the
#   remote rows are compared with the local ones; the exit status is 1 on any mismatch.
#
# environment (never printed, never hardcoded):
#   REMOTE_MYSQL_USER  ssh user and MySQL user on the remote host
#   REMOTE_MYSQL_PWD   MySQL password of that user on the remote host
#   REMOTE_MYSQL_HOST  remote host
#   REMOTE_MYSQL_PORT  remote MySQL port (default 3306)
#   If one is unset and powershell.exe is reachable (WSL), it is read from the Windows environment.
#   Local MySQL: MYSQL_HOST (127.0.0.1), MYSQL_PORT (3306), LOCAL_MYSQL_USER (prod), MYSQL_PWD.
#   SSH_OPTS: extra ssh options (default: -o BatchMode=yes, so ssh never prompts).
#   SSH_CMD: ssh executable (default: ssh; in WSL use SSH_CMD=ssh.exe to reuse the Windows keys/known_hosts).
set -u
cd "$(dirname "$0")/.." || exit 1

usage() { sed -n '2,23p' "$0" | sed 's/^# \{0,1\}//'; }

DRY=0
RAW=()
while [ $# -gt 0 ]; do
  case "$1" in
    -n|--dry-run) DRY=1 ;;
    -h|--help) usage; exit 0 ;;
    *) RAW+=("$1") ;;
  esac
  shift
done
if [ ${#RAW[@]} -eq 0 ]; then usage >&2; exit 2; fi

user=${LEAN_PROJECT_USER:-$(basename "$(pwd)")}

# ---- modules -------------------------------------------------------------
declare -A seen
MODULES=()
for m in "${RAW[@]}"; do
  m=${m//\\//}
  m=${m%.lean}
  case "$m" in *.echo) echo "ERROR: skip echo sidecar: $m" >&2; exit 2 ;; esac
  if [[ "$m" == *Lemma/* ]]; then m=${m#*Lemma/}; fi
  m=${m#./}
  m=${m//\//.}
  if [[ -z "$m" || "$m" =~ [[:space:]\"\\\;\`] ]]; then echo "ERROR: bad module name: $m" >&2; exit 2; fi
  if [ -z "${seen[$m]+x}" ]; then seen[$m]=1; MODULES+=("$m"); fi
done
in_list=""
for m in "${MODULES[@]}"; do in_list+="${in_list:+,}'${m//\'/\'\'}'"; done   # ' occurs in names like RotaryMatrix'

# ---- credentials ---------------------------------------------------------
env_or_ps() {
  local v=${!1:-}
  if [ -z "$v" ] && command -v powershell.exe >/dev/null 2>&1; then
    v=$(powershell.exe -NoProfile -Command "[Environment]::GetEnvironmentVariable('$1')" 2>/dev/null | tr -d '\r\n')
  fi
  printf '%s' "$v"
}
R_USER=$(env_or_ps REMOTE_MYSQL_USER)
R_PWD=$(env_or_ps REMOTE_MYSQL_PWD)
R_HOST=$(env_or_ps REMOTE_MYSQL_HOST)
R_PORT=$(env_or_ps REMOTE_MYSQL_PORT); R_PORT=${R_PORT:-3306}
for v in R_USER R_PWD R_HOST; do
  if [ -z "${!v}" ]; then echo "ERROR: REMOTE_MYSQL_${v#R_} is not set" >&2; exit 2; fi
done
if [[ "$R_USER$R_HOST$R_PORT" =~ [[:space:]\'\"\\\;\`\$\&\|\<\>\(\)] ]]; then echo "ERROR: unsafe characters in remote user/host/port" >&2; exit 2; fi
SSH_OPTS=${SSH_OPTS:--o BatchMode=yes}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
chmod 700 "$tmp"

# ---- local mysql ---------------------------------------------------------
{
  echo "[client]"
  echo "host=${MYSQL_HOST:-127.0.0.1}"
  echo "port=${MYSQL_PORT:-3306}"
  echo "user=${LOCAL_MYSQL_USER:-prod}"
  [ -n "${MYSQL_PWD:-}" ] && printf 'password="%s"\n' "$(printf '%s' "$MYSQL_PWD" | sed 's/[\\"]/\\&/g')"
  echo "default-character-set=utf8mb4"
} > "$tmp/local.cnf"
local_mysql() { env -u MYSQL_PWD mysql --defaults-extra-file="$tmp/local.cnf" -D axiom "$@"; }

# ---- remote mysql (script and password travel through ssh's encrypted stdin) -------
remote_mysql() {   # SQL on stdin, mysql flags as arguments
  local sql d1 d2 pw
  sql=$(cat)
  d1="EOF_CNF_$RANDOM$RANDOM"; d2="EOF_SQL_$RANDOM$RANDOM"
  pw=$(printf '%s' "$R_PWD" | sed 's/[\\"]/\\&/g')
  {
    echo "umask 077; cnf=\$(mktemp) || exit 1; trap 'rm -f \"\$cnf\"' EXIT"
    echo "cat > \"\$cnf\" <<'$d1'"
    printf '[client]\nuser=%s\npassword="%s"\nport=%s\ndefault-character-set=utf8mb4\n' "$R_USER" "$pw" "$R_PORT"
    echo "$d1"
    echo "M=/usr/local/mysql/bin/mysql; [ -x \"\$M\" ] || M=mysql"
    echo "\"\$M\" --defaults-extra-file=\"\$cnf\" -D axiom $* <<'$d2'"
    printf '%s\n' "$sql"
    echo "$d2"
  } | ${SSH_CMD:-ssh} $SSH_OPTS "$R_USER@$R_HOST" bash -s
}

cols="CAST(imports AS CHAR), CAST(\`open\` AS CHAR), IFNULL(CAST(set_option AS CHAR),'<NULL>'), CAST(preamble AS CHAR), CAST(lemma AS CHAR), IFNULL(CAST(meta AS CHAR),'<NULL>'), CAST(\`date\` AS CHAR)"
checksum_sql="SELECT '#count', CAST(COUNT(*) AS CHAR), '' FROM lemma
UNION ALL SELECT module, MD5(CONCAT_WS('#', $cols)), MD5(CAST(lemma AS CHAR)) FROM lemma WHERE user = '$user' AND module IN ($in_list);"

declare -A L_ROW L_LEM R_ROW R_LEM RB_ROW
fill() {  # name-prefix, count-var ; reads tab-separated lines on stdin
  local pfx=$1 cvar=$2 mod row lem
  while IFS=$'\t' read -r mod row lem; do
    [ -n "$mod" ] || continue
    if [ "$mod" == "#count" ]; then printf -v "$cvar" '%s' "$row"; continue; fi
    case "$pfx" in
      L) L_ROW[$mod]=$row; L_LEM[$mod]=$lem ;;
      B) RB_ROW[$mod]=$row ;;
      R) R_ROW[$mod]=$row; R_LEM[$mod]=$lem ;;
    esac
  done
}

echo "user = $user, ${#MODULES[@]} module(s), remote = $R_USER@$R_HOST (mysql port $R_PORT)"

# 1. local checksums, must all exist
L_COUNT=""
fill L L_COUNT < <(printf '%s\n' "$checksum_sql" | local_mysql -N -B --raw)
missing=0
for m in "${MODULES[@]}"; do
  if [ -z "${L_ROW[$m]+x}" ]; then echo "ERROR: no local row for user=$user module=$m (run: node mjs/run.mjs $m)" >&2; missing=1; fi
done
[ $missing -eq 0 ] || exit 1

# 2. remote state before
RB_COUNT=""
out=$(printf '%s\n' "$checksum_sql" | remote_mysql -s -N -B) || { echo "ERROR: remote query failed (ssh/mysql/auth)" >&2; exit 1; }
fill B RB_COUNT <<< "$out"
echo "remote rows before: $RB_COUNT"
new=0; changed=0
for m in "${MODULES[@]}"; do
  if [ -z "${RB_ROW[$m]+x}" ]; then st=new; new=$((new + 1))
  elif [ "${RB_ROW[$m]}" == "${L_ROW[$m]}" ]; then st=unchanged
  else st=changed; changed=$((changed + 1)); fi
  echo "  before  $st  $m"
done
if [ $DRY -eq 1 ]; then echo "dry run: nothing applied ($new new, $changed changed)"; exit 0; fi

# 3. one transaction of INSERT ... ON DUPLICATE KEY UPDATE for exactly these rows
ups="\`imports\`=VALUES(\`imports\`), \`open\`=VALUES(\`open\`), \`set_option\`=VALUES(\`set_option\`), \`preamble\`=VALUES(\`preamble\`), \`lemma\`=VALUES(\`lemma\`), \`meta\`=VALUES(\`meta\`), \`date\`=VALUES(\`date\`)"
gen_sql="SELECT CONCAT('INSERT INTO lemma (user, module, imports, \`open\`, set_option, preamble, lemma, meta, \`date\`) VALUES (',
  QUOTE(user), ',', QUOTE(module), ',', QUOTE(CAST(imports AS CHAR)), ',', QUOTE(CAST(\`open\` AS CHAR)), ',',
  QUOTE(CAST(set_option AS CHAR)), ',', QUOTE(CAST(preamble AS CHAR)), ',', QUOTE(CAST(lemma AS CHAR)), ',',
  QUOTE(CAST(meta AS CHAR)), ',', QUOTE(CAST(\`date\` AS CHAR)), ') ON DUPLICATE KEY UPDATE $ups;')
FROM lemma WHERE user = '$user' AND module IN ($in_list) ORDER BY module;"
{
  echo "SET NAMES utf8mb4;"
  echo "START TRANSACTION;"
  printf '%s\n' "$gen_sql" | local_mysql -N -B --raw
  echo "COMMIT;"
} > "$tmp/upsert.sql"
n_ins=$(grep -c '^INSERT INTO lemma' "$tmp/upsert.sql")
if [ "$n_ins" -ne "${#MODULES[@]}" ]; then echo "ERROR: generated $n_ins statements for ${#MODULES[@]} modules, aborting" >&2; exit 1; fi
remote_mysql < "$tmp/upsert.sql" || { echo "ERROR: remote apply failed (transaction not committed)" >&2; exit 1; }

# 4. verify
R_COUNT=""
out=$(printf '%s\n' "$checksum_sql" | remote_mysql -s -N -B) || { echo "ERROR: remote verification query failed" >&2; exit 1; }
fill R R_COUNT <<< "$out"
echo "remote rows after: $R_COUNT (expected $((RB_COUNT + new)))"
bad=0
[ "$R_COUNT" == "$((RB_COUNT + new))" ] || { echo "ERROR: unexpected remote row count" >&2; bad=1; }
for m in "${MODULES[@]}"; do
  if [ "${R_ROW[$m]:-}" == "${L_ROW[$m]}" ] && [ "${R_LEM[$m]:-}" == "${L_LEM[$m]}" ]; then
    echo "  after   OK        $m  (row ${L_ROW[$m]:0:8}, lemma ${L_LEM[$m]:0:8})"
  else
    echo "  after   MISMATCH  $m"; bad=1
  fi
done
[ $bad -eq 0 ] && echo "OK: ${#MODULES[@]} row(s) synchronized" || { echo "FAILED" >&2; exit 1; }