#!/usr/bin/env bash
# Deploy this Node app onto the remote Linux account.
#
# Local and remote project path: ~/github/lean
# .git, node_modules, tmp, and env files are left in place. .lake is not
# uploaded: the remote has no Lean compiler. The Node app listens on port 80.
#
#   bash sh/deploy.sh
#   bash sh/deploy.sh -n
#
# Steps: build dist/vue (pages.js and codemirror.js), rsync via sh/rsync.sh,
# npm ci --omit=dev when the lockfile changed, apply sql/create/*.sql
# (CREATE TABLE when missing, ALTER TABLE when the live columns differ),
# then load local rows without replacing that schema. Point lemma-node at
# ~/github/lean and restart it.
#
# Credentials (never printed, never hardcoded):
#   REMOTE_MYSQL_USER  ssh user and MySQL user on the remote host
#   REMOTE_MYSQL_PWD   MySQL password of that user on the remote host
#   REMOTE_MYSQL_HOST  remote host
#   REMOTE_MYSQL_PORT  remote MySQL port (default 3306)
#   If one is unset and powershell.exe is reachable (WSL), it is read from
#   the Windows environment.
#   SSH_OPTS: extra ssh options (default: BatchMode, no prompt).
#   SSH_CMD: ssh executable (default: ssh).
set -euo pipefail
cd "$(dirname "$0")/.."

DRY=0
while [ $# -gt 0 ]; do
  case "$1" in
    -n|--dry-run) DRY=1 ;;
    -h|--help) sed -n '2,/^set -euo pipefail$/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "ERROR: unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

env_or_ps() {
  local v=${!1:-}
  if [ -z "$v" ] && command -v powershell.exe >/dev/null 2>&1; then
    v=$(powershell.exe -NoProfile -Command "[Environment]::GetEnvironmentVariable('$1')" 2>/dev/null | tr -d '\r\n')
  fi
  printf '%s' "$v"
}
R_USER=$(env_or_ps REMOTE_MYSQL_USER)
R_HOST=$(env_or_ps REMOTE_MYSQL_HOST)
R_PWD=$(env_or_ps REMOTE_MYSQL_PWD)
R_PORT=$(env_or_ps REMOTE_MYSQL_PORT); R_PORT=${R_PORT:-3306}
for v in R_USER R_HOST R_PWD; do
  if [ -z "${!v}" ]; then echo "ERROR: REMOTE_MYSQL_${v#R_} is not set" >&2; exit 2; fi
done
if [[ "$R_USER$R_HOST$R_PORT" =~ [[:space:]\'\"\\\;\`\$\&\|\<\>\(\)] ]]; then
  echo "ERROR: unsafe characters in remote user/host/port" >&2
  exit 2
fi
case "$R_PWD" in
  *$'\n'*|*"'"*) echo "ERROR: remote password cannot contain a newline or a single quote" >&2; exit 2 ;;
esac

export SSH_CMD="${SSH_CMD:-ssh}"
export SSH_OPTS="${SSH_OPTS:--o BatchMode=yes -o ConnectTimeout=20}"
read -r -a SSH_OPT_ARR <<< "$SSH_OPTS"
ssh_remote() { "$SSH_CMD" "${SSH_OPT_ARR[@]}" "$R_USER@$R_HOST" "$@"; }

echo "remote = $R_USER@$R_HOST:~/github/lean"

if [ "$DRY" -eq 0 ]; then
  echo "build vue bundle"
  npm run build:vue
  test -s dist/vue/pages.js
  test -s dist/vue/codemirror.js
fi

# Same relative path on both sides: ~/github/lean. .lake is the local Lean
# build cache; the remote machine has no compiler, so it is not synced.
rsync_args=(github/lean --host "$R_USER@$R_HOST" --delete --times --no-owner)
rsync_args+=(--exclude '.git/,node_modules/,.lake/,tmp/,.env,*.env')
[ "$DRY" -eq 1 ] && rsync_args+=(--dry-run)
echo "rsync ~/github/lean -> $R_USER@$R_HOST:~/github/lean"
bash sh/rsync.sh "${rsync_args[@]}"

if [ "$DRY" -eq 0 ]; then
  echo "remote npm ci"
  ssh_remote bash -s <<'EOF'
set -euo pipefail
cd "$HOME/github/lean"
NPM=/usr/local/bin/npm
[ -x "$NPM" ] || NPM=$(command -v npm)
lock=$(sha256sum package-lock.json | awk 'NR==1 { print $1 }')
stamp=/var/lib/lemma-node/package-lock.sha256
mkdir -p /var/lib/lemma-node
prev=$(cat "$stamp" 2>/dev/null || true)
if [ "$lock" != "$prev" ] || [ ! -d node_modules/express ]; then
  "$NPM" ci --omit=dev
  printf '%s\n' "$lock" > "$stamp"
else
  echo "npm ci skipped (lockfile unchanged)"
fi
EOF
fi

# Schema from sql/create/*.sql, then row data from the local axiom database.
# A missing remote table is created by executing that file. An existing table
# keeps its rows and is altered until its columns match the file. The data
# load does not emit CREATE TABLE, so a column that exists only in sql/create
# (local mathlib has no `explicit`) is not dropped.
shopt -s nullglob
SQL_FILES=(sql/create/*.sql)
shopt -u nullglob
if [ ${#SQL_FILES[@]} -eq 0 ]; then echo "ERROR: sql/create/*.sql is empty" >&2; exit 1; fi

parse_create_cols() {
  awk '
    /^[[:space:]]*(CREATE|PARTITION|[)]|$)/ { next }
    /^[[:space:]]*(PRIMARY|UNIQUE|KEY|CONSTRAINT|FULLTEXT)/ { next }
    {
      line=$0
      sub(/^[[:space:]]+/, "", line)
      sub(/^`/, "", line)
      if (match(line, /^[A-Za-z_][A-Za-z0-9_]*/)) print substr(line, RSTART, RLENGTH)
    }
  ' "$1"
}

expected_cols=$(mktemp)
trap 'rm -f "$expected_cols"' EXIT
for f in "${SQL_FILES[@]}"; do
  t=$(basename "$f" .sql)
  echo "$t $(parse_create_cols "$f" | paste -sd' ' -)" >> "$expected_cols"
done

echo "mysql schema from sql/create"
tar -C sql/create -cf - . | ssh_remote "rm -rf /tmp/lemma-sql && mkdir -p /tmp/lemma-sql && tar -xf - -C /tmp/lemma-sql"
pw=$(printf '%s' "$R_PWD" | sed 's/[\\"]/\\&/g')
ssh_remote bash -s -- "$DRY" <<EOF
set -euo pipefail
DRY=\$1
umask 077
cnf=\$(mktemp)
trap 'rm -f "\$cnf"' EXIT
printf '[client]\nuser=$R_USER\npassword="$pw"\nport=$R_PORT\ndefault-character-set=utf8mb4\n' > "\$cnf"
M=/usr/local/mysql/bin/mysql; [ -x "\$M" ] || M=mysql
q() { "\$M" --defaults-extra-file="\$cnf" -D axiom -N -B "\$@"; }
exec_sql() {
  echo "\$1"
  if [ "\$DRY" -eq 0 ]; then q -e "\$1"; fi
}
table_exists() { [ "\$(q -e "SELECT COUNT(*) FROM information_schema.TABLES WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='\$1'")" = 1 ]; }
has_col() { [ "\$(q -e "SELECT COUNT(*) FROM information_schema.COLUMNS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='\$1' AND COLUMN_NAME='\$2'")" = 1 ]; }
part_method() { q -e "SELECT IFNULL(PARTITION_METHOD,'') FROM information_schema.PARTITIONS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='\$1' LIMIT 1"; }
has_index() { [ "\$(q -e "SELECT COUNT(*) FROM information_schema.STATISTICS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='\$1' AND INDEX_NAME='\$2'")" != 0 ]; }

for f in /tmp/lemma-sql/*.sql; do
  t=\$(basename "\$f" .sql)
  if table_exists "\$t"; then
    echo "table \$t exists"
    continue
  fi
  echo "CREATE TABLE \$t  <= \$f"
  if [ "\$DRY" -eq 0 ]; then q < "\$f"; fi
done

lemma_from_user=0
if table_exists lemma && has_col lemma user; then
  dups=\$(q -e "SELECT COUNT(*) FROM (SELECT module FROM lemma GROUP BY module HAVING COUNT(*) > 1) d")
  if [ "\$dups" != 0 ]; then
    echo "ERROR: lemma.module is not unique (\$dups name(s)); not dropping user" >&2
    exit 1
  fi
  if [ -n "\$(part_method lemma)" ]; then
    exec_sql "ALTER TABLE lemma REMOVE PARTITIONING"
  fi
  exec_sql 'ALTER TABLE lemma DROP PRIMARY KEY, ADD COLUMN id int NOT NULL AUTO_INCREMENT PRIMARY KEY FIRST, ADD UNIQUE KEY uq_lemma_module (module), DROP COLUMN \`user\`'
  lemma_from_user=1
fi
if [ "\$lemma_from_user" -eq 0 ] && table_exists lemma && ! has_col lemma id; then
  exec_sql "ALTER TABLE lemma ADD COLUMN id int NOT NULL AUTO_INCREMENT PRIMARY KEY FIRST"
fi
if [ "\$lemma_from_user" -eq 0 ] && table_exists lemma && [ -n "\$(part_method lemma)" ]; then
  exec_sql "ALTER TABLE lemma REMOVE PARTITIONING"
fi
if [ "\$lemma_from_user" -eq 0 ] && table_exists lemma && ! has_index lemma uq_lemma_module; then
  dups=\$(q -e "SELECT COUNT(*) FROM (SELECT module FROM lemma GROUP BY module HAVING COUNT(*) > 1) d")
  if [ "\$dups" != 0 ]; then
    echo "ERROR: lemma.module is not unique (\$dups name(s)); not adding uq_lemma_module" >&2
    exit 1
  fi
  exec_sql "ALTER TABLE lemma ADD UNIQUE KEY uq_lemma_module (module)"
fi
if table_exists mathlib && ! has_col mathlib explicit; then
  exec_sql 'ALTER TABLE mathlib ADD COLUMN \`explicit\` text COLLATE utf8mb4_bin NULL AFTER \`implicit\`'
fi
if table_exists docstring && ! has_index docstring ft_docstring; then
  exec_sql "ALTER TABLE docstring ADD FULLTEXT KEY ft_docstring (text)"
fi
for t in mathlib inverted unicode; do
  if table_exists "\$t" && [ -z "\$(part_method "\$t")" ]; then
    exec_sql "ALTER TABLE \$t PARTITION BY KEY() PARTITIONS 8"
  fi
done

if [ "\$DRY" -eq 0 ]; then
  while read -r table cols; do
    [ -n "\$table" ] || continue
    got=\$(q -e "SELECT COLUMN_NAME FROM information_schema.COLUMNS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='\$table' ORDER BY ORDINAL_POSITION" | paste -sd' ' -)
    if [ "\$got" != "\$cols" ]; then
      echo "ERROR: \$table columns differ after CREATE/ALTER" >&2
      echo "  sql/create: \$cols" >&2
      echo "  remote:     \$got" >&2
      exit 1
    fi
    echo "schema \$table OK"
  done <<'COLS'
$(cat "$expected_cols")
COLS
fi
EOF

if [ "$DRY" -eq 0 ]; then
  umask 077
  local_cnf=$(mktemp)
  trap 'rm -f "$expected_cols" "$local_cnf"' EXIT
  {
    echo "[client]"
    echo "host=${MYSQL_HOST:-127.0.0.1}"
    echo "port=${MYSQL_PORT:-3306}"
    echo "user=${LOCAL_MYSQL_USER:-prod}"
    [ -n "${MYSQL_PWD:-}" ] && printf 'password="%s"\n' "$(printf '%s' "$MYSQL_PWD" | sed 's/[\\"]/\\&/g')"
    echo "default-character-set=utf8mb4"
  } > "$local_cnf"
  local_mysql() { env -u MYSQL_PWD mysql --defaults-extra-file="$local_cnf" -D axiom -N -B "$@"; }
  dump_bin=(mysqldump --defaults-extra-file="$local_cnf")
  dump_bin+=(--single-transaction --no-create-info --complete-insert --skip-triggers)
  dump_bin+=(--skip-add-locks --no-tablespaces --set-gtid-purged=OFF)
  dump_bin+=(--max_allowed_packet=8M --net_buffer_length=1M)
  while read -r table cols; do
    [ -n "$table" ] || continue
    echo "mysql data $table"
    mapfile -t local_cols < <(local_mysql -e "SELECT COLUMN_NAME FROM information_schema.COLUMNS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='${table}' ORDER BY ORDINAL_POSITION")
    if [ ${#local_cols[@]} -eq 0 ]; then
      echo "ERROR: local axiom.$table does not exist" >&2
      exit 1
    fi
    for c in "${local_cols[@]}"; do
      case " $cols " in
        *" $c "*) ;;
        *) echo "ERROR: local axiom.$table.$c is not in sql/create/$table.sql" >&2; exit 1 ;;
      esac
    done
    ssh_remote bash -s <<EOF
set -euo pipefail
umask 077
cnf=\$(mktemp)
trap 'rm -f "\$cnf"' EXIT
printf '[client]\nuser=$R_USER\npassword="$pw"\nport=$R_PORT\ndefault-character-set=utf8mb4\n' > "\$cnf"
M=/usr/local/mysql/bin/mysql; [ -x "\$M" ] || M=mysql
"\$M" --defaults-extra-file="\$cnf" -D axiom -e "DROP TABLE IF EXISTS ${table}_old, ${table}_next; CREATE TABLE ${table}_next LIKE ${table}"
EOF
    env -u MYSQL_PWD "${dump_bin[@]}" axiom "$table" \
      | sed "s/^INSERT INTO \`${table}\`/INSERT INTO \`${table}_next\`/" \
      | gzip -1 \
      | ssh_remote "umask 077; cnf=\$(mktemp); trap 'rm -f \"\$cnf\"' EXIT; printf '[client]\\nuser=$R_USER\\npassword=\"$pw\"\\nport=$R_PORT\\ndefault-character-set=utf8mb4\\n' > \"\$cnf\"; M=/usr/local/mysql/bin/mysql; [ -x \"\$M\" ] || M=mysql; gunzip | \"\$M\" --defaults-extra-file=\"\$cnf\" -D axiom"
    ssh_remote bash -s <<EOF
set -euo pipefail
umask 077
cnf=\$(mktemp)
trap 'rm -f "\$cnf"' EXIT
printf '[client]\nuser=$R_USER\npassword="$pw"\nport=$R_PORT\ndefault-character-set=utf8mb4\n' > "\$cnf"
M=/usr/local/mysql/bin/mysql; [ -x "\$M" ] || M=mysql
q() { "\$M" --defaults-extra-file="\$cnf" -D axiom -N -B "\$@"; }
if q -e "SELECT COUNT(*) FROM information_schema.COLUMNS WHERE TABLE_SCHEMA='axiom' AND TABLE_NAME='${table}' AND EXTRA LIKE '%auto_increment%'" | grep -qx 1; then
  n=\$(q -e "SELECT COALESCE(MAX(id),0)+1 FROM ${table}_next")
  q -e "ALTER TABLE ${table}_next AUTO_INCREMENT = \$n"
fi
q -e "RENAME TABLE ${table} TO ${table}_old, ${table}_next TO ${table}; DROP TABLE ${table}_old"
EOF
    local_n=$(local_mysql -e "SELECT COUNT(*) FROM \`${table}\`")
    remote_n=$(ssh_remote bash -s <<EOF
set -euo pipefail
umask 077
cnf=\$(mktemp)
trap 'rm -f "\$cnf"' EXIT
printf '[client]\nuser=$R_USER\npassword="$pw"\nport=$R_PORT\ndefault-character-set=utf8mb4\n' > "\$cnf"
M=/usr/local/mysql/bin/mysql; [ -x "\$M" ] || M=mysql
"\$M" --defaults-extra-file="\$cnf" -D axiom -N -B -e "SELECT COUNT(*) FROM ${table}"
EOF
)
    if [ "$local_n" != "$remote_n" ]; then
      echo "ERROR: $table row count local=$local_n remote=$remote_n" >&2
      exit 1
    fi
    echo "data $table OK ($remote_n)"
  done < "$expected_cols"
else
  echo "dry run: schema checked above; row data not loaded"
fi

if [ "$DRY" -eq 0 ]; then
  echo "point lemma-node at ~/github/lean and restart"
  ssh_remote bash -s <<'EOF'
set -euo pipefail
wd="$HOME/github/lean"
unit=/etc/systemd/system/lemma-node.service
test -f "$wd/mjs/app.mjs"
case "$wd" in
  *[!A-Za-z0-9/_.-]*) echo "ERROR: unsafe remote home path" >&2; exit 1 ;;
esac
if [ ! -f "$unit" ]; then
  echo "ERROR: $unit is missing" >&2
  exit 1
fi
if grep -q '^WorkingDirectory[[:space:]]*=' "$unit"; then
  sed -i "s|^WorkingDirectory[[:space:]]*=.*|WorkingDirectory=$wd|" "$unit"
else
  sed -i "/^\[Service\]/a WorkingDirectory=$wd" "$unit"
fi
systemctl daemon-reload
envfile=/etc/lemma-node.env
if [ -f "$envfile" ] && grep -q '^PORT=' "$envfile"; then
  sed -i 's/^PORT=.*/PORT=80/' "$envfile"
else
  echo 'PORT=80' >> "$envfile"
fi
systemctl restart lemma-node
systemctl is-active lemma-node
EOF
fi

echo "OK: ~/github/lean"
