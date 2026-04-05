#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"

# Optional MySQL (see server/lean/fetchLemmaMysql.mjs, server/app.mjs):
#   export MYSQL_HOST=127.0.0.1 MYSQL_USER=user MYSQL_PWD=user MYSQL_DATABASE=axiom

# Multi-processing: default 8 workers; set LEAN_WORKERS=max, 4, 1, etc.
# One stuck request blocks one worker; others keep serving. Change count: pm2 delete lemma; ./start.sh
#
# PM2: use global if present; otherwise local via npx (install if missing).
# Prefer project-local PM2 (no sudo for global npm; version pinned in package.json).
run_pm2() {
  if command -v pm2 &>/dev/null; then
    command pm2 "$@"
  elif [ -d node_modules/pm2 ]; then
    npx pm2 "$@"
  else
    echo "pm2 not found, installing..."
    npm install pm2
    npx pm2 "$@"
  fi
}

LEAN_WORKERS="${LEAN_WORKERS:-8}"
if [ "$LEAN_WORKERS" = max ]; then
  PM2_INSTANCES=max
elif [ "$LEAN_WORKERS" = 1 ]; then
  PM2_INSTANCES=1
elif [[ "$LEAN_WORKERS" =~ ^[1-9][0-9]*$ ]]; then
  PM2_INSTANCES="$LEAN_WORKERS"
else
  echo "LEAN_WORKERS='$LEAN_WORKERS' not recognized; using 8" >&2
  PM2_INSTANCES=8
fi

if run_pm2 describe lemma &>/dev/null; then
  run_pm2 restart lemma
else
  run_pm2 start server/app.mjs --name lemma -i "$PM2_INSTANCES"
fi
run_pm2 save

# pm2 startup targets systemd/launchd etc. On Git Bash / MSYS it fails ("Init system not found").
case "$(uname -s 2>/dev/null)" in
  MINGW*|MSYS*|CYGWIN*|*_NT-*)
    echo "Skipping pm2 startup (Windows-like host). Use Task Scheduler or run this script after login."
    ;;
  *)
    run_pm2 startup
    ;;
esac
