#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"

# Optional MySQL (see server/lean/fetchLemmaMysql.mjs, server/app.mjs):
#   export MYSQL_HOST=127.0.0.1 MYSQL_USER=user MYSQL_PWD=user MYSQL_DATABASE=axiom

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

if run_pm2 describe lemma &>/dev/null; then
  run_pm2 restart lemma
else
  run_pm2 start server/app.mjs --name lemma
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
