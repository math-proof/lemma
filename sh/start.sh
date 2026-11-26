#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/.."

# Non-interactive boots (Windows logon) do not read .bashrc, where Node is added to PATH.
for d in "$HOME"/.local/node-v*/bin; do
  if [ -x "$d/node" ]; then
    export PATH="$d:$PATH"
  fi
done

# Optional MySQL (see mjs/lean/fetchLemmaMysql.mjs, mjs/app.mjs):

# Multi-processing: default 4 workers; set LEAN_NUM_THREADS=max, 4, 1, etc.
# One stuck request blocks one worker; others keep serving. Change count: pm2 delete lemma; ./sh/start.sh
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

LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
if [ "$LEAN_NUM_THREADS" = max ]; then
  PM2_INSTANCES=max
elif [ "$LEAN_NUM_THREADS" = 1 ]; then
  PM2_INSTANCES=1
elif [[ "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]]; then
  PM2_INSTANCES="$LEAN_NUM_THREADS"
else
  echo "LEAN_NUM_THREADS='$LEAN_NUM_THREADS' not recognized; using 4" >&2
  PM2_INSTANCES=4
fi

if run_pm2 describe lemma &>/dev/null; then
  run_pm2 restart lemma
else
  run_pm2 start mjs/app.mjs --name lemma -i "$PM2_INSTANCES"
fi
run_pm2 save

# A systemd unit only runs when systemd is pid 1. This WSL distro boots with /init,
# so the Windows logon task in sh/boot.sh is what starts the server after a reboot.
if [ "$(ps -p 1 -o comm= 2>/dev/null || true)" = systemd ]; then
  run_pm2 startup || true
fi
