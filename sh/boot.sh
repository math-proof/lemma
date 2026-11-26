#!/usr/bin/env bash
# Start the site after a Windows sign-in if it is not already serving.
# A reboot stops WSL; the logon task runs this and does not need a terminal.
set -eu
cd "$(dirname "$0")/.."
if curl -sf -o /dev/null --max-time 3 http://127.0.0.1/lean/; then
  exit 0
fi
exec bash sh/start.sh
