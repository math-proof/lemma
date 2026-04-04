#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
# Optional MySQL (see server/lean/fetchLemmaMysql.mjs, server/app.mjs):
#   export MYSQL_HOST=127.0.0.1 MYSQL_USER=user MYSQL_PWD=user MYSQL_DATABASE=axiom
exec npm start
