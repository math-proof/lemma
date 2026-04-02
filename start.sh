#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
# Optional MySQL (see server/lean/fetchLemmaMysql.mjs, server/app.mjs):
#   export MYSQL_HOST=127.0.0.1 MYSQL_USER=user MYSQL_PWD=user MYSQL_DATABASE=axiom
# With MYSQL_HOST set, lemma + proof latex load from DB when a row exists.
# PHP-style .echo.lean gate only: export LEAN_MYSQL_ECHO_RULE=1
exec npm start
