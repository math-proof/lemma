#!/bin/bash
# Run mathlib LaTeX batch processing until every entry has non-empty imply.latex.
# Restarts automatically on crash. Reports progress after each round.
cd "$(dirname "$0")/.."

while true; do
    remaining=$(mysql -D axiom -N -e "
        SELECT COUNT(*) FROM mathlib
        WHERE imply IS NULL OR imply = '{}' OR JSON_LENGTH(imply) = 0
           OR JSON_EXTRACT(imply, '$.latex') IS NULL
           OR JSON_EXTRACT(imply, '$.latex') = ''
           OR JSON_EXTRACT(imply, '$.latex') = 'null'" 2>/dev/null)

    remaining=$(echo "$remaining" | tr -d '[:space:]')
    if [ "$remaining" = "0" ]; then
        echo "[$(date)] ALL DONE — 0 unbuilt theorems remaining"
        break
    fi

    echo "[$(date)] $remaining unbuilt theorems remaining — starting node mjs/run_mathlib_latex.mjs"
    node mjs/run_mathlib_latex.mjs --batch 50 --concurrency 2 >> /tmp/mathlib_latex.log 2>&1
    exit_code=$?
    echo "[$(date)] node exited with code $exit_code"

    if [ $exit_code -ne 0 ]; then
        echo "[$(date)] crashed/waiting 5s before retry..."
        sleep 5
    fi
done
