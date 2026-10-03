#!/bin/bash
# . sh/run.sh [continue]      (bash counterpart of ps1/run.ps1)
# with "continue" (or true / 1), the run is repeated even after a successful exit
continue_after_success=0
case "$1" in true|1|continue) continue_after_success=1 ;; esac

export OPENBLAS_NUM_THREADS=1

# run from the repository root, like ps1/run.ps1 does
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

if [ -z "$MYSQL_USER" ] && [ -f ~/.bash_profile ]; then
  echo "MYSQL_USER is not set, acquiring it from ~/.bash_profile"
  source ~/.bash_profile
fi

# WSL often has python3 only
if command -v python > /dev/null; then PY=python; else PY=python3; fi

while true; do
    # Run the Python program with a timeout of 2 minutes (120 seconds);
    # -k force-kills it 5 seconds later if it ignores the termination signal
    timeout -k 5 120 "$PY" run.py
    exit_status=$?

    if [ $exit_status -eq 124 ] || [ $exit_status -eq 137 ]; then
        echo "Python program was halted because it took more than 2 minutes."
    elif [ $exit_status -eq 0 ]; then
        echo "Python program completed within the time limit."
        [ $continue_after_success -eq 1 ] || break
    else
        echo "An error occurred. Exit status: $exit_status"
    fi
done

read -r -p "Please enter any key to continue" user_input

"$PY" -c "exec(open('./util/hierarchy.py').read())"
"$PY" -c "exec(open('./util/function.py').read())"
"$PY" util/clean_prove_imports.py
"$PY" util/sync_created_dates.py