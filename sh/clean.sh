# usage:
# bash sh/clean.sh
#
# Remove unused lake artifacts (.olean, .ilean, .trace, .hash, .c) whose
# corresponding .lean sources no longer exist, leftover *.echo.lean files,
# and empty directories.
#
# Sourced by sh/run.sh after a run. Section runs skip the repo-wide .lake
# sweep and empty-dir cleanup: remove_invalid_* strips at the first dot, so
# Lemma/test.Nat.0.olean is treated as Lemma/test.lean and would be deleted
# (or would delete another run's in-progress test artifacts).

# When executed directly, run from the repo root.
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  cd "$(cd "$(dirname "$0")" && pwd)/.."
fi

function remove_invalid_ir_file {
  module=${1#*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    rm $1
  fi
}

# Section runs skip the repo-wide .lake sweep: remove_invalid_* strips at the
# first dot, so Lemma/test.Nat.0.olean is treated as Lemma/test.lean and would
# be deleted (or would delete another run's in-progress test artifacts).
if [ ${#MODULES[@]} -eq 0 ]; then
  find .lake/build/ir -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
      remove_invalid_ir_file $file
  done
fi

function remove_invalid_lib_file {
  module=${1#*/*/*/*/}
  module=${module%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    rm $1
  fi
}

if [ ${#MODULES[@]} -eq 0 ]; then
  find .lake/build/lib -type f -regex '.*\.\(trace\|olean\|ilean\|hash\|c\)$' | while read -r file; do
      remove_invalid_lib_file $file
  done
fi

function remove_invalid_echo_file {
  module=${1%%.*}
  module="$module.lean"
  if [ ! -f $module ]; then
    rm $1
  fi
}

find Lemma -type f -regex '.*\.echo\.lean$' | while read -r file; do
    remove_invalid_echo_file $file
done

if [ ${#MODULES[@]} -eq 0 ]; then
  find . -type d -empty -exec rmdir {} +
  find .lake/build -type d -empty -exec rmdir {} +
fi
