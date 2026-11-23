#!/usr/bin/env bash
# Incremental sync from the Linux source of truth to the Windows copy Apache
# serves. Only working-tree files that changed since the copy's last synced
# commit are copied/removed — no full-tree scan — and .git is mirrored with
# rsync so HEAD/index/refs match. Net effect: `git status` is identical on both
# sides afterwards, including after a `git push` (no manual ff-merge needed).
#
#   SRC  ~/github/lean        (source of truth; where you edit)
#   DST  /mnt/e/github/lean   (served copy; refresh-only, never edit in place)
#
# "Changed" = the union of:
#   * git diff <DST_HEAD> --      tracked files modified/added/deleted/renamed
#                                 between the copy's HEAD and the source working
#                                 tree (covers new commits AND uncommitted edits)
#   * git ls-files --others       untracked, non-ignored files to create
# plus a full mirror of .git (HEAD/index/refs/objects) via rsync.
#
# Run with -n/--dry-run first to preview. The agent sandbox cannot write under
# /mnt/e, so execute this in a normal shell.
#
# First sync (or when the copy is far behind): run the full rsync once — see
# php/AGENTS.md. This script assumes the copy already exists and was synced.
set -euo pipefail

SRC="${SRC:-$HOME/github/lean}"
DST="${DST:-/mnt/e/github/lean}"
DRY_RUN=0
VERBOSE=0

while [ $# -gt 0 ]; do
    case "$1" in
        -n|--dry-run) DRY_RUN=1; shift ;;
        -v|--verbose) VERBOSE=1; shift ;;
        --src)  SRC="$2"; shift 2 ;;
        --dst)  DST="$2"; shift 2 ;;
        -h|--help)
            sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) echo "rsync.sh: unknown argument: $1" >&2; exit 2 ;;
    esac
done

# --- guards -----------------------------------------------------------------
[ -d "$SRC/.git" ] || { echo "rsync.sh: SRC is not a git repo: $SRC" >&2; exit 1; }
[ "$(cd "$SRC" && pwd)" != "$(cd "$DST" 2>/dev/null && pwd || true)" ] \
    || { echo "rsync.sh: SRC and DST are the same directory" >&2; exit 1; }

# --- determine the base commit: what the destination currently has ------------
BASE=""
if [ -d "$DST/.git" ]; then
    BASE=$(git -C "$DST" rev-parse --verify HEAD 2>/dev/null || true)
fi
# If the copy's HEAD isn't a known object in the source (copy was never fully
# synced, or diverged), fall back to the source HEAD: then only uncommitted
# working-tree changes are synced, which is still safe (no full scan).
if [ -z "$BASE" ] || ! git -C "$SRC" cat-file -e "${BASE}^{commit}" 2>/dev/null; then
    BASE=$(git -C "$SRC" rev-parse HEAD)
    echo "rsync.sh: note: copy HEAD unknown in source; basing diff on source HEAD ($BASE)" >&2
fi

cd "$SRC"

tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT

# --- collect actions (NUL-delimited: ACTION\0PATH\0) -------------------------
# 1) tracked changes between BASE and the working tree.
#    `git diff -M --name-status -z` emits:  STATUS\0PATH\0
#    for renames/copies (-M/-C):            STATUS\0OLD\0NEW\0
#    (-M detects renames so a moved file is one copy + one rm, not a full
#    delete+re-add; without -M git reports D+A, which also works.)
while IFS= read -r -d '' st && IFS= read -r -d '' p1; do
    case "$st" in
        R*)  # rename: copy new, remove old
            IFS= read -r -d '' p2 || true
            printf 'RM\0%s\0' "$p1" >> "$tmp"
            printf 'CP\0%s\0' "$p2" >> "$tmp"
            ;;
        C*)  # copy
            IFS= read -r -d '' p2 || true
            printf 'CP\0%s\0' "$p2" >> "$tmp"
            ;;
        D*)
            printf 'RM\0%s\0' "$p1" >> "$tmp"
            ;;
        U*)  # unmerged conflict — leave it, don't guess
            echo "rsync.sh: WARN skipping unmerged path: $p1" >&2
            ;;
        *)   # M, A, T, ... -> copy the working-tree version
            printf 'CP\0%s\0' "$p1" >> "$tmp"
            ;;
    esac
done < <(git diff -M --name-status -z "$BASE" --)

# 2) untracked, non-ignored files to create on the copy.
while IFS= read -r -d '' f; do
    printf 'CP\0%s\0' "$f" >> "$tmp"
done < <(git ls-files --others --exclude-standard -z --)

# Note: `git diff` yields unique paths and untracked files are disjoint from the
# diff set, so no dedup is needed. (Do NOT `sort -z` here — it would sort the
# individual NUL-delimited fields and break the action/path pairing.)
count=$(tr -cd '\0' < "$tmp" | wc -c); count=$(( count / 2 ))
echo "rsync.sh: syncing $count changed path(s): $SRC -> $DST  (base=$BASE)"

copied=0; removed=0; skipped=0
while IFS= read -r -d '' action && IFS= read -r -d '' path; do
    [ -z "$path" ] && continue
    case "$path" in .git/*) skipped=$((skipped+1)); continue ;; esac  # never sync .git internals

    s="$SRC/$path"
    d="$DST/$path"

    if [ "$action" = CP ]; then
        if [ ! -e "$s" ] && [ ! -L "$s" ]; then
            echo "rsync.sh: SKIP (source gone): $path" >&2
            skipped=$((skipped+1)); continue
        fi
        if [ "$DRY_RUN" -eq 1 ]; then
            printf 'COPY  %s\n' "$path"
        else
            mkdir -p -- "$(dirname -- "$d")"
            cp -f -- "$s" "$d"
            [ "$VERBOSE" -eq 1 ] && printf 'copied %s\n' "$path"
        fi
        copied=$((copied+1))
    else  # RM
        if [ "$DRY_RUN" -eq 1 ]; then
            printf 'RM    %s\n' "$path"
        else
            if [ -e "$d" ] || [ -L "$d" ]; then
                rm -f -- "$d"
                [ "$VERBOSE" -eq 1 ] && printf 'removed %s\n' "$path"
            fi
        fi
        removed=$((removed+1))
    fi
done < "$tmp"

# --- mirror .git (HEAD/index/refs/objects) so `git status` parity holds -------
# The file sync above only touches working-tree files; .git internals are not
# reported by `git diff`, so mirror them wholesale with rsync. This advances the
# copy's HEAD/index/refs to match the source — the piece that makes `git status`
# identical on both sides, including after a `git push`.
#
# Pass 1: full mirror with rsync's default size+mtime quick-check (fast). Brings
# over new/changed objects and packs, and `--delete` prunes stale refs/objects
# the copy no longer needs. This is:  rsync -aP --delete SRC/.git/ DST/.git/
# (trailing slashes are required — without them rsync nests .git/.git).
#
# Pass 2: re-check ONLY the small mutable metadata by CHECKSUM. Files like
# refs/heads/*, packed-refs and index keep a fixed size when their content
# changes, so a same-size + same-mtime collision could make pass 1 skip them.
# These files total ~11 MB, so the checksum is cheap; the 500 MB+ object store
# is only stat'd in pass 1, never checksummed. Together the two passes make
# HEAD/index/refs parity deterministic.
if [ "$DRY_RUN" -eq 1 ] || [ "$VERBOSE" -eq 1 ]; then
    echo "rsync.sh: mirroring .git ($SRC/.git/ -> $DST/.git/)"
fi
n=''; [ "$DRY_RUN" -eq 1 ] && n='n'
rsync -a${n}P --delete -- "$SRC/.git/" "$DST/.git/"
rsync -a${n} --checksum \
    --include='HEAD' --include='packed-refs' --include='index' \
    --include='refs/' --include='refs/***' \
    --exclude='*' \
    -- "$SRC/.git/" "$DST/.git/"

printf 'rsync.sh: done. copied=%d removed=%d skipped=%d (dry_run=%d)\n' \
    "$copied" "$removed" "$skipped" "$DRY_RUN"
