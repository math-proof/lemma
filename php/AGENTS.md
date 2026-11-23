# PHP front end

The PHP server renders the site at http://localhost:8080/lean/ (`index.php` + `php/`).

## Scope

- Work only in `~/github/lean/php/`. The root `index.php` is the PHP front controller and belongs to this folder.
- `/mnt/e/github/lean` (`E:\github\lean`) is the copy Apache/WAMP serves: refresh it, never edit it in place. Development happens in `~/github/lean`.

## Syncing the copy

Preferred (once the change is committed and pushed to `origin/main`):

```bash
git -C /mnt/e/github/lean pull --ff-only
```

If the GitHub fetch is slow or aborts (`fatal: early EOF`, `git-remote-https died of signal 15`), rsync instead:

```bash
# full refresh — scans the whole tree; use for the first sync or when the copy is far behind
rsync -aP --delete --filter=':- .gitignore' ~/github/lean/ /mnt/e/github/lean/

# incremental — syncs only working-tree files changed since the copy's last sync
# (determined by `git diff`), no full-tree scan, and mirrors .git (HEAD/index/refs)
# with rsync so `git status` is identical on both sides afterwards — including after
# a `git push`. Honors every .gitignore via git tracking. Covers php/ and anything
# else you edited. Preview first with --dry-run, then drop it to apply.
bash ~/github/lean/php/rsync.sh --dry-run
bash ~/github/lean/php/rsync.sh
```

If the fast-forward is refused because the copy has unrelated local modifications, install only the router (same disk, no network):

```bash
git -C /mnt/e/github/lean fetch ~/github/lean main
```

The copy needs no build step: `git pull` or `rsync` is enough. If the agent sandbox refuses writes under `/mnt/e`, run these lines in a normal shell.

Invariant — both commands must print nothing:

```bash
diff <(git -C ~/github/lean status --porcelain | sort) \
     <(git -C /mnt/e/github/lean status --porcelain | sort)
```
