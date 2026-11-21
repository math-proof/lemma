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
# whole repo incl. .git (mirror; incremental, only changed files are copied)
rsync -avzP --no-group --no-times --delete --exclude=.lake --exclude=node_modules /home/cosmos/github/lean/ /mnt/e/github/lean/
```

If the fast-forward is refused because the copy has unrelated local modifications, install only the router (same disk, no network):

```bash
git -C /mnt/e/github/lean fetch /home/cosmos/github/lean main
git -C /mnt/e/github/lean checkout FETCH_HEAD -- index.php
```

The copy needs no build step: `git pull` or `rsync` is enough. If the agent sandbox refuses writes under `/mnt/e`, run these lines in a normal shell.

Invariant — both commands must print nothing:

```bash
diff <(git -C /home/cosmos/github/lean status --porcelain | sort) \
     <(git -C /mnt/e/github/lean status --porcelain | sort)
```
