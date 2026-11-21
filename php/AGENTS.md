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
# whole repo (mirrors ~/github/lean/ into E:\github\lean\)
rsync -avzP --no-group --no-times --exclude=.git /home/cosmos/github/lean/ /mnt/e/github/lean/

# PHP-owned paths only
rsync -avzP --no-group --no-times /home/cosmos/github/lean/index.php /mnt/e/github/lean/index.php
rsync -avzP --no-group --no-times /home/cosmos/github/lean/php/ /mnt/e/github/lean/php/
```

If the fast-forward is refused because the copy has unrelated local modifications, install only the router (same disk, no network):

```bash
git -C /mnt/e/github/lean fetch /home/cosmos/github/lean main
git -C /mnt/e/github/lean checkout FETCH_HEAD -- index.php
```

The copy needs no build step: `git pull` or `rsync` is enough. If the agent sandbox refuses writes under `/mnt/e`, run these lines in a normal shell.

`sh/rsync.sh` is not used here: it wraps rsync over SSH (`--host` is mandatory), while this copy is on the same local disk.
