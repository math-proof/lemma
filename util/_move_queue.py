"""One-at-a-time Algebra moves. Stop on first failure.

Usage:
  python util/_move_queue.py pairs.txt
  python util/_move_queue.py pairs.txt 3
"""
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(r"e:\github\py")
LOG = ROOT / "util" / "_move_last.log"


def load_pairs(path: Path) -> list[tuple[str, str]]:
    pairs = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        old, new = line.split()
        pairs.append((old, new))
    return pairs


def main():
    pair_file = Path(sys.argv[1])
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    pairs = load_pairs(pair_file)
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    for i, (src, dst) in enumerate(pairs[start:], start=start):
        print(f"\n======== [{i + 1}/{len(pairs)}] {src} -> {dst} ========", flush=True)
        with LOG.open("w", encoding="utf-8", errors="replace") as fh:
            r = subprocess.run(
                [sys.executable, "util/rename_algebra.py", src, dst, "--prove"],
                cwd=ROOT,
                stdout=fh,
                stderr=subprocess.STDOUT,
                env=env,
            )
        out = LOG.read_text(encoding="utf-8", errors="replace")
        print(out[-2000:], end="", flush=True)
        if f"{src} -> {dst}" not in out or "total failed    = 0" not in out:
            print(f"STOP at {src}: rename/prove failed, exit {r.returncode}", flush=True)
            sys.exit(2)
    print("QUEUE_DONE", flush=True)


if __name__ == "__main__":
    main()
