#!/usr/bin/env python3
"""Compare methods in a `lean.php` class: HEAD vs working tree (names + body equality)."""
import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "php" / "parser" / "lean.php"

PRESETS: dict[str, tuple[str, str]] = {
    "lean": (
        "abstract class Lean extends IndentedNode\n{",
        "\n}\n\nclass LeanCaret extends Lean",
    ),
    "leancaret": (
        "class LeanCaret extends Lean\n{",
        "\n}\n\nclass LeanToken extends Lean",
    ),
}

SIG_RE = re.compile(
    r"\n    ((?:public static |public |static )?function (\w+)\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)


def extract_class_body(text: str, marker_start: str, marker_end: str) -> str:
    si = text.index(marker_start) + len(marker_start)
    ei = text.index(marker_end, si)
    return text[si:ei]


def split_methods(body: str) -> dict[str, str]:
    matches = list(SIG_RE.finditer(body))
    out: dict[str, str] = {}
    for i, m in enumerate(matches):
        name = m.group(2)
        chunk = body[m.start() : matches[i + 1].start() if i + 1 < len(matches) else len(body)]
        if name in out:
            print(f"WARNING: duplicate method {name!r}", file=sys.stderr)
        out[name] = chunk
    return out


def normalize(s: str) -> str:
    lines = [ln.rstrip() for ln in s.splitlines()]
    return "\n".join(lines).strip() + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description="Compare class methods HEAD vs work tree.")
    ap.add_argument(
        "preset",
        nargs="?",
        default="lean",
        choices=sorted(PRESETS.keys()),
        help="class block (default: lean)",
    )
    args = ap.parse_args()
    marker_start, marker_end = PRESETS[args.preset]

    r = subprocess.run(
        ["git", "show", f"HEAD:{LEAN.relative_to(ROOT).as_posix()}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    head_text = r.stdout
    work_text = LEAN.read_text(encoding="utf-8")

    hb = extract_class_body(head_text, marker_start, marker_end)
    wb = extract_class_body(work_text, marker_start, marker_end)
    h = split_methods(hb)
    w = split_methods(wb)

    head_names = set(h)
    work_names = set(w)
    only_head = sorted(head_names - work_names)
    only_work = sorted(work_names - head_names)
    common = sorted(head_names & work_names)

    label = args.preset
    print(f"preset={label!r} - method count HEAD:", len(h), "WORK:", len(w))
    if only_head:
        print("ONLY in HEAD (missing in work):", only_head)
    if only_work:
        print("ONLY in work (missing in HEAD):", only_work)

    mismatches = []
    for name in common:
        if normalize(h[name]) != normalize(w[name]):
            mismatches.append(name)

    if mismatches:
        print("Methods with different bodies:", len(mismatches))
        for name in mismatches:
            print("  -", name)
    else:
        print("All", len(common), "shared methods: bodies match (normalized).")

    return 1 if only_head or only_work or mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
