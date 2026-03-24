#!/usr/bin/env python3
"""Reorder methods in a `lean.php` class: alphabetic (instance first, static last).

Presets (see php/parser/README.md):
  lean            — abstract class Lean
  leancaret       — class LeanCaret
  leanlinecomment — class LeanLineComment (do not use on LeanToken: static $ between methods)

Syntax check (match http://localhost/info.php), e.g. WAMP PHP 8.0.x:
    "D:\\wamp64\\bin\\php\\php8.0.26\\php.exe" -l php/parser/lean.php
"""
import argparse
import re
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
    "leanlinecomment": (
        "class LeanLineComment extends Lean\n{",
        "\n}\n\nclass LeanBlockComment extends Lean",
    ),
}

pat = re.compile(
    r"\n    ((?:public static |public |static )?function \w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)


def _sort_key(item: tuple) -> tuple:
    name, is_static = item[0], item[1]
    if name.startswith("__"):
        sec = (0, name.lower())
    else:
        sec = (1, name.lower().replace("_", ""))
    return (is_static, sec)


def reorder_class(text: str, marker_start: str, marker_end: str) -> str:
    si = text.index(marker_start) + len(marker_start)
    ei = text.index(marker_end, si)
    body = text[si:ei]
    matches = list(pat.finditer(body))
    if not matches:
        raise ValueError("no methods found in class body")
    preamble = body[: matches[0].start()]
    methods = []
    for i, m in enumerate(matches):
        sig_line = m.group(1)
        name_m = re.search(r"function (\w+)", sig_line)
        if not name_m:
            raise ValueError(f"bad sig: {sig_line!r}")
        name = name_m.group(1)
        block = body[m.start() : matches[i + 1].start() if i + 1 < len(matches) else len(body)]
        is_static = "static function" in sig_line
        methods.append((name, is_static, block))
    methods.sort(key=_sort_key)
    new_body = preamble + "".join(m[2] for m in methods)
    return text[:si] + new_body + text[ei:]


def main() -> int:
    ap = argparse.ArgumentParser(description="Reorder methods in a lean.php class.")
    ap.add_argument(
        "preset",
        nargs="?",
        default="lean",
        choices=sorted(PRESETS.keys()),
        help="class block to reorder (default: lean)",
    )
    args = ap.parse_args()
    start, end = PRESETS[args.preset]
    text = LEAN.read_text(encoding="utf-8")
    new_text = reorder_class(text, start, end)
    LEAN.write_text(new_text, encoding="utf-8", newline="\n")
    # count methods
    body = new_text[new_text.index(start) + len(start) : new_text.index(end, new_text.index(start))]
    n = len(list(pat.finditer(body)))
    print(f"reordered preset={args.preset!r}: {n} methods in {LEAN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as e:
        print(e, file=sys.stderr)
        raise SystemExit(1)
