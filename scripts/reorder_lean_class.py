#!/usr/bin/env python3
"""One-off: reorder `abstract class Lean` methods alphabetically (instance first, then static).

Syntax check (WAMP example):
    D:\\wamp64\\bin\\php\\php8.2.0\\php.exe -l php/parser/lean.php
"""
import re
from pathlib import Path

path = Path(__file__).resolve().parent.parent / "php" / "parser" / "lean.php"
text = path.read_text(encoding="utf-8")

marker_start = "abstract class Lean extends IndentedNode\n{"
marker_end = "\n}\n\nclass LeanCaret extends Lean"

si = text.index(marker_start) + len(marker_start)
ei = text.index(marker_end, si)
body = text[si:ei]

# Match method start: newline + 4 spaces + optional "public static " / "public " + "function " + name + (...)
# Do not require a newline after `)` so `function foo(...) {` on one line matches (e.g. __construct).
pat = re.compile(
    r"\n    ((?:public static |public |static )?function \w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)

matches = list(pat.finditer(body))
if not matches:
    raise SystemExit("no methods found")

preamble = body[: matches[0].start()]
methods = []
for i, m in enumerate(matches):
    sig_line = m.group(1)
    name_m = re.search(r"function (\w+)", sig_line)
    if not name_m:
        raise SystemExit(f"bad sig: {sig_line!r}")
    name = name_m.group(1)
    block = body[m.start() : matches[i + 1].start() if i + 1 < len(matches) else len(body)]
    is_static = "static function" in sig_line
    methods.append((name, is_static, block))

# Sort: instance first, then magic `__*` before other methods (ASCII `_` would mix them wrong if we
# only stripped underscores). Within non-magic names, strip `_` so `isProp` sorts before `is_space_separated`.
def _sort_key(item: tuple) -> tuple:
    name, is_static = item[0], item[1]
    if name.startswith("__"):
        sec = (0, name.lower())
    else:
        sec = (1, name.lower().replace("_", ""))
    return (is_static, sec)


methods.sort(key=_sort_key)

new_body = preamble + "".join(m[2] for m in methods)
new_text = text[:si] + new_body + text[ei:]
path.write_text(new_text, encoding="utf-8", newline="\n")
print("reordered", len(methods), "methods in abstract class Lean")
