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
    "leanlinecomment": (
        "class LeanLineComment extends Lean\n{",
        "\n}\n\nclass LeanBlockComment extends Lean",
    ),
    "leanblockcomment": (
        "class LeanBlockComment extends Lean\n{",
        "\n}\n\nclass LeanDocString extends LeanBlockComment",
    ),
    "leandocstring": (
        "class LeanDocString extends LeanBlockComment\n{",
        "\n}\n\n\ntrait LeanMultipleLine",
    ),
    "leanargs": (
        "abstract class LeanArgs extends Lean\n{",
        "\n}\n\n# Frac|Abs|Norm|Length|Sign|Square|Sqrt|Floor|Ceil|Sin|Cos|Tan|Cot|Arg|Neg|Inv|Cast|Coe|Exp|Log|Val|Card|ToNat|Arccos|Arcsin|Arctan|Arccot|Re|Im|Succ",
    ),
    "leanunary": (
        "abstract class LeanUnary extends LeanArgs\n{",
        "\n}\n\nabstract class LeanPairedGroup extends LeanUnary",
    ),
    "leanpairedgroup": (
        "abstract class LeanPairedGroup extends LeanUnary\n{",
        "\n}\n\nclass LeanParenthesis extends LeanPairedGroup",
    ),
    "leanparenthesis": (
        "class LeanParenthesis extends LeanPairedGroup\n{",
        "\n}\n\nclass LeanAngleBracket extends LeanPairedGroup",
    ),
    "leananglebracket": (
        "class LeanAngleBracket extends LeanPairedGroup\n{",
        "\n}\n\nclass LeanBracket extends LeanPairedGroup",
    ),
    "leanbracket": (
        "class LeanBracket extends LeanPairedGroup\n{",
        "\n}\n\nclass LeanBrace extends LeanPairedGroup",
    ),
    "leantoken": (
        "class LeanToken extends Lean\n{",
        "\n}\n\nLeanToken::$subscript_keys",
    ),
}

SIG_RE = re.compile(
    r"\n    ((?:public static |public |static )?function (\w+)\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)

MEMBER_HEAD = re.compile(
    r"\n    (?:"
    r"(?:public|protected|private)\s+function\s+\w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?"
    r"|(?:public\s+)?static\s+function\s+\w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?"
    r"|(?:public|protected|private)\s+\$\w+"
    r"|static\s+\$\w+"
    r")"
)


def extract_class_body(text: str, marker_start: str, marker_end: str) -> str:
    si = text.index(marker_start) + len(marker_start)
    ei = text.index(marker_end, si)
    return text[si:ei]


def _is_method_segment(seg: str) -> bool:
    return re.search(r"\n    .+function\s+\w+\s*\(", seg) is not None


def _declaration_segments(body: str) -> tuple[str, list[str]]:
    heads = list(MEMBER_HEAD.finditer(body))
    if not heads:
        raise ValueError("no class members found (MEMBER_HEAD)")
    preamble = body[: heads[0].start()]
    segments: list[str] = []
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(body)
        segments.append(body[m.start() : end])
    return preamble, segments


def split_methods(body: str, preset: str) -> dict[str, str]:
    if preset == "leantoken":
        _, segments = _declaration_segments(body)
        out: dict[str, str] = {}
        for seg in segments:
            if not _is_method_segment(seg):
                continue
            name_m = re.search(r"function\s+(\w+)\s*\(", seg)
            if not name_m:
                continue
            name = name_m.group(1)
            if name in out:
                print(f"WARNING: duplicate method {name!r}", file=sys.stderr)
            out[name] = seg
        return out
    matches = list(SIG_RE.finditer(body))
    out = {}
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
    h = split_methods(hb, args.preset)
    w = split_methods(wb, args.preset)

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
