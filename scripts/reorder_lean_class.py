#!/usr/bin/env python3
"""Reorder methods in a `lean.php` class: alphabetic (instance first, static last).

Presets (see php/parser/README.md):
  lean            — abstract class Lean
  leancaret       — class LeanCaret
  leanlinecomment — class LeanLineComment
  leanblockcomment — class LeanBlockComment
  leandocstring   — class LeanDocString
  leanargs        — abstract class LeanArgs
  leanunary       — abstract class LeanUnary
  leanpairedgroup — abstract class LeanPairedGroup
  leanparenthesis — class LeanParenthesis
  leananglebracket — class LeanAngleBracket
  leanbracket     — class LeanBracket
  leanbrace       — class LeanBrace
  leanabs         — class LeanAbs
  leandoubleanglequotation — class LeanDoubleAngleQuotation
  leanbinary      — abstract class LeanBinary
  leanproperty    — class LeanProperty
  leancolon       — class LeanColon
  leanassign      — class LeanAssign
  leanbinaryboolean — abstract class LeanBinaryBoolean (members-first: use + methods)
  leanrelational  — abstract class LeanRelational
  leanarithmetic  — abstract class LeanArithmetic
  leanmul         — class LeanMul
  leanneg         — class LeanNeg
  leanplus        — class LeanPlus
  leaninv         — class LeanInv
  leanpospart     — class LeanPosPart
  leannegpart     — class LeanNegPart
  leansqrt        — class Lean_sqrt
  leansquare      — class LeanSquare
  leancubicroot   — class LeanCubicRoot
  leanuparrow     — class Lean_uparrow
  leanuparrowuc   — class LeanUparrow
  leancube        — class LeanCube
  leanquarticroot — class LeanQuarticRoot
  leantesseract   — class LeanTesseract
  leantranspose   — class LeanTranspose
  leanpipeforward — class LeanPipeForward
  leanmethodchaining — class LeanMethodChaining
  leangotelem     — class LeanGetElem (members-first: use + methods)
  leangotelemque  — class LeanGetElemQue (members-first)
  leangotelemquote — class LeanGetElemQuote (members-first)
  leanis          — class Lean_is
  leanisnot       — class Lean_is_not
  leanlogicand    — class LeanLogicAnd
  leanlogicor     — class LeanLogicOr
  leanlogicxor    — class LeanLogicXor
  leanlor         — class Lean_lor
  leanstatements  — class LeanStatements (members-first: use + methods)
  leancommand     — abstract class LeanCommand
  leanimport      — class Lean_import
  leanopen        — class Lean_open
  leansetoption   — class Lean_set_option
  leanbar         — class LeanBar
  leanRightarrow  — class LeanRightarrow
  leanrightarrow  — class Lean_rightarrow
  leanmapsto      — class Lean_mapsto
  leanleftarrow   — class Lean_leftarrow
  leanlnot        — class Lean_lnot (members-first: use + methods)
  leannot         — class LeanNot (members-first)
  leanmatch       — class Lean_match
  leanite         — class LeanIte
  leandiv         — class LeanDiv
  leanbitor       — class LeanBitOr
  leantoken       — class LeanToken (data members first, then sorted methods)

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
    "leanbrace": (
        "class LeanBrace extends LeanPairedGroup\n{",
        "\n}\n\nclass LeanAbs extends LeanPairedGroup",
    ),
    "leanabs": (
        "class LeanAbs extends LeanPairedGroup\n{",
        "\n}\n\nclass LeanNorm extends LeanPairedGroup",
    ),
    "leandoubleanglequotation": (
        "class LeanDoubleAngleQuotation extends LeanPairedGroup\n{",
        "\n}\n\nabstract class LeanBinary extends LeanArgs",
    ),
    "leanbinary": (
        "abstract class LeanBinary extends LeanArgs\n{",
        "\n}\n\nclass LeanProperty extends LeanBinary",
    ),
    "leanproperty": (
        "class LeanProperty extends LeanBinary\n{",
        "\n}\n\nclass LeanColon extends LeanBinary",
    ),
    "leancolon": (
        "class LeanColon extends LeanBinary\n{",
        "\n}\n\nclass LeanAssign extends LeanBinary",
    ),
    "leanassign": (
        "class LeanAssign extends LeanBinary\n{",
        "\n}\n\ntrait LeanProp",
    ),
    "leanbinaryboolean": (
        "abstract class LeanBinaryBoolean extends LeanBinary\n{",
        "\n}\n\nabstract class LeanRelational extends LeanBinaryBoolean",
    ),
    "leanrelational": (
        "abstract class LeanRelational extends LeanBinaryBoolean\n{",
        "\n}\n\n\nclass Lean_gt extends LeanRelational",
    ),
    "leanarithmetic": (
        "abstract class LeanArithmetic extends LeanBinary\n{",
        "\n}\n\n\nclass LeanAdd extends LeanArithmetic",
    ),
    "leanmul": (
        "class LeanMul extends LeanArithmetic\n{",
        "\n}\n\n\nclass Lean_times extends LeanArithmetic",
    ),
    "leanneg": (
        "class LeanNeg extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanPlus extends LeanUnaryArithmeticPre",
    ),
    "leanplus": (
        "class LeanPlus extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanInv extends LeanUnaryArithmeticPost",
    ),
    "leaninv": (
        "class LeanInv extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanPosPart extends LeanUnaryArithmeticPost",
    ),
    "leanpospart": (
        "class LeanPosPart extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanNegPart extends LeanUnaryArithmeticPost",
    ),
    "leannegpart": (
        "class LeanNegPart extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass Lean_sqrt extends LeanUnaryArithmeticPre",
    ),
    "leansqrt": (
        "class Lean_sqrt extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanSquare extends LeanUnaryArithmeticPost",
    ),
    "leansquare": (
        "class LeanSquare extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanCubicRoot extends LeanUnaryArithmeticPre",
    ),
    "leancubicroot": (
        "class LeanCubicRoot extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass Lean_uparrow extends LeanUnaryArithmeticPre",
    ),
    "leanuparrow": (
        "class Lean_uparrow extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanUparrow extends LeanUnaryArithmeticPre",
    ),
    "leanuparrowuc": (
        "class LeanUparrow extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanCube extends LeanUnaryArithmeticPost",
    ),
    "leancube": (
        "class LeanCube extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanQuarticRoot extends LeanUnaryArithmeticPre",
    ),
    "leanquarticroot": (
        "class LeanQuarticRoot extends LeanUnaryArithmeticPre\n{",
        "\n}\n\nclass LeanTesseract extends LeanUnaryArithmeticPost",
    ),
    "leantesseract": (
        "class LeanTesseract extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanTranspose extends LeanUnaryArithmeticPost",
    ),
    "leantranspose": (
        "class LeanTranspose extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanPipeForward extends LeanUnaryArithmeticPost",
    ),
    "leanpipeforward": (
        "class LeanPipeForward extends LeanUnaryArithmeticPost\n{",
        "\n}\n\nclass LeanMethodChaining extends LeanBinary",
    ),
    "leanmethodchaining": (
        "class LeanMethodChaining extends LeanBinary\n{",
        "\n}\n\ntrait LeanGetElemBase",
    ),
    "leangotelem": (
        "class LeanGetElem extends LeanBinary\n{",
        "\n}\n\nclass LeanGetElemQue extends LeanBinary",
    ),
    "leangotelemque": (
        "class LeanGetElemQue extends LeanBinary\n{",
        "\n}\n\nclass LeanGetElemQuote extends LeanArgs",
    ),
    "leangotelemquote": (
        "class LeanGetElemQuote extends LeanArgs\n{",
        "\n}\n\nclass Lean_is extends LeanBinary",
    ),
    "leanis": (
        "class Lean_is extends LeanBinary\n{",
        "\n}\n\nclass Lean_is_not extends LeanBinary",
    ),
    "leanisnot": (
        "class Lean_is_not extends LeanBinary\n{",
        "\n}\n\nabstract class LeanSetOperator extends LeanBinary {",
    ),
    "leanlogicand": (
        "class LeanLogicAnd extends LeanLogic\n{",
        "\n}\n\n\nclass LeanLogicOr extends LeanLogic",
    ),
    "leanlogicor": (
        "class LeanLogicOr extends LeanLogic\n{",
        "\n}\n\nclass LeanLogicXor extends LeanLogic",
    ),
    "leanlogicxor": (
        "class LeanLogicXor extends LeanLogic\n{",
        "\n}\n\n\nclass Lean_lor extends LeanLogic",
    ),
    "leanlor": (
        "class Lean_lor extends LeanLogic\n{",
        "\n}\n\nclass Lean_land extends LeanLogic",
    ),
    "leanstatements": (
        "class LeanStatements extends LeanArgs\n{",
        "\n}\n\n\nclass LeanModule extends LeanStatements",
    ),
    "leancommand": (
        "abstract class LeanCommand extends LeanUnary\n{",
        "\n}\n\nclass Lean_import extends LeanCommand",
    ),
    "leanimport": (
        "class Lean_import extends LeanCommand\n{",
        "\n}\n\nclass Lean_open extends LeanCommand",
    ),
    "leanopen": (
        "class Lean_open extends LeanCommand\n{",
        "\n}\n\nclass Lean_set_option extends LeanCommand",
    ),
    "leansetoption": (
        "class Lean_set_option extends LeanCommand\n{",
        "\n}\n\nclass Lean_namespace extends LeanCommand",
    ),
    "leanbar": (
        "class LeanBar extends LeanUnary\n{",
        "\n}\n\nclass LeanRightarrow extends LeanBinary",
    ),
    "leanRightarrow": (
        "class LeanRightarrow extends LeanBinary\n{",
        "\n}\n\nclass Lean_rightarrow extends LeanBinary",
    ),
    "leanrightarrow": (
        "class Lean_rightarrow extends LeanBinary\n{",
        "\n}\n\nclass Lean_mapsto extends LeanBinary",
    ),
    "leanmapsto": (
        "class Lean_mapsto extends LeanBinary\n{",
        "\n}\n\nclass Lean_leftarrow extends LeanUnary",
    ),
    "leanleftarrow": (
        "class Lean_leftarrow extends LeanUnary\n{",
        "\n}\n\nclass Lean_lnot extends LeanUnary",
    ),
    "leanlnot": (
        "class Lean_lnot extends LeanUnary\n{",
        "\n}\n\nclass LeanNot extends LeanUnary",
    ),
    "leannot": (
        "class LeanNot extends LeanUnary\n{",
        "\n}\n\nclass Lean_match extends LeanArgs",
    ),
    "leanmatch": (
        "class Lean_match extends LeanArgs\n{",
        "\n}\n\nclass LeanIte extends LeanArgs",
    ),
    "leanite": (
        "class LeanIte extends LeanArgs\n{",
        "\n}\n\nclass LeanArgsSpaceSeparated extends LeanArgs",
    ),
    "leandiv": (
        "class LeanDiv extends LeanArithmetic\n{",
        "\n}\n\nclass LeanFDiv extends LeanArithmetic",
    ),
    "leanbitor": (
        "class LeanBitOr extends LeanArithmetic\n{",
        "\n}\n\nclass LeanBitwiseOr extends LeanArithmetic",
    ),
    "leantoken": (
        "class LeanToken extends Lean\n{",
        "\n}\n\nLeanToken::$subscript_keys",
    ),
}

# Presets that use reorder_class_members_first (properties + use lines, then sorted methods).
MEMBERS_FIRST_PRESETS = frozenset(
    {
        "leanbinaryboolean",
        "leangotelem",
        "leangotelemque",
        "leangotelemquote",
        "leanlnot",
        "leannot",
        "leanstatements",
        "leantoken",
    }
)

pat = re.compile(
    r"\n    ((?:abstract )?(?:public static |static public |public |static )?function \w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)

# Top-level class member starts (4-space indent); splits properties from methods.
MEMBER_HEAD = re.compile(
    r"\n    (?:"
    r"(?:public|protected|private)\s+function\s+\w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?"
    r"|(?:public\s+)?static\s+function\s+\w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?"
    r"|static\s+public\s+function\s+\w+\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?"
    r"|(?:public|protected|private)\s+\$\w+"
    r"|static\s+\$\w+"
    r"|use\s+[\w\\]+(?:\s*,\s*[\w\\]+)*\s*;"
    r")"
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
        is_static = "public static function" in sig_line or "static public function" in sig_line
        methods.append((name, is_static, block))
    methods.sort(key=_sort_key)
    new_body = preamble + "".join(m[2] for m in methods)
    return text[:si] + new_body + text[ei:]


def _is_method_segment(seg: str) -> bool:
    return re.search(r"\n    .+function\s+\w+\s*\(", seg) is not None


def _method_meta(seg: str) -> tuple[str, bool]:
    name_m = re.search(r"function\s+(\w+)\s*\(", seg)
    if not name_m:
        raise ValueError(f"method segment without function name: {seg[:80]!r}")
    name = name_m.group(1)
    is_static = bool(
        re.search(
            r"\n    (?:(?:public\s+)?static\s+function|static\s+public\s+function)\s+\w+",
            seg,
        )
    )
    return name, is_static


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


def reorder_class_members_first(text: str, marker_start: str, marker_end: str) -> str:
    """All data members (properties) first, preserving their relative order; then methods sorted."""
    si = text.index(marker_start) + len(marker_start)
    ei = text.index(marker_end, si)
    body = text[si:ei]
    preamble, segments = _declaration_segments(body)
    member_parts: list[str] = [preamble]
    methods: list[tuple[str, bool, str]] = []
    for seg in segments:
        if _is_method_segment(seg):
            name, is_static = _method_meta(seg)
            methods.append((name, is_static, seg))
        else:
            member_parts.append(seg)
    if not methods:
        raise ValueError("no methods found after splitting members")
    methods.sort(key=_sort_key)
    new_body = "".join(member_parts) + "".join(m[2] for m in methods)
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
    if args.preset in MEMBERS_FIRST_PRESETS:
        new_text = reorder_class_members_first(text, start, end)
    else:
        new_text = reorder_class(text, start, end)
    LEAN.write_text(new_text, encoding="utf-8", newline="\n")
    # count methods
    body = new_text[new_text.index(start) + len(start) : new_text.index(end, new_text.index(start))]
    if args.preset in MEMBERS_FIRST_PRESETS:
        _, segs = _declaration_segments(body)
        n = sum(1 for seg in segs if _is_method_segment(seg))
    else:
        n = len(list(pat.finditer(body)))
    print(f"reordered preset={args.preset!r}: {n} methods in {LEAN.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as e:
        print(e, file=sys.stderr)
        raise SystemExit(1)
