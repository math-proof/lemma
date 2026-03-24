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
    "leanlogic": (
        "abstract class LeanLogic extends LeanBinaryBoolean\n{",
        "\n}\n\n\nclass LeanLogicAnd extends LeanLogic",
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
    "leanargsspaceseparated": (
        "class LeanArgsSpaceSeparated extends LeanArgs\n{",
        "\n}\n\nclass LeanArgsNewLineSeparated extends LeanArgs",
    ),
    "leanargsnewlineseparated": (
        "class LeanArgsNewLineSeparated extends LeanArgs\n{",
        "\n}\n\nclass LeanArgsIndented extends LeanBinary",
    ),
    "leanargsindented": (
        "class LeanArgsIndented extends LeanBinary\n{",
        "\n}\n\nclass LeanArgsCommaSeparated extends LeanArgs",
    ),
    "leanargscommaseparated": (
        "class LeanArgsCommaSeparated extends LeanArgs\n{",
        "\n}\n\nclass LeanArgsSemicolonSeparated extends LeanArgs",
    ),
    "leanargssemicolonseparated": (
        "class LeanArgsSemicolonSeparated extends LeanArgs\n{",
        "\n}\n\nclass LeanArgsCommaNewLineSeparated extends LeanArgs",
    ),
    "leanargscommanewlineseparated": (
        "class LeanArgsCommaNewLineSeparated extends LeanArgs\n{",
        "\n}\n\nabstract class LeanSyntax extends LeanArgs",
    ),
    "leantactic": (
        "class LeanTactic extends LeanSyntax\n{",
        "\n}\n\nclass LeanBy extends LeanUnary",
    ),
    "leanby": (
        "class LeanBy extends LeanUnary\n{",
        "\n}\n\nclass LeanFrom extends LeanUnary",
    ),
    "leanfrom": (
        "class LeanFrom extends LeanUnary\n{",
        "\n}\n\nclass LeanCalc extends LeanUnary",
    ),
    "leancalc": (
        "class LeanCalc extends LeanUnary\n{",
        "\n}\n\n\nclass LeanMOD extends LeanUnary",
    ),
    "leanmod": (
        "class LeanMOD extends LeanUnary\n{",
        "\n}\n\n\nclass LeanUsing extends LeanUnary",
    ),
    "leanusing": (
        "class LeanUsing extends LeanUnary\n{",
        "\n}\n\nclass LeanAt extends LeanUnary",
    ),
    "leanat": (
        "class LeanAt extends LeanUnary\n{",
        "\n}\n\nclass LeanIn extends LeanUnary",
    ),
    "leanin": (
        "class LeanIn extends LeanUnary\n{",
        "\n}\n\nclass LeanGeneralizing extends LeanUnary",
    ),
    "leangeneralizing": (
        "class LeanGeneralizing extends LeanUnary\n{",
        "\n}\n\nclass LeanSequentialTacticCombinator extends LeanUnary",
    ),
    "leansequentialtacticcombinator": (
        "class LeanSequentialTacticCombinator extends LeanUnary\n{",
        "\n}\n\nclass LeanTacticBlock extends LeanUnary",
    ),
    "leantacticblock": (
        "class LeanTacticBlock extends LeanUnary\n{",
        "\n}\n\n\nclass LeanWith extends LeanArgs",
    ),
    "leanwith": (
        "class LeanWith extends LeanArgs\n{",
        "\n}\n\nclass LeanAttribute extends LeanUnary",
    ),
    "leanattribute": (
        "class LeanAttribute extends LeanUnary\n{",
        "\n}\n\nclass Lean_def extends LeanArgs",
    ),
    "lean_def": (
        "class Lean_def extends LeanArgs\n{",
        "\n}\n\nclass Lean_theorem extends Lean_def {}",
    ),
    "lean_lemma": (
        "class Lean_lemma extends Lean_def\n{",
        "\n}\n\nclass Lean_let extends LeanSyntax",
    ),
    "leanlet": (
        "class Lean_let extends LeanSyntax\n{",
        "\n}\n\nclass Lean_have extends Lean_let",
    ),
    "leanhave": (
        "class Lean_have extends Lean_let\n{",
        "\n}\n\n\nclass Lean_show extends LeanSyntax",
    ),
    "leanshow": (
        "class Lean_show extends LeanSyntax\n{",
        "\n}\n\nclass Lean_fun extends LeanUnary",
    ),
    "lean_fun": (
        "class Lean_fun extends LeanUnary\n{",
        "\n}\n\nclass LbigOperator extends LeanArgs",
    ),
    "lbigoperator": (
        "class LbigOperator extends LeanArgs\n{",
        "\n}\n\n\nclass LeanQuantifier extends LbigOperator",
    ),
    "leanquantifier": (
        "class LeanQuantifier extends LbigOperator\n{",
        "\n}\n\n\n// universal quantifier\nclass Lean_forall extends LeanQuantifier",
    ),
    "leanforall": (
        "class Lean_forall extends LeanQuantifier\n{",
        "\n}\n\n// existential quantifier\nclass Lean_exists extends LeanQuantifier",
    ),
    "leanexists": (
        "class Lean_exists extends LeanQuantifier\n{",
        "\n}\n\n\nclass Lean_sum extends LbigOperator",
    ),
    "leansum": (
        "class Lean_sum extends LbigOperator\n{",
        "\n}\n\nclass Lean_prod extends LbigOperator",
    ),
    "leanprod": (
        "class Lean_prod extends LbigOperator\n{",
        "\n}\n\nclass Lean_bigcap extends LbigOperator",
    ),
    "leanbigcap": (
        "class Lean_bigcap extends LbigOperator\n{",
        "\n}\n\nclass Lean_bigcup extends LbigOperator",
    ),
    "leanbigcup": (
        "class Lean_bigcup extends LbigOperator\n{",
        "\n}\n\nclass LeanStack extends LbigOperator",
    ),
    "leanstack": (
        "class LeanStack extends LbigOperator\n{",
        "\n}\n\nfunction compile($code) {",
    ),
    "leanparser": (
        "class LeanParser extends AbstractParser {\n",
        "\n}\n\nLeanParser::$instance = new LeanParser();",
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

SIG_RE = re.compile(
    r"\n    ((?:abstract )?(?:public static |static public |public |static )?function (\w+)\([^)]*\)(?:\s*:\s*\??[\w\\|]+)?)",
    re.MULTILINE,
)

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


SEGMENT_SPLIT_PRESETS = frozenset(
    {
        "leanbinaryboolean",
        "leangotelem",
        "leangotelemque",
        "leangotelemquote",
        "leanlnot",
        "leannot",
        "leanargsnewlineseparated",
        "leanargscommanewlineseparated",
        "leanstatements",
        "leantactic",
        "leansequentialtacticcombinator",
        "lean_fun",
        "leanquantifier",
        "leantoken",
    }
)


def split_methods(body: str, preset: str) -> dict[str, str]:
    if preset in SEGMENT_SPLIT_PRESETS:
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
