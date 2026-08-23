"""Propose sections for remaining Algebra lemmas (not Ge/Gt/Given)."""
from pathlib import Path

root = Path("Lemma/Algebra")
mods = []
for p in root.rglob("*.py"):
    text = p.read_text(encoding="utf-8", errors="ignore")
    if "@apply" not in text:
        continue
    rel = p.relative_to(root)
    parts = list(rel.parts[:-1]) if rel.name == "__init__.py" else list(rel.with_suffix("").parts)
    m = ".".join(parts)
    if m.startswith(("Ge", "Gt", "Given")):
        continue
    mods.append(m)


def tokens(m: str) -> set[str]:
    return set(m.split("."))


def section(m: str) -> str:
    t = tokens(m)
    if m.startswith(("Iff", "Or", "Or_", "OrAny")):
        if t & {"Abs", "Floor", "Ceil", "GeAbs", "GtAbs", "Eq_Abs"}:
            return "Int"
        if t & {"Div", "Inv"}:
            return "Rat"
        if t & {"Log", "Exp", "Sqrt"}:
            return "Real"
        return "Bool"
    if t & {"Im", "Re", "Conj"} or m.startswith("Im.") or m.startswith("Re."):
        return "Complex"
    if m.startswith(("Inf", "Sup", "Maxima", "Minima", "Log")):
        return "Real"
    if m.startswith(("Prod", "LeProd", "LtProd", "LeSum", "LtSum")) or "Prod" in t:
        return "Finset"
    if any(s in m for s in ("Reduced", "Block", "Slice", "Transpose", "Matrix")):
        return "Tensor"
    if t & {"Maxima", "Minima", "Integral", "Inf", "Sup", "Log", "Exp", "Sqrt"}:
        return "Real"
    if m.startswith("Inv") or "InvAdd" in m:
        return "Rat"
    if any(s in m for s in ("LeInf", "LeSup", "LeMaxima", "LeMinima", "LeExp", "LeLog", "LeSqrt", "LeIntegral")):
        return "Real"
    if any(s in m for s in ("LtMaxima", "LtMinima", "LtExp", "LtLog", "LtSqrt", "LtIntegral", "Lt_Maxima")):
        return "Real"
    if any(s in m for s in ("Floor", "Ceil", "Abs", "Frac", "Mod", "Sign")):
        return "Int"
    if "scale.negative" in m or "strengthen.minus" in m:
        return "Int"
    if "scale.positive" in m:
        return "Rat"
    if t & {"Div", "Inv"} or "DivSum" in m or "DivSquare" in m:
        return "Rat"
    if m.startswith(("Prod", "LeProd", "LtProd", "LeSum", "LtSum")) or "Prod" in t:
        return "Finset"
    if any(s in m for s in (".Sum", "LeSum", "LtSum", "Pow.Sum", "Mul.Sum")):
        return "Finset"
    if m.startswith(("One", "Zero")):
        return "Tensor"
    if "NeMatrix" in m or "Square.Norm" in m:
        return "Tensor"
    if m.startswith("Sqrt"):
        return "Real"
    if "Neg" in m and m.startswith(("Mul", "Pow", "Square")):
        return "Int"
    if m.startswith("Subs"):
        return "Bool"
    if "quadratic" in m:
        return "Rat"
    if ("Lt_0" in m or "Le_0" in m) and any(s in m for s in ("Mul", "Square")):
        return "Int"
    if m.startswith(("LtSub", "Sub.")):
        return "Int"
    return "Nat"


for m in sorted(mods, key=lambda x: (-x.count("."), x)):
    print(f"Algebra.{m} {section(m)}.{m}")
