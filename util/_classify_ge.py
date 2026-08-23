"""Propose sections for remaining Algebra.Ge/Gt/Given lemmas from path rules."""
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
        mods.append(m)


def section(m: str) -> str:
    if m.startswith("Given"):
        return "Bool"
    if any(s in m for s in ("Floor", "Ceil", "Abs", "Frac")):
        return "Int"
    if any(s in m for s in ("Maxima", "Minima", "Inf", "Sup", "Log", "Sqrt")):
        return "Real"
    if "GeExp" in m or "GtExp" in m or m.endswith(".Exp") or ".Exp." in m:
        return "Real"
    if any(s in m for s in ("Div", "Inv")):
        return "Rat"
    if "scale.negative" in m or "strengthen.minus" in m:
        return "Int"
    if "scale.positive" in m:
        return "Rat"
    if "Block" in m:
        return "Tensor"
    if ".Sum" in m or m.startswith("GeSum") or m.startswith("GtSum") or "Ge_0.Sum" in m:
        return "Finset"
    if "Prod" in m:
        return "Finset"
    if "ReducedSum" in m:
        return "Tensor"
    if ("Lt_0" in m or "Le_0" in m) and any(s in m for s in ("Mul", "Square", "Le_0.Le_0", "Lt_0.Lt_0")):
        return "Int"
    if "Sub" in m:
        return "Int"
    return "Nat"


for m in sorted(mods, key=lambda x: (-x.count("."), x)):
    print(f"Algebra.{m} {section(m)}.{m}")
