import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Definition_5_1

/--
[padic_isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicField.lean)
-/
@[path]
lemma padic_isFractionRing
  {p : ℕ}
  [Fact p.Prime] :
-- imply
  IsFractionRing ℤ_[p] ℚ_[p] :=
-- proof
  PadicInt.isFractionRing

end Definition_5_1


-- created on 2026-10-23
