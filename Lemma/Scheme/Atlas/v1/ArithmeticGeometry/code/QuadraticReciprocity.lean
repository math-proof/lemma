import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[quadratic_reciprocity_gauss](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticReciprocity.lean)
-/
@[path]
lemma quadratic_reciprocity_gauss
  {p q : ℕ}
  [Fact p.Prime]
  [Fact q.Prime]
-- given
  (hp : p ≠ 2)
  (hq : q ≠ 2)
  (hpq : p ≠ q) :
-- imply
  legendreSym q (p : ℤ) * legendreSym p (q : ℤ) = (-1) ^ (p / 2 * (q / 2)) :=
-- proof
  legendreSym.quadratic_reciprocity hp hq hpq


-- created on 2026-10-23
