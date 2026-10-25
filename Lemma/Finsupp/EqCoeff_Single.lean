import Mathlib
import sympy.Basic
import Def.AlgebraicGeometry.Curve.Divisor
open CurveDivisor


/--
[coeff_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Divisor.lean)
-/
@[path]
private lemma main
-- given
  (P : C) (n : ℤ) :
-- imply
  coeff (Finsupp.single P n) P = n := by
-- proof
  classical
  simp [coeff]


-- created on 2026-10-09
-- updated on 2026-10-24
