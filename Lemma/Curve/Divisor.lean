import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.Curve.Divisor

open CurveDivisor

/--
[coeff_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Divisor.lean)
-/
@[path]
private lemma coeff_single_eq
-- given
  (P : C) (n : ℤ) :
-- imply
  coeff (Finsupp.single P n) P = n := by
-- proof
  apply CurveDivisor.coeff_single


-- created on 2026-10-09
