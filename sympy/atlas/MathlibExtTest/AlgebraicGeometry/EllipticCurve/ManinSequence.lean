/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinSequence.lean -/


import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinSequence

/-- The recurrence solver recovers a concrete quadratic sequence. -/
example (n : ℤ) :
    n ^ 2 + 3 * n + 5 = n ^ 2 + (5 + 1 - 3) * n + 5 := by
  apply Int.eq_quadratic_of_recurrence (d := fun m : ℤ ↦ m ^ 2 + 3 * m + 5)
  · intro m
    ring
  · norm_num
  · norm_num

/-- The discriminant bound applies to a concrete everywhere-positive quadratic. -/
example : (3 : ℤ) ^ 2 ≤ 4 * 5 := by
  exact Int.sq_le_four_mul_of_quadratic_nonnegative
    (a := 3) (q := 5) (by intro n; nlinarith [sq_nonneg (2 * n + 3)])
    (by intro n hn hn1; nlinarith)

/-- Concrete Manin degree data gives its discriminant bound. -/
example : ((1 : ℤ) + 1 - 2) ^ 2 ≤ 4 * 1 := by
  let data : MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 1 2 :=
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic
      1 2 0 (by norm_num) (by intro n; norm_num; positivity)
      (by intro n hn _; norm_num at hn; nlinarith [sq_nonneg n])
  exact data.hasse_bound

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinSequence
