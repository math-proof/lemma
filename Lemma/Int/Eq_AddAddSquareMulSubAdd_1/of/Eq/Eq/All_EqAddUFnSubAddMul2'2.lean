import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.ManinSequence

open Int

/--
[eq_quadratic_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Eq_AddAddSquareMulSubAdd_1.of.Eq.Eq.All_EqAddUFnSubAddMul2'2.lean)
-/
@[path]
private lemma eq_quadratic_of_recurrence_eq
-- given
  (d : ℤ → ℤ) (q N : ℤ)
  (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
  (hzero : d 0 = q) (hnegOne : d (-1) = N) (n : ℤ) :
-- imply
  d n = n ^ 2 + (q + 1 - N) * n + q := by
-- proof
  apply Int.eq_quadratic_of_recurrence
  · exact hrec
  · exact hzero
  · exact hnegOne


/--
[sq_le_four_mul_of_quadratic_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Eq_AddAddSquareMulSubAdd_1.of.Eq.Eq.All_EqAddUFnSubAddMul2'2.lean)
-/
@[path]
private lemma sq_le_four_mul_of_quadratic_nonnegative_eq
-- given
  {a q : ℤ}
  (hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + a * n + q)
  (hnotTwoZeros : ∀ n : ℤ,
    n ^ 2 + a * n + q = 0 → (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) :
-- imply
  a ^ 2 ≤ 4 * q := by
-- proof
  apply Int.sq_le_four_mul_of_quadratic_nonnegative
  · exact hnonneg
  · exact hnotTwoZeros


/--
[hasse_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/Eq_AddAddSquareMulSubAdd_1.of.Eq.Eq.All_EqAddUFnSubAddMul2'2.lean)
-/
@[path]
private lemma hasse_bound_eq
-- given
  {q N : ℕ} (data : AlgebraicGeometry.EllipticCurve.ManinDegreeData q N) :
-- imply
  (((q : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (q : ℤ)) :=
-- proof
  AlgebraicGeometry.EllipticCurve.ManinDegreeData.hasse_bound data


-- created on 2026-10-09
