import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinSequence
open Int
open MathlibExt.AlgebraicGeometry.EllipticCurve
open ManinDegreeData


/--
[eq_quadratic_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
private lemma eq_quadratic_of_recurrence_eq
  {d : ℤ → ℤ}
  {q N n : ℤ}
-- given
  (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
  (hzero : d 0 = q)
  (hnegOne : d (-1) = N) :
-- imply
  d n = n ^ 2 + (q + 1 - N) * n + q := by
-- proof
  apply Int.eq_quadratic_of_recurrence d q N hrec hzero hnegOne n

/--
[sq_le_four_mul_of_quadratic_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
private lemma sq_le_four_mul_of_quadratic_nonnegative_eq
  {a q : ℤ}
-- given
  (hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + a * n + q)
  (hnotTwoZeros : ∀ n : ℤ, n ^ 2 + a * n + q = 0 → (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) :
-- imply
  a ^ 2 ≤ 4 * q := by
-- proof
  apply Int.sq_le_four_mul_of_quadratic_nonnegative hnonneg hnotTwoZeros

/--
[hasse_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean)
-/
@[path]
private lemma hasse_bound_eq
  {q N : ℕ}
  {data : ManinDegreeData q N} :
-- imply
  (((q : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (q : ℤ)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.hasse_bound data


-- created on 2026-10-20
