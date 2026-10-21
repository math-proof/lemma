import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_product_approximation_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (x : Fin m → ℝ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (Q a : ℝ)
-- given
  (hQ : 0 < Q)
  (hcoord : ∀ h, |(q h : ℝ) - x h| ≤ Real.rpow Q (-a / r h)) :
-- imply
  ∀ l : RothMvIndex m,
    ∏ h, |(q h : ℝ) - x h| ^ l h ≤
      Real.rpow Q (-a * rothMvWeight r l) := by
-- proof
  intro l
  calc
    _ ≤ ∏ h, (Real.rpow Q (-a / r h)) ^ l h := by
      gcongr with h
      exact hcoord h
    _ = ∏ h, Real.rpow Q ((-a / r h) * (l h : ℝ)) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hQ.le _ _).symm
    _ = Real.rpow Q (∑ h, (-a / r h) * (l h : ℝ)) :=
      (Real.rpow_sum_of_pos hQ _ _).symm
    _ = Real.rpow Q (-a * rothMvWeight r l) := by
      congr 1
      unfold rothMvWeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring


-- created on 2026-10-21
