import Mathlib
import sympy.Basic
open Matrix


/--
[weak_duality_standard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/LP/WeakDualityStandard.lean)
-/
@[path]
lemma weak_duality_standard
  {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) ℝ}
  {b : Fin m → ℝ}
  {c : Fin n → ℝ}
  {x : Fin n → ℝ}
  {y : Fin m → ℝ}
-- given
  (hAx : A *ᵥ x = b)
  (hx : ∀ j, 0 ≤ x j)
  (hATy : ∀ j, c j ≤ (Aᵀ *ᵥ y) j) :
-- imply
  dotProduct c x ≤ dotProduct b y := by
-- proof
  calc dotProduct c x
    ≤ dotProduct (Aᵀ *ᵥ y) x := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hATy i) (hx i)
    _ = dotProduct y (A *ᵥ x) := by
      rw [dotProduct_comm (Aᵀ *ᵥ y) x, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        dotProduct_comm]
    _ = dotProduct y b := by rw [hAx]
    _ = dotProduct b y := dotProduct_comm y b


-- created on 2026-10-23
