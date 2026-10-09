import Mathlib.Data.Matrix.Mul
import sympy.sets.sets
import sympy.Basic
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ}
  {W : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  (x ᵥ* W) ⬝ᵥ y = (y ᵥ* Wᵀ) ⬝ᵥ x := by
-- proof
  rw [Matrix.vecMul_transpose, dotProduct_comm (W *ᵥ y), ← Matrix.dotProduct_mulVec]


-- created on 2021-01-04
