import sympy.functions.elementary.complexes
import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℂ} :
-- imply
  x ⬝ᵥ (fun i => ~(x i)) = ((√(∑ i, ‖x i‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
-- proof
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl


-- created on 2023-06-24
