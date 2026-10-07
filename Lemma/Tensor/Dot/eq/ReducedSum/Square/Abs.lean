import sympy.functions.elementary.complexes
import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℂ} :
-- imply
  x ⬝ᵥ (fun i => ~(x i)) = ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
-- proof
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]


-- created on 2023-06-23
