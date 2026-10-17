import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a b : EuclideanSpace ℝ (Fin n)} :
-- imply
  (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
-- proof
  have hab : |∑ i : Fin n, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    simpa [PiLp.inner_apply, mul_comm] using abs_real_inner_le_norm a b
  have hnorm : ∀ (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Real.sq_sqrt
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : (∑ i : Fin n, a i * b i) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    have : |∑ i : Fin n, a i * b i| ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hab 2
    simpa [sq_abs] using this
  refine le_trans hsq (le_of_eq ?_)
  rw [mul_pow, hnorm a, hnorm b]


-- created on 2026-10-11
-- updated on 2026-10-17
