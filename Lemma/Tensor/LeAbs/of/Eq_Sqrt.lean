import Mathlib.Analysis.InnerProductSpace.PiL2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {a b : EuclideanSpace ℝ (Fin n)}
-- given
  (h₀ : 0 < ∑ i : Fin n, a i ^ 2)
  (h₁ : 0 < ∑ i : Fin n, b i ^ 2) :
-- imply
  |∑ i : Fin n, a i * b i| / (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) ≤ 1 := by
-- proof
  have hab : |∑ i : Fin n, a i * b i| ≤ ‖a‖ * ‖b‖ := by
    simpa [PiLp.inner_apply, mul_comm] using abs_real_inner_le_norm a b
  have hnorm : ∀ (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Real.sq_sqrt
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
    have hineq : (∑ i : Fin n, a i * b i) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
      have : |∑ i : Fin n, a i * b i| ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hab 2
      simpa [sq_abs] using this
    refine le_trans hineq (le_of_eq ?_)
    rw [mul_pow, hnorm a, hnorm b]
  have hpos : 0 < Real.sqrt (∑ i : Fin n, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    mul_pos (Real.sqrt_pos.mpr h₀) (Real.sqrt_pos.mpr h₁)
  rw [div_le_one hpos]
  have hsq2 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt h₀), Real.sq_sqrt (le_of_lt h₁)]
    simpa [sq_abs] using hsq
  have habs : |∑ i : Fin n, a i * b i| ≤ |Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)| :=
    (sq_le_sq).1 hsq2
  simpa [abs_of_nonneg (le_of_lt hpos)] using habs


-- created on 2022-04-02
-- updated on 2026-10-26
