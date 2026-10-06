import Mathlib
import sympy.Basic


/--
[AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq.lean)
-/

private theorem mul_conj_eq_of_norm_eq {b : ℂ} {c : ℝ} (h2 : ‖b‖ = c) :
    b * starRingEnd ℂ b = (c : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2, Complex.ofReal_pow]

private theorem conj_eq_div_of_mul_conj_eq_of_mul_conj_eq {a b c : ℂ}
    (h1 : a * starRingEnd ℂ b = c * starRingEnd ℂ a) (h2 : b * starRingEnd ℂ b = c ^ 2)
    (hc : c ≠ 0) :
    b ≠ 0 ∧ starRingEnd ℂ a = c * (a / b) ∧ starRingEnd ℂ b = c ^ 2 * b⁻¹ := by
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h2
    exact hc (by simpa using h2.symm)
  refine ⟨hb, ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff hb]
    apply mul_left_cancel₀ hc
    calc c * (starRingEnd ℂ a * b) = c * starRingEnd ℂ a * b := by ring
      _ = a * starRingEnd ℂ b * b := by rw [h1]
      _ = a * (b * starRingEnd ℂ b) := by ring
      _ = a * c ^ 2 := by rw [h2]
      _ = c * (c * a) := by ring
  · rw [← div_eq_mul_inv, eq_div_iff hb, mul_comm (starRingEnd ℂ b) b]
    exact h2
@[main]
private lemma main
  {a b : ℂ}
  {c : ℝ}
-- given
  (hc : 0 < c)
  (h1 : a * starRingEnd ℂ b = (c : ℂ) * starRingEnd ℂ a)
  (h2 : ‖b‖ = c) :
-- imply
  starRingEnd ℂ a = (c : ℂ) * (a / b) ∧ starRingEnd ℂ b = (c : ℂ) ^ 2 * b⁻¹ :=
-- proof
  (conj_eq_div_of_mul_conj_eq_of_mul_conj_eq h1 (mul_conj_eq_of_norm_eq h2)
    (Complex.ofReal_ne_zero.mpr hc.ne')).2


-- created on 2026-10-05
