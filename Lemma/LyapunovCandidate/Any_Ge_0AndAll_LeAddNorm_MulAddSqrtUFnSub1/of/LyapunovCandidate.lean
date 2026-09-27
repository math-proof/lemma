import sympy.stats.lyapunov
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
  {a : ℝ}
-- given
  (h : LyapunovCandidate φ φ')
  (z : EuclideanVec d) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ + a ≤ C * (√(φ (x - z)) + 1) := by
-- proof
  obtain ⟨C, hC, hnorm⟩ := h.norm_le
  refine ⟨max C (a + ‖z‖), le_max_of_le_left hC, fun x => ?_⟩
  have h₂ : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := norm_le_insert' x z
  have h₃ := hnorm (x - z)
  have h₄ : C * √(φ (x - z)) ≤ max C (a + ‖z‖) * √(φ (x - z)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have h₅ : a + ‖z‖ ≤ max C (a + ‖z‖) := le_max_right _ _
  linarith


-- created on 2026-09-26