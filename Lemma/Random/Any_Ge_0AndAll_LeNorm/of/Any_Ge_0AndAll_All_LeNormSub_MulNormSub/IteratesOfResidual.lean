import sympy.stats.iterates
import sympy.Basic
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S] [Nonempty S]
  {x : ℕ → (ℕ → S × S) → EuclideanVec d}
  {x₀ : EuclideanVec d}
  {α : ℕ → ℝ}
  {F : EuclideanVec d → S × S → EuclideanVec d}
-- given
  (h₀ : IteratesOfResidual x x₀ α F)
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  (n : ℕ) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ ω, ‖x n ω‖ ≤ C := by
-- proof
  obtain ⟨C₂, hC₂, hg⟩ :=
    Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub h₁
  induction n with
  | zero => exact ⟨‖x₀‖, norm_nonneg _, fun ω => by rw [h₀.init]⟩
  | succ n ih =>
    obtain ⟨C₁, hC₁, hx⟩ := ih
    refine ⟨C₁ + |α n| * (C₂ * (C₁ + 1) + C₁), by positivity, fun ω => ?_⟩
    rw [h₀.step]
    have hF : ‖F (x n ω) (ω (n + 1))‖ ≤ C₂ * (C₁ + 1) :=
      (hg _ _).trans (mul_le_mul_of_nonneg_left (by linarith [hx ω]) hC₂)
    calc _ ≤ ‖x n ω‖ + ‖α n • (F (x n ω) (ω (n + 1)) - x n ω)‖ := norm_add_le _ _
      _ ≤ C₁ + |α n| * (C₂ * (C₁ + 1) + C₁) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (hx ω)
          (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hF (hx ω))) (abs_nonneg _))


-- created on 2026-09-26