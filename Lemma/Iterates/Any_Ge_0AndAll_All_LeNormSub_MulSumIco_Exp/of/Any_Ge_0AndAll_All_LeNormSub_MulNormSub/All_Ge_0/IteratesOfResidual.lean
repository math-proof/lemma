import sympy.stats.iterates
import sympy.Basic
import Lemma.Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Real.Le_MulAddSum_ExpSum.of.In_Ico.All_Ge_0.All_Ge_0.All_Le_AddMulAdd1.Ge_0
open Finset Real


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
  (h₁ : ∀ n, 0 ≤ α n)
  (h₂ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ ω n m, ∀ i ∈ Ico n m,
    ‖x i ω - x n ω‖ ≤ (∑ k ∈ Ico n m, α k * C * (‖x n ω‖ + 1)) * exp (∑ j ∈ Ico n m, α j * C) := by
-- proof
  obtain ⟨C₁, hC₁, hg⟩ :=
    Real.Any_Ge_0AndAll_All_LeNorm_MulAddNorm1.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub h₂
  refine ⟨C₁ + 1, by positivity, fun ω n m i hi => ?_⟩
  have hstep : ∀ k ≥ n, ‖x (k + 1) ω - x n ω‖ ≤
      (1 + α k * (C₁ + 1)) * ‖x k ω - x n ω‖ + α k * (C₁ + 1) * (‖x n ω‖ + 1) := by
    intro k hk
    have hak := h₁ k
    rw [h₀.step]
    have e : x k ω + α k • (F (x k ω) (ω (k + 1)) - x k ω) - x n ω =
        (x k ω - x n ω) + α k • (F (x k ω) (ω (k + 1)) - x k ω) := by abel
    rw [e]
    have hF := hg (x k ω) (ω (k + 1))
    have hxk : ‖x k ω‖ ≤ ‖x n ω‖ + ‖x k ω - x n ω‖ := by
      calc ‖x k ω‖ = ‖x n ω + (x k ω - x n ω)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have hs : ‖α k • (F (x k ω) (ω (k + 1)) - x k ω)‖ ≤ α k * (C₁ * (‖x k ω‖ + 1) + ‖x k ω‖) := by
      rw [norm_smul, Real.norm_of_nonneg hak]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) hak
    have h₃ := mul_le_mul_of_nonneg_left hxk (mul_nonneg hak (by positivity : (0 : ℝ) ≤ C₁ + 1))
    calc _ ≤ ‖x k ω - x n ω‖ + ‖α k • (F (x k ω) (ω (k + 1)) - x k ω)‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith
  have h := Le_MulAddSum_ExpSum.of.In_Ico.All_Ge_0.All_Ge_0.All_Le_AddMulAdd1.Ge_0
    (u := fun k => ‖x k ω - x n ω‖) (b := fun k => α k * (C₁ + 1) * (‖x n ω‖ + 1))
    (c := fun k => α k * (C₁ + 1)) (n₀ := n) (n₁ := m) (by simp) hstep
    (fun k _ => by have := h₁ k; positivity) (fun k _ => by have := h₁ k; positivity) hi
  simpa using h


-- created on 2026-09-26