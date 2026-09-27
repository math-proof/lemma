import sympy.stats.iterates
import sympy.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
open Filter MeasureTheory


@[main]
private lemma main
  {d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {x e₁ e₂ : ℕ → Ω → EuclideanVec d}
  {x₀ : EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {α : ℕ → ℝ}
-- given
  (h₀ : Iterates x x₀ f e₁ e₂ α)
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1))
  (h₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₂ (n + 1) ω‖ ≤ C * α n ^ 2 * (‖x n ω‖ + 1))
  (h₃ : ∃ L, LipschitzWith L f)
  (h₄ : ∀ n, 0 < α n)
  (n : ℕ) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ‖x n ω‖ ≤ C := by
-- proof
  obtain ⟨L, hL⟩ := h₃
  obtain ⟨C₁, hC₁, he₁⟩ := h₁
  obtain ⟨C₂, hC₂, he₂⟩ := h₂
  induction n with
  | zero => exact ⟨‖x₀‖, norm_nonneg _, Eventually.of_forall fun ω => by rw [h₀.init]⟩
  | succ n ih =>
    obtain ⟨C₃, hC₃, hx⟩ := ih
    have hα := h₄ n
    refine ⟨C₃ + α n * (L * C₃ + ‖f 0‖ + C₃) + C₁ * α n * (C₃ + 1) + C₂ * α n ^ 2 * (C₃ + 1),
      by positivity, ?_⟩
    filter_upwards [he₁, he₂, hx] with ω h₁ h₂ h₃
    have hf : ‖f (x n ω)‖ ≤ L * C₃ + ‖f 0‖ := by
      have h := hL.norm_sub_le (x n ω) 0
      rw [sub_zero] at h
      calc ‖f (x n ω)‖ ≤ ‖f (x n ω) - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
        _ ≤ L * ‖x n ω‖ + ‖f 0‖ := by linarith
        _ ≤ L * C₃ + ‖f 0‖ := by gcongr
    have hstep : ‖α n • (f (x n ω) - x n ω)‖ ≤ α n * (L * C₃ + ‖f 0‖ + C₃) := by
      rw [norm_smul, Real.norm_of_nonneg hα.le]
      gcongr
      exact (norm_sub_le _ _).trans (by linarith)
    have he₁' : ‖e₁ (n + 1) ω‖ ≤ C₁ * α n * (C₃ + 1) := (h₁ n).trans (by gcongr)
    have he₂' : ‖e₂ (n + 1) ω‖ ≤ C₂ * α n ^ 2 * (C₃ + 1) := (h₂ n).trans (by gcongr)
    rw [h₀.step]
    have n₁ := norm_add_le (x n ω + α n • (f (x n ω) - x n ω) + e₁ (n + 1) ω) (e₂ (n + 1) ω)
    have n₂ := norm_add_le (x n ω + α n • (f (x n ω) - x n ω)) (e₁ (n + 1) ω)
    have n₃ := norm_add_le (x n ω) (α n • (f (x n ω) - x n ω))
    linarith

-- created on 2026-09-26