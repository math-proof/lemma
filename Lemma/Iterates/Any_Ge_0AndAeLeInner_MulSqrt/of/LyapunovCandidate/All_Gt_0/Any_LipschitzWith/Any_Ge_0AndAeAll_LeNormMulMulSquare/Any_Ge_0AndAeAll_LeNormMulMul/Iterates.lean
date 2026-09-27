import sympy.stats.lyapunov
import Lemma.Iterates.Any_Ge_0AndAeLeNorm.of.All_Gt_0.Any_LipschitzWith.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates
import Lemma.LyapunovCandidate.Any_And_Ge_0_All_LeInner.of.LyapunovCandidate
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
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : Iterates x x₀ f e₁ e₂ α)
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * α n * (‖x n ω‖ + 1))
  (h₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₂ (n + 1) ω‖ ≤ C * α n ^ 2 * (‖x n ω‖ + 1))
  (h₃ : ∃ L, LipschitzWith L f)
  (h₄ : ∀ n, 0 < α n)
  (h₅ : LyapunovCandidate φ φ')  (n : ℕ)
  (z y : EuclideanVec d) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, inner ℝ (φ' (x n ω - z)) y ≤ C * √(φ y) := by
-- proof
  obtain ⟨C₁, hC₁, hle⟩ := h₅.le_norm
  obtain ⟨C₂, hC₂, hx⟩ :=
    Iterates.Any_Ge_0AndAeLeNorm.of.All_Gt_0.Any_LipschitzWith.Any_Ge_0AndAeAll_LeNormMulMulSquare.Any_Ge_0AndAeAll_LeNormMulMul.Iterates h₀ h₁ h₂ h₃ h₄ n
  obtain ⟨C₃, hC₃, hinner⟩ := LyapunovCandidate.Any_And_Ge_0_All_LeInner.of.LyapunovCandidate h₅
  refine ⟨C₃ * (C₁ * (C₂ + ‖z‖)), by positivity, ?_⟩
  filter_upwards [hx] with ω hω
  have h : √(φ (x n ω - z)) ≤ C₁ * (C₂ + ‖z‖) :=
    (hle _).trans (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) hC₁)
  calc inner ℝ (φ' (x n ω - z)) y ≤ C₃ * √(φ (x n ω - z)) * √(φ y) := hinner _ _
    _ ≤ C₃ * (C₁ * (C₂ + ‖z‖)) * √(φ y) := by gcongr


-- created on 2026-09-26