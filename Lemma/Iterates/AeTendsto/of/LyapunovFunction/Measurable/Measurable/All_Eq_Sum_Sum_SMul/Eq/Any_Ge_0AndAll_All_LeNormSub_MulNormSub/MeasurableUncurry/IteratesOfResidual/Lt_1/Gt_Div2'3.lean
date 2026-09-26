import sympy.stats.markov_samples
import sympy.stats.lyapunov
import sympy.Basic
import Lemma.Iterates.AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.SufficientlySparse
import Lemma.Real.Any_SufficientlySparse.of.Lt_1.Gt_Div2'3
open Filter MeasureTheory Topology Real Iterates


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {MRP : FiniteMRP S}
  {x : ℕ → (ℕ → S × S) → EuclideanVec d}
  {x₀ z : EuclideanVec d}
  {ν : ℝ}
  {F : EuclideanVec d → S × S → EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h₀ : 2 / 3 < ν)
  (h₁ : ν < 1)
  (h₂ : IteratesOfResidual x x₀ (fun n : ℕ => inv_poly ν 2 n) F)
  (h₃ : Measurable F.uncurry)
  (h₄ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖)
  (h₅ : z = f z)
  (h₆ : ∀ w, f w = ∑ s, ∑ s', (MRP.μ s * MRP.P s s') • F w (s, s'))
  (h₇ : Measurable φ)
  (h₈ : Measurable φ')
  (h₉ : LyapunovFunction φ φ' f) :
-- imply
  ∀ᵐ ω ∂MRP.markov_samples, Tendsto (fun n => x n ω) atTop (𝓝 z) := by
-- proof
  obtain ⟨anc, hanc⟩ := Any_SufficientlySparse.of.Lt_1.Gt_Div2'3 h₀ h₁
  exact AeTendsto.of.LyapunovFunction.Measurable.Measurable.All_Eq_Sum_Sum_SMul.Eq.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.MeasurableUncurry.IteratesOfResidual.SufficientlySparse hanc h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉


-- created on 2026-09-26