import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a state reachable at times t and 0: `M.Vc θ γ x = M.V θ γ t x`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₂ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω t).2.1) ⁻¹' {x}) ≠ 0)
  (h₃ : (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0) :
-- imply
  M.Vc θ γ x = M.V θ γ t x := by
-- proof
  exact (V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₂ h₃).symm


-- created on 2026-10-20
