import Def.Dynamics.PolicyTrajectory.Gradient
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random
set_option linter.unusedVariables false


/--
By definition `V θ γ t x = V0 θ γ x` (time-homogeneous series value), so the equality holds
on every state (the former reachability hypotheses are retained only for API compatibility).
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
  M.V θ γ t x = M.V0 θ γ x := by
-- proof
  rfl


-- created on 2026-10-06
-- updated on 2026-11-03
