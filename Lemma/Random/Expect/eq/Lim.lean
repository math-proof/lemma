import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter Topology


@[path]
private lemma main
  [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {π : Measure Ω}
  {F : ℕ → Ω → E}
  {f : Ω → E}
  {bound : Ω → ℝ}
-- given
  (h₀ : ∀ n, AEStronglyMeasurable (F n) π)
  (h₁ : Integrable bound π)
  (h₂ : ∀ n, ∀ᵐ ω ∂π, ‖F n ω‖ ≤ bound ω)
  (h₃ : ∀ᵐ ω ∂π, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
-- imply
  Tendsto (fun n => ∫ ω, F n ω ∂π) atTop (𝓝 (∫ ω, f ω ∂π)) :=
-- proof
  tendsto_integral_of_dominated_convergence bound h₀ h₁ h₂ h₃


-- created on 2023-04-04
-- updated on 2026-10-26
