import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory
open scoped ProbabilityTheory


/-- Unfold `𝔼[x: π](f x | y)` to Mathlib's `π[fun ω ↦ f (x ω) | MeasurableSpace.comap y inferInstance]`. -/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace γ]
  [NormedAddCommGroup β]
  [NormedSpace ℝ β]
  [CompleteSpace β]
-- given
  (π : Measure Ω)
  (x : Ω → α)
  (y : Ω → γ)
  (f : α → β) :
-- imply
  Expectation.condSigma π x y f =
      MeasureTheory.condExp (MeasurableSpace.comap y inferInstance) π (fun ω ↦ f (x ω)) := by
-- proof
  exact rfl


-- created on 2026-10-07
