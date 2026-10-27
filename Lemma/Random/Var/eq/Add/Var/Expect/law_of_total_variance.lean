import Mathlib.Probability.CondVar
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
Law of total variance: `Var[x] = Var[𝔼[x | m]] + 𝔼[Var[x | m]]`.
-/
@[path]
private lemma main
  {m₀ : MeasurableSpace Ω}
  {π : Measure[m₀] Ω} [IsProbabilityMeasure π]
  {x : Ω → ℝ}
  {m : MeasurableSpace Ω}
-- given
  (h₀ : m ≤ m₀)
  (h₁ : MemLp x 2 π) :
-- imply
  variance x π = variance (condExp m π x) π + ∫ ω, condVar m x π ω ∂π :=
-- proof
  (integral_condVar_add_variance_condExp (μ := π) h₀ h₁).symm.trans (add_comm _ _)


-- created on 2023-04-09
-- updated on 2026-10-26
