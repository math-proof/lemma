import Def.Probability.Decision.Risk.ValueAtRisk
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {α v : ℝ}
-- given
  (h₀ : IsVaR μ X α v) :
-- imply
  IsQuantileLower μ X α v := by
-- proof
  exact h₀.isGreatest.1


-- created on 2026-09-26
