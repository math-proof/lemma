import Mathlib.Probability.Independence.Integration
import Lemma.Random.Var.eq.Integral
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x] :
-- imply
  𝕍𝕒𝕣 π x = ∫ ω, (x ω - ∫ ω', x ω' ∂π) ^ 2 ∂π := by
-- proof
  exact Random.Var.eq.Integral


-- created on 2023-03-24
-- updated on 2026-11-17
