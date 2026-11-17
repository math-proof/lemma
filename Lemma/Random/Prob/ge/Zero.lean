import Def.Probability.SymbolicProbability
open MeasureTheory


@[path]
private lemma main
  {Ω α : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  (π : Measure Ω)
  (x : Ω → α)
  [SinglePSpace π x]
  (s : Set α) :
-- imply
  0 ≤ Probability π x s :=
-- proof
  zero_le


-- created on 2023-04-04
-- updated on 2026-11-16
