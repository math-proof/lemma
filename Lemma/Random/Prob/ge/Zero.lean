import Initialize.Tactic.Attr.Basic
import Def.Probability.SymbolicProbability.Part2
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
