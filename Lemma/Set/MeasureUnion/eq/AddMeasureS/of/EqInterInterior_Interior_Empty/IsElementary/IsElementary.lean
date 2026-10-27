import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[IsElementary.measure_of_almostDisjUnion](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E F: Set (EuclideanSpace' d)}
-- given
  (hE: IsElementary E)
  (hF: IsElementary F)
  (h: interior E ∩ interior F = ∅) :
-- imply
  (hE.union hF).measure = hE.measure + hF.measure :=
-- proof
  IsElementary.measure_of_almostDisjUnion hE hF h


-- created on 2026-10-22
