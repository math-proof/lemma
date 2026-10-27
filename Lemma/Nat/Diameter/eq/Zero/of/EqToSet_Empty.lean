import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[diameter_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
-- given
  (h: B.toSet = ∅) :
-- imply
  B.diameter = 0 :=
-- proof
  Box.diameter_of_empty B h


-- created on 2026-10-22
