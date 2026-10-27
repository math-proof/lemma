import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box


/--
[Box.volume_eq_zero_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
-- given
  (h: B.toSet = ∅) :
-- imply
  |B|ᵥ = 0 :=
-- proof
  Box.volume_eq_zero_of_empty B h


-- created on 2026-10-22
