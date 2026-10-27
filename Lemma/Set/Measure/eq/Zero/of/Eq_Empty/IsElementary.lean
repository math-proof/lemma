import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[measure_of_empty_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {E : Set (EuclideanSpace' d)}
-- given
  (hE : IsElementary E)
  (hempty : E = ∅) :
-- imply
  hE.measure = 0 :=
-- proof
  IsElementary.measure_of_empty_eq hE hempty


-- created on 2026-10-22
