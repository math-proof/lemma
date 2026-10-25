import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[outer_measure_le_measure](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hd: 0 < d)
  (hE: IsElementary E) :
-- imply
  Lebesgue_outer_measure E ≤ (hE.measure : EReal) :=
-- proof
  IsElementary.outer_measure_le_measure hd hE


-- created on 2026-10-22
