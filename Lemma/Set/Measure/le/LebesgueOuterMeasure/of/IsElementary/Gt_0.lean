import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[measure_le_outer_measure](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hd: 0 < d)
  (hE: IsElementary E) :
-- imply
  (hE.measure : EReal) ≤ Lebesgue_outer_measure E :=
-- proof
  IsElementary.measure_le_outer_measure hd hE


-- created on 2026-10-22
