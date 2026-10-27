import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsElementary


/--
[measure_le_finset_boxes_volume'](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {t : Finset ℕ}
  {B : ℕ → Box d} :
-- imply
  (IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => B n.1)).measure ≤ ∑ n ∈ t, (B n).volume :=
-- proof
  IsElementary.measure_le_finset_boxes_volume' t B


-- created on 2026-10-22
