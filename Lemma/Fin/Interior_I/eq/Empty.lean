import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[interior_iUnion_Box_frontier_eq_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d n : ℕ}
  {B : Fin n → Box d} :
-- imply
  interior (⋃ i, frontier (B i).toSet) = ∅ :=
-- proof
  interior_iUnion_Box_frontier_eq_empty B


-- created on 2026-10-22
