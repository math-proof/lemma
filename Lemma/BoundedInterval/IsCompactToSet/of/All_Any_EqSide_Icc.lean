import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[isCompact](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d}
-- given
  (h_closed : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) :
-- imply
  IsCompact B.toSet :=
-- proof
  Box.isCompact B h_closed


-- created on 2026-10-22
