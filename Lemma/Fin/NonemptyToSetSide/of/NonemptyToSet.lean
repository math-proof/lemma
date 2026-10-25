import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box


/--
[Box.side_nonempty_of_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B : Box d}
  {i : Fin d}
-- given
  (hB : B.toSet.Nonempty) :
-- imply
  (B.side i).toSet.Nonempty :=
-- proof
  Box.side_nonempty_of_nonempty B hB i


-- created on 2026-10-22
