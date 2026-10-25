import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_one_step_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
-- given
  (hB: B.toSet.Nonempty) :
-- imply
  ∀ B' ∈ B.subdivide, B'.toSet.Nonempty :=
-- proof
  Box.subdivide_one_step_nonempty B hB


-- created on 2026-10-22
