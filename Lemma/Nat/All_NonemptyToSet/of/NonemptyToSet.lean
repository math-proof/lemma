import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_iter_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {k: ℕ}
-- given
  (hB: B.toSet.Nonempty) :
-- imply
  ∀ B' ∈ subdivide_iter B k, B'.toSet.Nonempty :=
-- proof
  Box.subdivide_iter_nonempty B hB k


-- created on 2026-10-22
