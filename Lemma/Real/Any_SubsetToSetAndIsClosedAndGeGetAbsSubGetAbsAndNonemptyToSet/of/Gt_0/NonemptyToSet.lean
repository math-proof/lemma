import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.shrink_to_closed](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {δ: ℝ}
-- given
  (hB: B.toSet.Nonempty)
  (hδ: 0 < δ) :
-- imply
  ∃ B': Box d, B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ |B'|ᵥ ≥ |B|ᵥ - δ ∧ B'.toSet.Nonempty :=
-- proof
  Box.shrink_to_closed B hB δ hδ


-- created on 2026-10-22
