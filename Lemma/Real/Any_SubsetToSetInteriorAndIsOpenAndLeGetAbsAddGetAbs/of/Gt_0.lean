import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[Box.inflate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {δ: ℝ}
-- given
  (hδ: 0 < δ) :
-- imply
  ∃ B': Box d, B.toSet ⊆ interior B'.toSet ∧ IsOpen (interior B'.toSet) ∧ |B'|ᵥ ≤ |B|ᵥ + δ :=
-- proof
  Box.inflate B δ hδ


-- created on 2026-10-22
