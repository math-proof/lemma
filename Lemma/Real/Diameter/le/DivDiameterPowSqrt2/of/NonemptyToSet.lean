import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[diameter_subdivide_iter](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {k: ℕ}
-- given
  (hB: B.toSet.Nonempty) :
-- imply
  ∀ B' ∈ subdivide_iter B k, B'.diameter ≤ B.diameter / (Real.sqrt 2) ^ k :=
-- proof
  Box.diameter_subdivide_iter B hB k


-- created on 2026-10-22
