import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[diameter_lt_of_iter_count](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {r: ℝ}
-- given
  (hB: B.toSet.Nonempty)
  (hr: 0 < r) :
-- imply
  ∀ B' ∈ subdivide_iter B (B.iter_count r), B'.diameter < r :=
-- proof
  Box.diameter_lt_of_iter_count B hB r hr


-- created on 2026-10-22
