import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[diameter_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d} :
-- imply
  0 ≤ B.diameter :=
-- proof
  Box.diameter_nonneg B


-- created on 2026-10-22
