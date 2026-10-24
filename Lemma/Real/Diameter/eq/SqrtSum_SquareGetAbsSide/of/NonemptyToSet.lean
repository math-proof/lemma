import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[diameter_eq_sqrt_sum_sq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
-- given
  (h: B.toSet.Nonempty) :
-- imply
  B.diameter = √(∑ i, |B.side i|ₗ^2) :=
-- proof
  Box.diameter_eq_sqrt_sum_sq B h


-- created on 2026-10-22
