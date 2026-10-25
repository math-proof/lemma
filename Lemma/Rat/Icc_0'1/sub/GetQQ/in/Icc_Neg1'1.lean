import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
open scoped Pointwise


/--
[unit_interval_covered_by_translates](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  Set.Icc (0:ℝ) 1 ⊆ ⋃ (q : ℚ) (_ : q ∈ Set.Icc (-1:ℚ) 1), (VitaliSet + {(q:ℝ)}) :=
-- proof
  unit_interval_covered_by_translates


-- created on 2026-10-22
