import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Remark_1_2_8


/--
[q_surj](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∀ x ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)), ∃ n, q n = x :=
-- proof
  Remark_1_2_8.q_surj


-- created on 2026-10-22
