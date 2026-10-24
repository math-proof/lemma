import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Remark_1_2_8


/--
[q_mem](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {n : ℕ} :
-- imply
  q n ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun r:ℚ ↦ (r:ℝ)) :=
-- proof
  Remark_1_2_8.q_mem n


-- created on 2026-10-22
