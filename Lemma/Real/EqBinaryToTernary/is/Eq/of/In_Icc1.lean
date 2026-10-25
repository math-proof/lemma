import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[binaryToTernary_eq_zero_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
-- given
  (hx : x ∈ Set.Icc (0:ℝ) 1) :
-- imply
  binaryToTernary x = 0 ↔ x = 0 :=
-- proof
  Remark_1_3_10.binaryToTernary_eq_zero_iff hx


-- created on 2026-10-22
