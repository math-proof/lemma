import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[binaryToTernary_summable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ} :
-- imply
  Summable (fun j => (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)) :=
-- proof
  Remark_1_3_10.binaryToTernary_summable x


-- created on 2026-10-22
