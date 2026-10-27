import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[non_dyadic_eq_binary_sum](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
-- given
  (hx : x ∈ Set.Ico (0:ℝ) 1)
  (hnd : x ∉ DyadicRationals) :
-- imply
  x = ∑' j : ℕ, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) :=
-- proof
  Remark_1_3_10.non_dyadic_eq_binary_sum hx hnd


-- created on 2026-10-22
