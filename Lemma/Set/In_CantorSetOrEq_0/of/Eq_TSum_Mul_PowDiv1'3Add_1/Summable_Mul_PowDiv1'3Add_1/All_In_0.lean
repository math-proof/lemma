import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[mem_CantorSet_of_ternary_02](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {y : ℝ}
  {d : ℕ → ℕ}
-- given
  (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
  (hsum : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
  (hy : y = ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1)) :
-- imply
  y ∈ CantorSet ∨ y = 0 :=
-- proof
  Remark_1_3_10.mem_CantorSet_of_ternary_02 d hd hsum hy


-- created on 2026-10-22
