import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9


/--
[floor_two_mul_even_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {z : ℝ}
-- given
  (hz : 0 ≤ z)
  (heven : ⌊2 * z⌋₊ % 2 = 0) :
-- imply
  ⌊2 * z⌋₊ ≤ 2 * ⌊z⌋₊ :=
-- proof
  floor_two_mul_even_le hz heven


-- created on 2026-10-22
