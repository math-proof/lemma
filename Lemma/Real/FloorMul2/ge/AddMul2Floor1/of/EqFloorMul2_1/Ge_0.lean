import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2


/--
[floor_two_mul_odd_ge](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {z : ℝ}
-- given
  (hz : 0 ≤ z)
  (hodd : ⌊2 * z⌋₊ % 2 = 1) :
-- imply
  ⌊2 * z⌋₊ ≥ 2 * ⌊z⌋₊ + 1 :=
-- proof
  floor_two_mul_odd_ge hz hodd


-- created on 2026-10-22
