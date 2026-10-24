import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2


/--
[floor_two_mul_eq_of_mod_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y)
  (h_floor : ⌊x⌋₊ = ⌊y⌋₊)
  (h_mod : ⌊2 * x⌋₊ % 2 = ⌊2 * y⌋₊ % 2) :
-- imply
  ⌊2 * x⌋₊ = ⌊2 * y⌋₊ :=
-- proof
  floor_two_mul_eq_of_mod_eq hx hy h_floor h_mod


-- created on 2026-10-22
