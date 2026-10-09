import Mathlib
import sympy.Basic
import sympy.Analysis.AbsoluteValue.FiniteField

open AbsoluteValue

/--
[isNonarchimedean_of_charP](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
private lemma isNonarchimedean_of_charP_eq
  [Field K] [CharP K p] [NeZero p]
-- given
  (v : AbsoluteValue K ℝ) :
-- imply
  IsNonarchimedean v := by
-- proof
  apply AbsoluteValue.isNonarchimedean_of_charP


/--
[eq_one_of_ne_zero_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
private lemma eq_one_of_ne_zero_of_finite_eq
  [Field K] [Finite K]
-- given
  {x : K} (hx : x ≠ 0) (v : AbsoluteValue K ℝ) :
-- imply
  v x = 1 := by
-- proof
  apply AbsoluteValue.eq_one_of_ne_zero_of_finite
  · exact hx


-- created on 2026-10-09
