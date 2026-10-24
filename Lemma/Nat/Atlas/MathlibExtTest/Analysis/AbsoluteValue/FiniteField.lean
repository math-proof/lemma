import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Analysis.AbsoluteValue.FiniteField
open AbsoluteValue


/--
[test_charP_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
lemma test_charP_abstract
  [Field K]
  {p : ℕ}
  [CharP K p]
  [NeZero p]
  {v : AbsoluteValue K ℝ} :
-- imply
  IsNonarchimedean v :=
-- proof
  isNonarchimedean_of_charP v

/--
[test_finite_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
lemma test_finite_abstract
  [Field K]
  [Finite K]
  {v : AbsoluteValue K ℝ}
  {x : K}
-- given
  (hx : x ≠ 0) :
-- imply
  v x = 1 :=
-- proof
  eq_one_of_ne_zero_of_finite v hx

/--
[test_charP_zmod5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
lemma test_charP_zmod5
  [Field K]
  {v : AbsoluteValue (ZMod 5) ℝ} :
-- imply
  IsNonarchimedean v :=
-- proof
  isNonarchimedean_of_charP (K := ZMod 5) (p := 5) v

/--
[test_finite_zmod5_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
lemma test_finite_zmod5_two
  [Field K]
  {v : AbsoluteValue (ZMod 5) ℝ}
-- given
  (h : (2 : ZMod 5) ≠ 0) :
-- imply
  v 2 = 1 :=
-- proof
  eq_one_of_ne_zero_of_finite (K := ZMod 5) (x := (2 : ZMod 5)) v h

/--
[test_zero_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/FiniteField.lean)
-/
@[path]
lemma test_zero_eval
  [Field K]
  {v : AbsoluteValue (ZMod 5) ℝ} :
-- imply
  v 0 = 0 :=
-- proof
  v.map_zero


-- created on 2026-10-23
