import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch7PowerDifference

open Ramanujan.Part1Ch7

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
private lemma chapter7_admissible_zero_is :
-- imply
  chapter7Admissible 0 := by
-- proof
  apply Ramanujan.Part1Ch7.chapter7Admissible_zero

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
private lemma chapter7_power_difference_term_zero_left_eq
-- given
  (x : ℂ)
  (j : ℕ) :
-- imply
  chapter7PowerDifferenceTerm 0 x j = 0 := by
-- proof
  apply Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_left x j

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
private lemma chapter7_power_difference_term_zero_right_eq
-- given
  (r : ℂ)
  (j : ℕ) :
-- imply
  chapter7PowerDifferenceTerm r 0 j = 0 := by
-- proof
  apply Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_right r j

-- created on 2026-10-10
