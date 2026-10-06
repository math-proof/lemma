import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℤ}
  {y : ℝ}
-- given
  (h : (x : ℝ) ≤ y) :
-- imply
  x ≤ Int.floor y :=
-- proof
  Int.le_floor.mpr h


-- created on 2018-05-22
