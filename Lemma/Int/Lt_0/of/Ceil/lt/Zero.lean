import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : ⌈x⌉ < 0) :
-- imply
  x < 0 := by
-- proof
  have h₀ := Int.le_ceil x
  have h₁ : (⌈x⌉ : ℝ) < 0 := by exact_mod_cast h
  linarith


-- created on 2019-03-11
