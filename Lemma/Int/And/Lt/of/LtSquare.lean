import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ^ 2 < a ^ 2) :
-- imply
  x < √(a ^ 2) ∧ -√(a ^ 2) < x := by
-- proof
  rw [Real.sqrt_sq_eq_abs]
  have := abs_lt.mp (sq_lt_sq.mp h)
  exact ⟨this.2, this.1⟩


-- created on 2023-06-18
