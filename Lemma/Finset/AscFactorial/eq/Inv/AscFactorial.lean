import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {i : ℤ} :
-- imply
  RisingFactorial x i = 1 / RisingFactorial (x + i) (-i) := by
-- proof
  unfold RisingFactorial
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · rw [if_neg (show ¬(0 ≤ i) by omega), if_pos (show 0 ≤ -i by omega)]
  · simp
  · rw [if_pos hi.le, if_neg (show ¬(0 ≤ -i) by omega), neg_neg, Int.cast_neg, add_neg_cancel_right, one_div_one_div]


-- created on 2023-08-20
