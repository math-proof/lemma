import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {i : ℤ} :
-- imply
  FallingFactorial x i = 1 / FallingFactorial (x - i) (-i) := by
-- proof
  unfold FallingFactorial
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · rw [ite_eq_right (show ¬(0 ≤ i) by omega), ite_eq_left (show 0 ≤ -i by omega)]
  · simp
  · rw [ite_eq_left hi.le, ite_eq_right (show ¬(0 ≤ -i) by omega), neg_neg, Int.cast_neg, sub_neg_eq_add, sub_add_cancel,
      one_div_one_div]


-- created on 2023-08-20
