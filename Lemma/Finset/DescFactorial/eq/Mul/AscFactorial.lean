import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {n : ℕ} :
-- imply
  (descPochhammer ℝ n).eval x = (-1) ^ n * (ascPochhammer ℝ n).eval (-x) := by
-- proof
  rw [ascPochhammer_eval_neg_eq_descPochhammer ℝ x n, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]


-- created on 2023-08-20
