import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  (descPochhammer ℝ n).eval x = ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) * (-1) ^ (n - k) := by
-- proof
  exact descPochhammer_eval_eq_sum_stirlingFirst x n


-- created on 2023-08-26
