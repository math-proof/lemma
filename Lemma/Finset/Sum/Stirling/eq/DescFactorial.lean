import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) * (-1) ^ (n - k) = (descPochhammer ℝ n).eval x := by
-- proof
  exact (descPochhammer_eval_eq_sum_stirlingFirst x n).symm


-- created on 2026-09-27
