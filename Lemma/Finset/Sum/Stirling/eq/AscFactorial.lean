import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) = (ascPochhammer ℝ n).eval x := by
-- proof
  exact (ascPochhammer_eval_eq_sum_stirlingFirst x n).symm


-- created on 2023-08-26
