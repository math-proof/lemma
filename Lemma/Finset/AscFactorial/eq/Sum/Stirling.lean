import sympy.functions.combinatorial.integer_factorials
import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.EvalAscPochhammer.eq.Sum_MulPowStirlingFirst


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  (ascPochhammer ℝ n).eval x = ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) := by
-- proof
  exact Finset.EvalAscPochhammer.eq.Sum_MulPowStirlingFirst x n


-- created on 2023-08-26
