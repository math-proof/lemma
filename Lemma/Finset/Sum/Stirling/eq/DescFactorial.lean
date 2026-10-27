import Mathlib.RingTheory.Polynomial.Pochhammer
import Theorem.Data.Set.Sets
import Lemma.Finset.EvalDescPochhammer.eq.Sum_MulMulPowStirlingFirstPowNeg1Sub


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) * (-1) ^ (n - k) = (descPochhammer ℝ n).eval x := by
-- proof
  exact (Finset.EvalDescPochhammer.eq.Sum_MulMulPowStirlingFirstPowNeg1Sub x n).symm


-- created on 2023-08-26
