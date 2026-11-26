import Mathlib.RingTheory.Polynomial.Pochhammer
import Theorem.Data.Set.Sets
import Lemma.Finset.EvalAscPochhammer.eq.Sum_MulPowStirlingFirst


@[path]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  (ascPochhammer ℝ n).eval x = ∑ k < (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) := by
-- proof
  exact Finset.EvalAscPochhammer.eq.Sum_MulPowStirlingFirst x n


-- created on 2023-08-26
-- updated on 2026-11-26
