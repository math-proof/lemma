import Lemma.Algebra.Sum_Add.eq.AddSumS
open Algebra


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (n : ℕ)
  (g : ℕ → α)
  (f : ℕ → ℕ → α) :
-- imply
  ∑ k : Fin n, g k + ∑ k : Fin n, ∑ i : Fin k, f k i = ∑ k : Fin n, (g k + ∑ i : Fin k, f k i) := by
-- proof
  rw [Sum_Add.eq.AddSumS]


-- created on 2025-07-19
