import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (n : ℕ)
  (f : ℕ → α) :
-- imply
  ∑ k < n, f k = ∑ k : Fin n, f k := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  apply Finset.sum_range


-- created on 2019-11-02
