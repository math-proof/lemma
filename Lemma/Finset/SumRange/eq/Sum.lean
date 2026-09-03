import sympy.sets.sets
import sympy.Basic


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (n : ℕ)
  (f : ℕ → α) :
-- imply
  ∑ k ∈ range n, f k = ∑ k : Fin n, f k := by
-- proof
  apply Finset.sum_range


-- created on 2019-11-02
