import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (hk : k ∈ Finset.range n)
  (h : x ∈ A k) :
-- imply
  ∃ i ∈ Finset.range n, x ∈ A i := by
-- proof
  exact ⟨k, hk, h⟩


-- created on 2021-03-02
