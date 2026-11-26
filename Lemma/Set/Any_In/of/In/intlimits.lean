import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n k : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (hk : k ∈ Finset.range n)
  (h : x ∈ A k) :
-- imply
  ∃ i < n, x ∈ A i := by
-- proof
  try simp only [← Finset.mem_range] at *
  exact ⟨k, hk, h⟩


-- created on 2021-03-02
