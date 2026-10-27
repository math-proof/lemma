import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : x ∈ ⋃ k ∈ Finset.range n, A k) :
-- imply
  ∃ k ∈ Finset.range n, x ∈ A k := by
-- proof
  obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp h
  exact ⟨k, hk, hx⟩


-- created on 2018-09-09
