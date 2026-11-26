import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : ∃ k < n, x ∈ A k) :
-- imply
  x ∈ ⋃ k < n, A k := by
-- proof
  obtain ⟨k, hk, hx⟩ := h
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hx⟩


-- created on 2018-09-28
