import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Set α}
  {g : ℕ → Set α}
-- given
  (h : ∃ i < n, A ⊆ g i) :
-- imply
  A ⊆ ⋃ i < n, g i := by
-- proof
  obtain ⟨i, hi, hsi⟩ := h
  intro y hy
  simp only [Set.mem_iUnion₂]
  exact ⟨i, hi, hsi hy⟩


-- created on 2023-06-01
