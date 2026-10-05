import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A : Set α}
  {g : ℕ → Set α}
-- given
  (h : ∃ i ∈ Finset.range n, A ⊆ g i) :
-- imply
  A ⊆ ⋃ i ∈ Finset.range n, g i := by
-- proof
  obtain ⟨i, hi, hsi⟩ := h
  intro y hy
  simp only [Set.mem_iUnion₂, Finset.mem_coe]
  exact ⟨i, hi, hsi hy⟩


-- created on 2023-06-01
