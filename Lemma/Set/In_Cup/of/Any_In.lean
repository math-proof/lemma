import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : ∃ k ∈ Finset.range n, x ∈ A k) :
-- imply
  x ∈ ⋃ k ∈ Finset.range n, A k := by
-- proof
  obtain ⟨k, hk, hx⟩ := h
  exact Set.mem_iUnion₂.mpr ⟨k, hk, hx⟩


-- created on 2018-10-23
