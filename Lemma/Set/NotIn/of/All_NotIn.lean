import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : α}
  {A : ℕ → Set α}
-- given
  (h : ∀ k ∈ Finset.range n, x ∉ A k) :
-- imply
  x ∉ ⋃ k ∈ Finset.range n, A k := by
-- proof
  intro hx
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
  exact h k hk hxk


-- created on 2026-09-27
