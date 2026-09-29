import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℤ}
  {A : ℕ → Set ℤ}
-- given
  (h : x ∉ ⋃ k ∈ Finset.range n, A k) :
-- imply
  ∀ k < n, x ∉ A k := by
-- proof
  exact fun k hk hx => h (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk, hx⟩)


-- created on 2026-09-27
