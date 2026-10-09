import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (h : x ∈ ⋂ k ∈ Finset.range n, A k) :
-- imply
  ∀ k ∈ Finset.range n, x ∈ A k :=
-- proof
  fun k hk ↦ Set.mem_iInter₂.mp h k hk


-- created on 2021-01-22
