import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : ℕ → Set α}
  {x : α}
-- given
  (h : ∀ k ∈ Finset.range n, x ∈ A k) :
-- imply
  x ∈ ⋂ k ∈ Finset.range n, A k := by
-- proof
  simp only [Set.mem_iInter]
  exact h


-- created on 2021-01-09
-- updated on 2023-05-21
