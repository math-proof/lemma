import sympy.Basic


@[main]
private lemma main
  {n j : ℕ}
-- given
  (h : ∀ i ∈ Finset.range n, i ≠ j) :
-- imply
  j ∉ Finset.range n := by
-- proof
  exact fun hj ↦ h j hj rfl


-- created on 2021-01-15
