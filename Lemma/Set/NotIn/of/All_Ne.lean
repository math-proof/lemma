import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n j : ℕ}
-- given
  (h : ∀ i < n, i ≠ j) :
-- imply
  j ∉ Finset.range n := by
-- proof
  try simp only [← Finset.mem_range] at *
  exact fun hj ↦ h j hj rfl


-- created on 2021-01-15
