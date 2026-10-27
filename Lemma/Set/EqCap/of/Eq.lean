import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → Set α}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  (⋂ i ∈ Finset.range n, f i) = ⋂ i ∈ Finset.range n, g i := by
-- proof
  ext x
  simp only [Set.mem_iInter, Finset.mem_range]
  constructor
  ·
    intro hx i hi
    rw [← h i hi]
    exact hx i hi
  ·
    intro hx i hi
    rw [h i hi]
    exact hx i hi


-- created on 2021-01-17
