import sympy.Basic

@[main]
private lemma comm'
  [CommMonoid β]
  {s : Finset γ}
  {t : Finset α}
-- given
  (f : γ → α → β) :
-- imply
  ∏ i ∈ s, ∏ j ∈ t, f i j = ∏ j ∈ t, ∏ i ∈ s, f i j := by
-- proof
  apply Finset.prod_comm


-- created on 2025-07-19
