import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h : ∀ i ∈ Finset.range n, f i = g i) :
-- imply
  ∏ i ∈ Finset.range n, f i = ∏ i ∈ Finset.range n, g i :=
-- proof
  Finset.prod_congr rfl h


-- created on 2026-09-27
