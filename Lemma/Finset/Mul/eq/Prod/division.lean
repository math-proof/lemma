import sympy.Basic


@[path]
private lemma main
  [CommGroupWithZero α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∏ k ∈ Finset.range n, (f k / g k) =
    (∏ k ∈ Finset.range n, f k) / ∏ k ∈ Finset.range n, g k :=
-- proof
  Finset.prod_div_distrib _ _


-- created on 2020-01-31
