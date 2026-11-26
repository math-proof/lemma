import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommGroupWithZero α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∏ k < n, (f k / g k) =
    (∏ k < n, f k) / ∏ k < n, g k :=
-- proof
  Finset.prod_div_distrib _ _


-- created on 2020-01-31
