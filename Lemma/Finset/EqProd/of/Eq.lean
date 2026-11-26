import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommMonoid α]
  {n : ℕ}
  {f g : ℕ → α}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  ∏ i < n, f i = ∏ i < n, g i :=
-- proof
  Finset.prod_congr rfl (fun i hi => h i (by simpa using hi))


-- created on 2019-04-09
