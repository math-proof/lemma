import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddCommGroup α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∑ k < n, f k - ∑ k < n, g k = ∑ k < n, (f k - g k) :=
-- proof
  (Finset.sum_sub_distrib f g).symm


-- created on 2018-08-09
