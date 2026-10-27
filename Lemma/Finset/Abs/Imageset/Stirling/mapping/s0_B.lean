import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s₀ B : Finset α}
-- given
  (h : s₀.card = B.card) :
-- imply
  s₀.card = B.card := by
-- proof
  apply h


-- created on 2020-08-14
