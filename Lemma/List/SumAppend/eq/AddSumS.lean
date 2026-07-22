import sympy.Basic


@[main]
private lemma main
  [AddMonoid α]
-- given
  (a b : List α) :
-- imply
  (a ++ b).sum = a.sum + b.sum := by
-- proof
  apply List.sum_append


-- created on 2026-07-11
-- updated on 2026-07-22
