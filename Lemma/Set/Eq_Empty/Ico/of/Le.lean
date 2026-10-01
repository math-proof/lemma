import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : b ≤ a) :
-- imply
  Set.Ico a b = ∅ :=
-- proof
  Set.Ico_eq_empty (not_lt.mpr h)


-- created on 2021-05-22
