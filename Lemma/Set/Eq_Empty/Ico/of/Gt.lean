import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  Set.Ico a b = ∅ :=
-- proof
  Set.Ico_eq_empty (not_lt.mpr (le_of_lt h))


-- created on 2021-04-17
