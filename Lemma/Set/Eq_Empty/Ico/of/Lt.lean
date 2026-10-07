import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : b < a) :
-- imply
  Set.Ico a b = ∅ :=
-- proof
  Set.Ico_eq_empty (not_lt.mpr h.le)


-- created on 2026-10-07
