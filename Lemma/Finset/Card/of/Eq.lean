import sympy.Basic


@[main]
private lemma main
  {A B : Finset α}
-- given
  (h : A = B) :
-- imply
  A.card = B.card :=
-- proof
  congrArg Finset.card h


-- created on 2020-07-07
-- updated on 2026-09-07
