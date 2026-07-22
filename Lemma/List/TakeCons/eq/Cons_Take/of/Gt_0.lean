import sympy.Basic


@[main]
private lemma main
-- given
  (h : i > 0)
  (a : α)
  (b : List α) :
-- imply
  (a :: b).take i = a :: b.take (i - 1) :=
-- proof
  List.take_cons h


-- created on 2025-11-18
-- updated on 2026-07-22
