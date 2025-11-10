import sympy.Basic


@[main]
private lemma main
  -- given
  (f : α → β)
  (l : List α)
  (i : ℕ) :
-- imply
  (l.take i).map f = (l.map f).take i :=
-- proof
  List.map_take


-- created on 2025-11-09
