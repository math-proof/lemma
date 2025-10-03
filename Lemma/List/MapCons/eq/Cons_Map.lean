import sympy.Basic


@[main]
private lemma main
-- given
  (f : α → β)
  (a : α)
  (l : List α) :
-- imply
  (a :: l).map f = f a :: l.map f := by
-- proof
  apply List.map_cons


-- created on 2025-05-08
