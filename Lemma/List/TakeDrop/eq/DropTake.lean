import sympy.Basic


@[main]
private lemma main
  -- given
  (s : List α) :
-- imply
  (s.drop i).take j = (s.take (i + j)).drop i := by
-- proof
  apply List.take_drop


-- created on 2025-10-23
