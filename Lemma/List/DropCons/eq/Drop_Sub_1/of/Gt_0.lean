import sympy.Basic


@[main]
private lemma main
  {i : ℕ}

-- given
  (h : i > 0) 
  (a : α)
  (l : List α):
-- imply
  (a :: l).drop i = l.drop (i - 1) :=
-- proof
  List.drop_cons h


-- created on 2025-10-03
