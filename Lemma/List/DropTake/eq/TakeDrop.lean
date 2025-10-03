import sympy.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (i j : ℕ):
-- imply
  (l.take j).drop i = (l.drop i).take (j - i) := by
-- proof
  apply l.drop_take


-- created on 2025-06-20
