import sympy.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (i : ℕ) :
-- imply
  l.eraseIdx i = l.take i ++ l.drop (i + 1) :=
-- proof
  List.eraseIdx_eq_take_drop_succ l i


-- created on 2025-10-03
