import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.eraseIdx i = s.take i ++ s.drop (i + 1) :=
-- proof
  List.eraseIdx_eq_take_drop_succ s i


-- created on 2025-10-03
