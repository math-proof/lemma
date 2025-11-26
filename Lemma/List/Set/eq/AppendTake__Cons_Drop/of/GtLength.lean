import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > i)
  (a : α) :
-- imply
  s.set i a = s.take i ++ a :: s.drop (i + 1) :=
-- proof
  List.set_eq_take_cons_drop a h


-- created on 2025-07-05
