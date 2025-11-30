import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length < i)
  (x : α) :
-- imply
  s.insertIdx i x = s :=
-- proof
  List.insertIdx_of_length_lt h


-- created on 2025-10-03
