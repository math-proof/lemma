import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : i > a.length)
  (x : α) :
-- imply
  a.insertIdx i x = a :=
-- proof
  List.insertIdx_of_length_lt h


-- created on 2025-10-03
