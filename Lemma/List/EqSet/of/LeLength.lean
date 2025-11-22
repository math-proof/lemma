import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ d)
  (a : α) :
-- imply
  s.set d a = s :=
-- proof
  List.set_eq_of_length_le h


-- created on 2025-11-22
