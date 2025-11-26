import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.eraseIdx i).length = s.length - 1 :=
-- proof
  List.length_eraseIdx_of_lt h


-- created on 2025-06-09
