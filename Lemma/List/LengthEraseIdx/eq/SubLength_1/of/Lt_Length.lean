import sympy.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.eraseIdx i).length = v.length - 1 :=
-- proof
  List.length_eraseIdx_of_lt h


-- created on 2025-06-09
