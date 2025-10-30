import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  s.drop i = s[i] :: s.drop (i + 1) :=
-- proof
  List.drop_eq_getElem_cons h


-- created on 2025-06-14
