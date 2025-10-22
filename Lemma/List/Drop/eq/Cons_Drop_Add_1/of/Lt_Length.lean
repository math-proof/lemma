import sympy.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  v.drop i = v[i] :: v.drop (i + 1) :=
-- proof
  List.drop_eq_getElem_cons h


-- created on 2025-06-14
