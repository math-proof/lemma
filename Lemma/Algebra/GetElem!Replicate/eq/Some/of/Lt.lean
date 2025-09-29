import sympy.Basic


@[main]
private lemma main
-- given
  (h : i < n)
  (a : α) :
-- imply
  (List.replicate n a)[i]? = some a :=
-- proof
  List.getElem?_replicate_of_lt h


-- created on 2025-05-21
