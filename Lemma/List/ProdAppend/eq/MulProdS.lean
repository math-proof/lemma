import sympy.Basic


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (a b : List α) :
-- imply
  (a ++ b).prod = a.prod * b.prod :=
-- proof
  List.prod_append


-- created on 2025-06-14
