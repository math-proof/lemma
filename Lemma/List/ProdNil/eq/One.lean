import sympy.Basic


@[main]
private lemma main
  [Mul α] [One α] :
-- imply
  ([] : List α).prod = 1 :=
-- proof
  List.prod_nil


-- created on 2026-08-25
