import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  [LinearOrder α]
  {a : α} :
-- imply
  |a| = a ⊔ -a :=
-- proof
  abs_eq_max_neg


-- created on 2025-12-25
