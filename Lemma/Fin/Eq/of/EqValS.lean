import sympy.Basic


@[main]
private lemma main
  {a b : Fin n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b :=
-- proof
  Fin.eq_of_val_eq h


-- created on 2024-07-01
-- updated on 2025-10-03
