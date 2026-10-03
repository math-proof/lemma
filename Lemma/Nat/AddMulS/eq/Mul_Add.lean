import sympy.Basic


@[main]
private lemma main
  [Mul α] [Add α] [LeftDistribClass α]
-- given
  (a x y : α) :
-- imply
  a * x + a * y = a * (x + y) :=
-- proof
  (mul_add a x y).symm


-- created on 2026-10-03
