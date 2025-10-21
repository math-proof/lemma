import sympy.Basic


@[main, comm]
private lemma main
  [Mul α] [Add α] [LeftDistribClass α]
-- given
  (x a b : α) :
-- imply
  x * (a + b) = x * a + x * b :=
-- proof
  mul_add x a b


-- created on 2024-07-01
-- updated on 2025-07-14
