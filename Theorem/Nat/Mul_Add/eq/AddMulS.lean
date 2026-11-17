module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.Mul_Add.eq.AddMulS
  [Mul α] [Add α] [LeftDistribClass α]
-- given
  (x a b : α) :
-- imply
  x * (a + b) = x * a + x * b :=
-- proof
  mul_add x a b


-- created on 2018-03-01
-- updated on 2026-10-26
