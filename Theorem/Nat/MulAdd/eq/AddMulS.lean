module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.MulAdd.eq.AddMulS
  [Mul α] [Add α] [RightDistribClass α]
-- given
  (a b c : α) :
-- imply
  (a + b) * c = a * c + b * c :=
-- proof
  right_distrib a b c


-- created on 2024-07-01
-- updated on 2026-10-26
