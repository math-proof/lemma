module

public import Theorem.List.EqCons_Tail.of.GtLength_0
public import Theorem.List.ProdCons.eq.Mul_Prod

public section

open List


@[comm]
public theorem List.Prod.eq.Mul_ProdTail.of.GtLength_0
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.prod = s[0] * s.tail.prod := by
-- proof
  conv_lhs => rw [Eq_Cons_Tail.of.GtLength_0 h]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-06-09
