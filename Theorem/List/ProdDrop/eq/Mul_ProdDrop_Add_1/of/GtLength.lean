module

public import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
public import Theorem.List.ProdCons.eq.Mul_Prod

public section

open List


@[comm]
public theorem List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.drop i).prod = s[i] * (s.drop (i + 1)).prod := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength h]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-06-08
-- updated on 2025-11-30
