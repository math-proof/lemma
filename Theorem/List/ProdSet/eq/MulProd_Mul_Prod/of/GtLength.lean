module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
public import Theorem.List.ProdAppend.eq.MulProdS
public import Theorem.List.ProdCons.eq.Mul_Prod
public import Theorem.Nat.Mul.of.Eq
public import Theorem.Nat.MulMul.eq.Mul_Mul

public section

open List Nat


@[comm]
public theorem List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (a : α) :
-- imply
  (s.set i a).prod = (s.take i).prod * (a * (s.drop (i + 1)).prod) := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength h]
  rw [ProdAppend.eq.MulProdS]
  apply Mul.of.Eq.left
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-07-12
