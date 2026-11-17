module

public import Theorem.List.DropTake.eq.ListGet.of.GtLength
public import Theorem.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
public import Theorem.Nat.Mul.of.Eq

public section

open List Nat


public theorem List.ProdTake_Add_1.eq.MulProdTake.of.GtLength
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.take (i + 1)).prod = (s.take i).prod * s[i] := by
-- proof
  rw [ProdTake.eq.Mul_ProdDropTake.of.Ge (j := i) (by omega)]
  apply Mul.of.Eq.left
  rw [DropTake.eq.ListGet.of.GtLength h]
  simp


-- created on 2025-06-14
-- updated on 2025-11-28
