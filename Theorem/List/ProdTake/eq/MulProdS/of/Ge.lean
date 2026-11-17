module

public import Theorem.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
public import Theorem.List.Slice.eq.DropTake

public section

open List


public theorem List.ProdTake.eq.MulProdS.of.Ge
  [Monoid α]
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.take i).prod = (s.take j).prod * (s.slice j i).prod := by
-- proof
  rw [ProdTake.eq.Mul_ProdDropTake.of.Ge h]
  rw [Slice.eq.DropTake]


-- created on 2025-06-14
-- updated on 2025-11-28
