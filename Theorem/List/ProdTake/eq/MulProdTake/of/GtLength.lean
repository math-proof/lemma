module

public import Theorem.List.ProdAppend.eq.MulProdS
public import Theorem.List.Take.eq.AppendTake.of.GtLength

public section

open List


public theorem List.ProdTake.eq.MulProdTake.of.GtLength
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.take (i + 1)).prod = (s.take i).prod * s[i] := by
-- proof
  rw [Take.eq.AppendTake.of.GtLength h]
  rw [ProdAppend.eq.MulProdS]
  simp


-- created on 2025-10-27
