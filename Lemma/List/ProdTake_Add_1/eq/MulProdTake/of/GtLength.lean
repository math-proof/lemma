import Lemma.List.DropTake.eq.ListGet.of.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
import Lemma.Nat.EqMulS.of.Eq
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.take (i + 1)).prod = (s.take i).prod * s[i] := by
-- proof
  rw [ProdTake.eq.Mul_ProdDropTake.of.Ge (j := i) (by omega)]
  apply EqMulS.of.Eq.left
  rw [DropTake.eq.ListGet.of.GtLength h]
  simp


-- created on 2025-06-14
-- updated on 2025-11-28
