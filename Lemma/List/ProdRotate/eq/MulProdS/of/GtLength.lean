import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.Nat.EqMod.of.Lt
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.rotate i).prod = (s.drop i).prod * (s.take i).prod := by
-- proof
  rw [ProdRotate.eq.MulProdS]
  rw [EqMod.of.Lt h]


-- created on 2025-11-24
