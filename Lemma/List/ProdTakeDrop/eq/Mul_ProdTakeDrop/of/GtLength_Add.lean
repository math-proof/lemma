import Lemma.List.ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength_Add
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i + d < s.length) :
-- imply
  ((s.drop i).take (d + 1)).prod = s[i + d] * ((s.drop i).take d).prod := by
-- proof
  simp [ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength_Add h]
  rw [Mul.comm]


-- created on 2025-10-29
