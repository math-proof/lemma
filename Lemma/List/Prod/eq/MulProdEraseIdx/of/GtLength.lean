import Lemma.List.Prod.eq.Mul_ProdEraseIdx.of.GtLength
import Lemma.Nat.Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s.prod = (s.eraseIdx i).prod * s[i] := by
-- proof
  rw [Prod.eq.Mul_ProdEraseIdx.of.GtLength h]
  rw [Mul.comm]


-- created on 2025-11-29
