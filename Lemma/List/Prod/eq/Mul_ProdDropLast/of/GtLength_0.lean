import Lemma.List.Prod.eq.MulProdDropLast.of.GtLength_0
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.prod = s[s.length - 1] * s.dropLast.prod := by
-- proof
  have := Prod.eq.MulProdDropLast.of.GtLength_0 h
  rw [Mul.comm] at this
  assumption


-- created on 2025-11-24
