import Lemma.Nat.Mul
import Lemma.List.ProdSet__MulGet.eq.MulProd.of.Lt_Length
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i < s.length)
  (t : α) :
-- imply
  (s.set i (t * s[i])).prod = t * s.prod := by
-- proof
  repeat rw [Mul.comm (a := t)]
  apply ProdSet__MulGet.eq.MulProd.of.Lt_Length h


-- created on 2025-07-12
