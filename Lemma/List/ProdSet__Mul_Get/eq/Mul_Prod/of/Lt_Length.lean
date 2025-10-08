import Lemma.Nat.Mul
import Lemma.List.ProdSet__MulGet.eq.MulProd.of.Lt_Length
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {v : List α}
-- given
  (h : i < v.length)
  (t : α) :
-- imply
  (v.set i (t * v[i])).prod = t * v.prod := by
-- proof
  repeat rw [Mul.comm (a := t)]
  apply ProdSet__MulGet.eq.MulProd.of.Lt_Length h


-- created on 2025-07-12
