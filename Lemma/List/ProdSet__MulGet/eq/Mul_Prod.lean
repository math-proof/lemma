import Lemma.Nat.Mul
import Lemma.List.ProdSet__MulGet.eq.MulProd
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (t : α) :
-- imply
  (s.set i (t * s[i])).prod = t * s.prod := by
-- proof
  rw [Mul.comm]
  rw [Mul.comm (b := s.prod)]
  apply ProdSet__MulGet.eq.MulProd


-- created on 2025-07-12
