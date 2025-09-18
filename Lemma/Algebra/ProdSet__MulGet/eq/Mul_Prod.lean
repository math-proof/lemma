import Lemma.Algebra.Mul
import Lemma.Algebra.ProdSet__MulGet.eq.MulProd
open Algebra


@[main]
private lemma main
  [CommMonoid α]
  {v : List α}
-- given
  (i : Fin v.length)
  (t : α) :
-- imply
  (v.set i (t * v[i])).prod = t * v.prod := by
-- proof
  rw [Mul.comm]
  rw [Mul.comm (b := v.prod)]
  apply ProdSet__MulGet.eq.MulProd


-- created on 2025-07-12
