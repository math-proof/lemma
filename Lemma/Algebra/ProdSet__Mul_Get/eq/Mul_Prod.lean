import Lemma.Algebra.ProdSet__MulGet.eq.MulProd
import Lemma.Algebra.Mul
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
  repeat rw [Mul.comm (a := t)]
  apply ProdSet__MulGet.eq.MulProd


-- created on 2025-07-12
