import Lemma.List.ProdSet__MulGet.eq.Mul_Prod
open List


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
  apply ProdSet__MulGet.eq.Mul_Prod ⟨i, h⟩ t


-- created on 2025-07-18
