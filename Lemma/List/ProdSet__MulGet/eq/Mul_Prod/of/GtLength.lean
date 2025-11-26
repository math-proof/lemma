import Lemma.List.ProdSet__MulGet.eq.Mul_Prod
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (t : α) :
-- imply
  (s.set i (t * s[i])).prod = t * s.prod := by
-- proof
  apply ProdSet__MulGet.eq.Mul_Prod ⟨i, h⟩ t


-- created on 2025-07-18
