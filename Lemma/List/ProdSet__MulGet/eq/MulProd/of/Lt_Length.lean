import Lemma.List.ProdSet__MulGet.eq.MulProd
open List


@[main]
private lemma main
  [CommMonoid α]
  {v : List α}
-- given
  (h : i < v.length)
  (t : α) :
-- imply
  (v.set i (v[i] * t)).prod = v.prod * t := by
-- proof
  let i' : Fin v.length := ⟨i, h⟩
  have := ProdSet__MulGet.eq.MulProd i' t
  rw [← this]
  simp [i']


-- created on 2025-07-06
