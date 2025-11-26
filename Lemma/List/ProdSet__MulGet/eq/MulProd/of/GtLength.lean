import Lemma.List.ProdSet__MulGet.eq.MulProd
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : s.length > i)
  (t : α) :
-- imply
  (s.set i (s[i] * t)).prod = s.prod * t := by
-- proof
  let i' : Fin s.length := ⟨i, h⟩
  have := ProdSet__MulGet.eq.MulProd i' t
  rw [← this]
  simp [i']


-- created on 2025-07-06
