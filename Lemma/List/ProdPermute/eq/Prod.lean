import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i d).prod = s.prod := by
-- proof
  rw [ProdPermute.eq.MulProd_ProdAppend]
  rw [ProdAppend.eq.MulProdS]
  rw [ProdRotate.eq.Prod]
  simp [MulProdS.eq.ProdAppend]


-- created on 2025-10-19
