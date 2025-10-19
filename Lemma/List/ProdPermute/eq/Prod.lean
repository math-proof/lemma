import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (d : Fin s.length)
  (k : ℕ) :
-- imply
  (s.permute d k).prod = s.prod := by
-- proof
  rw [ProdPermute.eq.MulProd_ProdAppend]
  rw [ProdAppend.eq.MulProdS]
  rw [ProdRotate.eq.Prod]
  rw [MulProdS.eq.ProdAppend]
  simp


-- created on 2025-10-19
