import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Append_DropTake.eq.Take.of.Ge
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute__Neg.eq.MulProd_ProdAppend
import Lemma.List.ProdRotate.eq.Prod
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d)).prod = s.prod := by
-- proof
  rw [ProdPermute__Neg.eq.MulProd_ProdAppend]
  rw [ProdAppend.eq.MulProdS]
  rw [ProdRotate.eq.Prod]
  repeat rw [MulProdS.eq.ProdAppend]
  rw [Append_Append.eq.AppendAppend]
  rw [Append_DropTake.eq.Take.of.Ge (by omega)]
  simp


-- created on 2025-10-28
