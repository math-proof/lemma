import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdTake_1.eq.HeadD_1
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α} :
-- imply
  (s.eraseIdx 1).prod = s.headD 1 * (s.drop 2).prod := by
-- proof
  rw [EraseIdx.eq.Append_Drop_Add_1]
  rw [ProdAppend.eq.MulProdS]
  rw [ProdTake_1.eq.HeadD_1]


-- created on 2025-11-03
