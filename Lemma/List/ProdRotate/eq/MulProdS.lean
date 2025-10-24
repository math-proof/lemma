import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  (v.rotate n).prod = (v.drop (n % v.length)).prod * (v.take (n % v.length)).prod := by
-- proof
  rw [Rotate.eq.AppendDrop__Take]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-10-24
