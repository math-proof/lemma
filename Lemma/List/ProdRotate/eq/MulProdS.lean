import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  (s.rotate n).prod = (s.drop (n % s.length)).prod * (s.take (n % s.length)).prod := by
-- proof
  rw [Rotate.eq.AppendDrop__Take]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-10-24
