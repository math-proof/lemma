import Lemma.List.EqAppendTake__Drop
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.take i).prod * (s.drop i).prod := by
-- proof
  rw [MulProdS.eq.ProdAppend]
  rw [EqAppendTake__Drop]


-- created on 2025-10-29
