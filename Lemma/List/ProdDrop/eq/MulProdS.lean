import Lemma.List.Drop.eq.AppendTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i d : ℕ):
-- imply
  (s.drop i).prod = ((s.drop i).take d).prod * (s.drop (i + d)).prod := by
-- proof
  conv_lhs =>
    rw [Drop.eq.AppendTakeDrop s i d]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-10-15
