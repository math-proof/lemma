import Lemma.List.Drop.eq.AppendTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (v : List α)
  (i d : ℕ):
-- imply
  (v.drop i).prod = ((v.drop i).take d).prod * (v.drop (i + d)).prod := by
-- proof
  conv_lhs =>
    rw [Drop.eq.AppendTakeDrop v i d]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-10-15
