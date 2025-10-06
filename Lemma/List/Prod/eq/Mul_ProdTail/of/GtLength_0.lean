import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.ProdCons.eq.Mul_Prod
open List


@[main]
private lemma main
  [Mul α] [One α]
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v.prod = v[0] * v.tail.prod := by
-- proof
  conv_lhs =>
    rw [Eq_Cons_Tail.of.GtLength_0 h]
  rw [ProdCons.eq.Mul_Prod]


-- created on 2025-06-09
