import Lemma.List.ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0
import Lemma.Algebra.MulProd_Mul_Prod.eq.Mul_Prod
open Algebra List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h_d : d > 0)
  (h_s : d < s.length) :
-- imply
  (s.set d (n * s[d])).tail.prod = (s.tail.take (d - 1)).prod * (n * (s.tail.drop (d - 1)).prod) := by
-- proof
  rw [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0 h_d h_s]
  rw [MulProd_Mul_Prod.eq.Mul_Prod]


-- created on 2025-07-17
