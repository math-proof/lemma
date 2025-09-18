import Lemma.Algebra.ProdTailSet.eq.MulProdTail.LtLength_0.Gt_0
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h_d : d > 0)
  (h_s : d < s.length)
  (n : α) :
-- imply
  (s.set d (n * s[d])).tail.prod = n * s.tail.prod := by
-- proof
  
  repeat rw [Mul.comm (a := n)]
  apply ProdTailSet.eq.MulProdTail.LtLength_0.Gt_0 h_d h_s n


-- created on 2025-07-12
