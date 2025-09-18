import Lemma.Algebra.LtVal
import Lemma.Algebra.ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0
open Algebra


@[main]
private lemma main
  [CommMonoid α]
  [LT α]
  {s : List α}
  {d : Fin s.length}
  {n : α}
-- given
  (h_d : d.val > 0)
  (h_t : t < n * s.tail.prod) :
-- imply
  t < ((s.set d (n * s[d])).drop 1).prod := by
-- proof
  simp
  rwa [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0 h_d (LtVal d) n]


-- created on 2025-07-17
