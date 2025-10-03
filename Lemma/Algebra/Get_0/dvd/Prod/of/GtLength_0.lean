import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.Dvd_Mul
open Algebra List


@[main]
private lemma main
  [Monoid α]
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v[0] ∣ v.prod := by
-- proof
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
  apply Dvd_Mul.left


-- created on 2025-07-12
