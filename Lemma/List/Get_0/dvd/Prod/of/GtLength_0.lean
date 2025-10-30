import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s[0] ∣ s.prod := by
-- proof
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h]
  apply Dvd_Mul.left


-- created on 2025-07-12
