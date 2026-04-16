import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α) :
-- imply
  s.dropLast.prod ∣ s.prod := by
-- proof
  rw [DropLast.eq.Take_SubLength_1]
  rw [Prod.eq.MulProdS s (s.length - 1)]
  apply Dvd_Mul.left


-- created on 2026-04-16
