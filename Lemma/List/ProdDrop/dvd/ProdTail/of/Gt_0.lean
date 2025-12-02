import Lemma.List.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.List.ProdDrop.dvd.Prod
import Lemma.List.ProdTail.eq.MulProdTailTake.of.Gt_0
import Lemma.List.Tail.eq.Drop_1
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {d : ℕ}
-- given
  (h : d > 0)
  (s : List α) :
-- imply
  (s.drop d).prod ∣ s.tail.prod := by
-- proof
  rw [ProdTail.eq.MulProdTailTake.of.Gt_0 h]
  apply Dvd_Mul


-- created on 2025-07-08
-- updated on 2025-12-02
