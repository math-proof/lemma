import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.List.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.ProdDrop.gt.Zero.of.GtProd_0
import Lemma.Nat.Gt_0.of.GtMul
open List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : d > 0)
  (h_t : t < n * s.tail.prod) :
-- imply
  t % (s.drop d).prod < ((s.drop 1).drop (d - 1)).prod := by
-- proof
  simp
  rw [EqAddSub.of.Ge (by linarith)]
  apply LtMod.of.Gt_0
  rw [Drop.eq.DropDrop__Sub.of.Ge (k := d) (i := 1) (by linarith)]
  rw [Drop_1.eq.Tail]
  apply ProdDrop.gt.Zero.of.GtProd_0
  apply Gt_0.of.GtMul h_t


-- created on 2025-07-08
