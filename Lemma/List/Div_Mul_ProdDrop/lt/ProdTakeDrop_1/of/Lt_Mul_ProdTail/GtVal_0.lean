import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.List.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Mul_Mul
open List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : d > 0)
  (h_t : t < n * s.tail.prod) :
-- imply
  t / (n * (s.drop d).prod) < ((s.drop 1).take (d - 1)).prod := by
-- proof
  apply LtDiv.of.Lt_Mul
  rw [Mul_Mul.comm]
  rw [Drop.eq.DropDrop__Sub.of.Ge (k := d) (i := 1) (by linarith)]
  rw [← Prod.eq.MulProdS]
  simpa


-- created on 2025-07-08
