import Lemma.Algebra.LtDiv.of.Lt_Mul
import Lemma.Algebra.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Algebra.Mul_Mul
open Algebra


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
  rw [← Prod.eq.MulProdTake__ProdDrop]
  simpa


-- created on 2025-07-08
