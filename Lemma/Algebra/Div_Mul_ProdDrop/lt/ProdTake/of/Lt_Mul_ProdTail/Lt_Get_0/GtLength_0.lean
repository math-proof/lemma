import Lemma.Algebra.LtDiv.of.Lt_Mul
import Lemma.Algebra.Prod.eq.MulProdTake__ProdDrop
import Lemma.Algebra.Mul_Mul
import Lemma.Algebra.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
open Algebra


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h_t : t < n * s.tail.prod)
  (d : ℕ) :
-- imply
  (i * (n * s.tail.prod) + t) / (n * (s.drop d).prod) < (s.take d).prod := by
-- proof
  apply LtDiv.of.Lt_Mul
  rw [Mul_Mul.comm (a := (s.take d).prod)]
  rw [← Prod.eq.MulProdTake__ProdDrop]
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]
  rw [Mul_Mul.comm (a := n)]
  apply AddMul.lt.Mul.of.Lt.Lt <;>
    assumption


-- created on 2025-07-08
