import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Gt_0.of.GtMul
import Lemma.Algebra.Gt_0.of.Lt
import Lemma.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Algebra.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.ProdDrop.gt.Zero.of.GtProd_0
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
  (i * (n * s.tail.prod) + t) % (s.drop d).prod < (s.drop d).prod := by
-- proof
  apply LtMod.of.Gt_0
  have h_tail := Gt_0.of.GtMul h_t
  have h_head := Gt_0.of.Lt h_i
  have h_prod := Mul.gt.Zero.of.Gt_0.Gt_0 h_head h_tail
  rw [← Prod.eq.Mul_ProdTail.of.GtLength_0 h_s] at h_prod
  apply ProdDrop.gt.Zero.of.GtProd_0 h_prod


-- created on 2025-07-08
