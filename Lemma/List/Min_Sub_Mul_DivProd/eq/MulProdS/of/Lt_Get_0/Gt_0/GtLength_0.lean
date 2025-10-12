import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Nat.EqMin.of.Le
import Lemma.List.Tail.eq.AppendTakeTail__Drop.of.Gt_0
import Lemma.List.ProdTail.eq.DivProd.of.GtLength_0.Gt_0
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Algebra.Le_SubMulS.of.Lt
import Lemma.Nat.Gt_0
import Lemma.Nat.Gt_0.of.Gt
open Algebra List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_d : d > 0)
  (h_i : i < s[0]) :
-- imply
  s.prod / s[0] ⊓ (s.prod - i * (s.prod / s[0])) = (s.tail.take (d - 1)).prod * (s.drop d).prod := by
-- proof
  have h_s := Gt_0.of.Gt h_i
  rw [MulProdS.eq.ProdAppend]
  rw [EqMin.of.Le]
  rw [← Tail.eq.AppendTakeTail__Drop.of.Gt_0]
  rwa [DivProd.eq.ProdTail.of.GtLength_0.Gt_0 (by assumption) (by assumption)]
  rw [DivProd.eq.ProdTail.of.GtLength_0.Gt_0]
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 (v := s) (by linarith)]
  apply Le_SubMulS.of.Lt
  repeat assumption


-- created on 2025-07-07
