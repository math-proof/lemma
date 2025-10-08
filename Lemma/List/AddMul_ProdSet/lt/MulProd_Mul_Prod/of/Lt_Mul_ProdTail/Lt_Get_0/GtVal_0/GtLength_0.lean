import Lemma.List.ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Algebra.Lt.of.Lt.Le
import Lemma.Algebra.Le.of.Eq
import Lemma.Nat.Mul
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
open Algebra List Nat


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h_s : s.length > 0)
  (h_d : d.val > 0)
  (h_i : i < s[0])
  (h_t : t < n * s.tail.prod) :
-- imply
  i * (s.set d (n * s[d.val])).tail.prod + t < (s.take d).prod * (n * (s.drop d).prod) := by
-- proof
  rw [ProdTailSet.eq.Mul_ProdTail.LtLength_0.Gt_0 h_d]
  have := AddMul.lt.Mul.of.Lt.Lt h_i h_t
  apply Lt.of.Lt.Le this
  apply Le.of.Eq
  repeat rw [Mul.comm (a := n)]
  repeat rw [Mul_Mul.eq.MulMul]
  apply EqMulS.of.Eq
  rw [MulProdS.eq.ProdAppend]
  simp
  rw [Prod.eq.Mul_ProdTail.of.GtLength_0 (v := s)]


-- created on 2025-07-17
