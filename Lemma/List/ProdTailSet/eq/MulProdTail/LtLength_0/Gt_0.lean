import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length
import Lemma.Nat.EqMulS.of.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Tail.eq.AppendTailTake__Drop.of.Gt_0
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h_d : d > 0)
  (h_s : d < s.length)
  (n : α) :
-- imply
  (s.set d (s[d] * n)).tail.prod = s.tail.prod * n := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length]
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0]
    ·
      simp
      rw [Mul.comm (b := n)]
      rw [MulMul.eq.Mul_Mul]
      rw [← ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length]
      rw [Mul.comm (a := n)]
      rw [Mul_Mul.eq.MulMul]
      apply EqMulS.of.Eq
      rw [← ProdAppend.eq.MulProdS]
      congr
      rwa [← Tail.eq.AppendTailTake__Drop.of.Gt_0]
    ·
      simp_all
      linarith
  ·
    assumption


-- created on 2025-07-06
-- updated on 2025-07-12
