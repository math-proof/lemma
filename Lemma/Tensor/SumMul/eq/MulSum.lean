import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Finset.MulSum.eq.Sum_Mul
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Ge.of.NotLt
import Lemma.Tensor.Mul.eq.Mul_TensorReplicate
import Lemma.Tensor.SEqMulS.of.SEq
import Lemma.Tensor.SelectMul.eq.MulSelectS
import Lemma.Tensor.SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
open Bool Fin Finset List Nat Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s)
  (d : ℕ)
  (a : α) :
-- imply
  (X * a).sum d = X.sum d * a := by
-- proof
  if h : d < s.length then
    repeat rw [Sum.eq.Sum_Select.of.GtLength (by omega)]
    simp [Mul.eq.Mul_TensorReplicate]
    rw [MulSum.eq.Sum_Mul]
    apply @Fin.Sum.of.All_Eq
    intro i
    rw [SelectMul.eq.MulSelectS]
    apply EqMulS.of.Eq.left
    apply SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx
  else
    repeat rw [Sum.eq.Cast_Sum.of.LeLength (by omega)]
    have h := Ge.of.NotLt h
    have h := Eq_EraseIdx.of.LeLength h
    apply EqCast.of.SEq.Eq h
    apply SEqMulS.of.SEq
    apply SEq_Cast.of.Eq h


-- created on 2025-12-01
