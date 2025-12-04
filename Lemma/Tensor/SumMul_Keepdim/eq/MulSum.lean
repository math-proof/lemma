import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.MulSum.eq.Sum_Mul
import Lemma.Fin.Sum.of.All_Eq
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Ge.of.NotLt
import Lemma.Tensor.EqSelectKeepdim
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SelectMul.eq.MulSelectS
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import sympy.tensor.functions
open Bool Fin List Nat Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s)
  (A : Tensor α (s.eraseIdx d)) :
-- imply
  (X * A.keepdim).sum d = X.sum d * A := by
-- proof
  if h : d < s.length then
    repeat rw [Sum.eq.Sum_Select.of.GtLength (by omega)]
    rw [MulSum.eq.Sum_Mul]
    apply @Fin.Sum.of.All_Eq
    intro i
    rw [SelectMul.eq.MulSelectS]
    apply EqMulS.of.Eq.left
    apply EqSelectKeepdim (d := ⟨d, h⟩)
  else
    have h := Ge.of.NotLt h
    have h_s := Eq_EraseIdx.of.LeLength h
    repeat rw [Sum.eq.Cast_Sum.of.LeLength (by omega)]
    apply EqCast.of.SEq.Eq h_s
    apply SEqMulS.of.SEq.SEq
    ·
      apply SEq_Cast.of.Eq h_s
    ·
      rw [Keepdim.eq.Cast.of.LeLength h]
      apply SEqCast.of.Eq h_s.symm


-- created on 2025-12-04
