import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.DivSum.eq.Sum_Div.of.All_EqDivAdd.All_EqDiv0
import Lemma.Fin.Sum.of.All_Eq
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.Div.of.Eq
import Lemma.Nat.NotLt.is.Ge
import Lemma.Tensor.DivAdd.eq.AddDivS
import Lemma.Tensor.EqDiv0_0
import Lemma.Tensor.EqSelectKeepdim
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Tensor.SEqDivS.of.SEq.SEq
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.Sum.as.Sum.of.LeLength
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import sympy.tensor.functions
open Bool Fin List Nat Tensor


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (X : Tensor α s)
  (A : Tensor α (s.eraseIdx d)) :
-- imply
  (X / A.keepdim).sum d = X.sum d / A := by
-- proof
  if h : d < s.length then
    repeat rw [Sum.eq.Sum_Select.of.GtLength (by omega)]
    rw [DivSum.eq.Sum_Div.of.All_EqDivAdd.All_EqDiv0 EqDiv0_0 DivAdd.eq.AddDivS]
    apply @Fin.Sum.of.All_Eq
    intro i
    rw [SelectDiv.eq.DivSelectS]
    apply Div.of.Eq.left
    apply EqSelectKeepdim (d := ⟨d, h⟩)
  else
    have h := Ge.of.NotLt h
    have h_s := Eq_EraseIdx.of.LeLength h
    rw [Sum.eq.Cast_Sum.of.LeLength (by omega)]
    conv_rhs => rw [Sum.eq.Cast_Sum.of.LeLength (by omega)]
    apply EqCast.of.SEq.Eq h_s
    apply SEqDivS.of.SEq.SEq
    ·
      apply SEq_Cast.of.Eq h_s
    ·
      rw [Keepdim.eq.Cast.of.LeLength h]
      apply SEqCast.of.Eq h_s.symm


-- created on 2026-08-15
