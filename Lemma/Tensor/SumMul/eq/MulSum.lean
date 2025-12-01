import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Finset.MulSum.eq.Sum_Mul
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.Nat.Ge.of.NotLt
import Lemma.Tensor.SEqMulS.of.SEq
import Lemma.Tensor.Sum.eq.Cast_Sum.of.LeLength
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
open Bool List Nat Tensor Finset


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
    -- rw [MulSum.eq.Sum_Mul.fin]
    sorry
  else
    repeat rw [Sum.eq.Cast_Sum.of.LeLength (by omega)]
    have h := Ge.of.NotLt h
    have h := Eq_EraseIdx.of.LeLength h
    apply EqCast.of.SEq.Eq h
    apply SEqMulS.of.SEq
    apply SEq_Cast.of.Eq h


-- created on 2025-12-01
