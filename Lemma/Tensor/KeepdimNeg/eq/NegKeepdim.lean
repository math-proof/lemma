import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.Nat.NotGt.is.Le
import Lemma.Tensor.Keepdim.eq.Cast.of.LeLength
import Lemma.Tensor.Keepdim.eq.Cast_RepeatUnsqueeze
import Lemma.Tensor.RepeatNeg.eq.NegRepeat
import Lemma.Tensor.SEqNegS.of.SEq
import Lemma.Tensor.UnsqueezeNeg.eq.NegUnsqueeze
open Bool List Nat Tensor


@[main, comm]
private lemma main
  [Neg α]
  {s : List ℕ}
  {d : ℕ}
-- given
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  (-X).keepdim = -X.keepdim := by
-- proof
  if h : s.length > d then
    simp [Keepdim.eq.Cast_RepeatUnsqueeze (d := ⟨d, h⟩)]
    have h_s := EqSetInsertIdxEraseIdx.of.GtLength h
    apply EqCast.of.SEq.Eq
    ·
      simp [h_s]
    ·
      rw [UnsqueezeNeg.eq.NegUnsqueeze]
      rw [RepeatNeg.eq.NegRepeat]
      apply SEqNegS.of.SEq
      apply SEq_Cast.of.SEq.Eq
      ·
        simp [h_s]
      ·
        rfl
  else
    have h := Le.of.NotGt h
    simp [Keepdim.eq.Cast.of.LeLength h]
    have h_s := EqEraseIdx.of.LeLength h
    apply EqCast.of.SEq.Eq
    ·
      rw [h_s]
    ·
      apply SEqNegS.of.SEq
      apply SEq_Cast.of.Eq h_s


-- created on 2025-12-04
