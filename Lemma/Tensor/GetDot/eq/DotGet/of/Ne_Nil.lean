import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.as.DotGet
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Tensor List Bool


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s ≠ [])
  (X : Tensor α (n :: s))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s (by apply GeLength_1.of.Ne_Nil h_s) X Y i) ≃ X[i] @ Y := by
-- proof
  have h_s := GtLength_0.of.Ne_Nil h_s
  let X' : Tensor α (n :: (s.take (s.length - 1) ++ [s[s.length - 1]])) := cast (by simp; grind) X
  have h_get := GetDot.as.DotGet.fin X' Y i
  simp [X'] at h_get
  simp [GetElem.getElem]
  have h_cast := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp; grind) X ⟨i, by grind⟩ (s' := n :: (s.take (s.length - 1) ++ [s[s.length - 1]]))
  simp at h_cast
  rw [h_cast] at h_get
  have h_s : (n :: s).tail = (n :: (s.take (s.length - 1) ++ [s[s.length - 1]])).tail := by 
    simp
    grind
  have h_seq : (cast (congrArg (Tensor α) h_s) (X.get i)) @ Y ≃ (X.get i) @ Y := SEqDotS.of.SEq (by apply SEqCast.of.Eq h_s) Y
  have h_get := h_get.trans h_seq
  symm
  apply h_get.symm.trans
  apply SEqGetS.of.SEq.GtLength
  apply SEqDotS.of.SEq
  apply SEqCast.of.Eq
  simp
  grind


-- created on 2026-01-04
-- updated on 2026-01-13
