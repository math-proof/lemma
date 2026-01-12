import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.TailTake.eq.TakeTail
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import Lemma.Tensor.BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS
import Lemma.Tensor.GetBroadcast.as.Broadcast.of.GtLength_0
import Lemma.Tensor.GetBroadcastMatmulRec.as.Map₂_ToVectorS.of.GtLengthS
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength
import Lemma.Tensor.SEqBroadcastMatmulRecS.of.SEq.SEq
import Lemma.Tensor.SEqBroadcastS.of.Eq.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import sympy.tensor.tensor
open Tensor Bool List


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k]))
  (i : Fin s[0]) :
-- imply
  let Xi : Tensor α (s.tail ++ [m, n]) := cast (by grind) (X[i]'(GtLength.of.GtLength (by simpa) X ⟨i, by grind⟩ (j := s'.length + 2)))
  (X.broadcast_matmul Y)[i]'(GtLength.of.GtLength (by simp [broadcast_shape]; grind) (X.broadcast_matmul Y) ⟨i, by simp [broadcast_shape]; grind⟩ (j := s'.length + 2)) ≃ Xi.broadcast_matmul_rec (Y.broadcast (s.tail.take (s.tail.length - s'.length) ++ s' ++ [n, k]) (by simp)) (by grind) := by
-- proof
  simp only [GetElem.getElem]
  have := BroadcastMatmul.as.BroadcastMatmulRec.of.GtLengthS h X Y
  have := Eq_Cast.of.SEq this
  rw [this]
  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (i := ⟨i, by simp [broadcast_shape]; grind⟩)]
  ·
    simp
    apply SEqCast.of.SEq.Eq
    ·
      simp [broadcast_shape]
      split_ifs
      repeat omega
      simp
      rw [Append_Append.eq.AppendAppend]
      congr
      rw [ZipWith__Append.eq.AppendZipWithS]
      apply EqAppendS.of.Eq
      simp
    ·
      have := GetBroadcastMatmulRec.as.Map₂_ToVectorS.of.GtLengthS (by grind) (by grind) (by grind) X (Y.broadcast (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by grind)) i
      apply this.trans
      apply SEqBroadcastMatmulRecS.of.SEq.SEq
      ·
        simp
        grind
      ·
        rfl
      ·
        apply SEqCast.of.SEq.Eq
        ·
          grind
        ·
          have h_s : s.tail.take (s.tail.length - s'.length) ++ s' ++ [n, k] = (s.take (s.length - s'.length)).tail ++ (s' ++ [n, k]) := by 
            simp
            rw [← TailTake.eq.TakeTail]
            grind
          have h_broadcast := SEqBroadcastS.of.Eq.Eq (by simp) h_s (by rfl) (A := Y)
          symm
          apply h_broadcast.trans
          have h_get := GetBroadcast.as.Broadcast.of.GtLength_0.fin (by grind) Y ⟨i, by grind⟩ (s' := s.take (s.length - s'.length))
          simp at h_get
          apply h_get.symm.trans
          apply SEqGetS.of.SEq.GtLength
          apply SEqBroadcastS.of.Eq.Eq
          ·
            simp
          ·
            rfl
  ·
    simp [broadcast_shape]
    split_ifs
    repeat omega
    simp
    rw [Append_Append.eq.AppendAppend]
    apply EqAppendS.of.Eq
    rw [ZipWith__Append.eq.AppendZipWithS]
    apply EqAppendS.of.Eq
    simp
  ·
    simp [broadcast_shape]


-- created on 2026-01-11
-- updated on 2026-01-12
