import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqBatchDotS.of.SEq.SEq
import Lemma.Tensor.SEqBroadcastS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool List Tensor
set_option maxHeartbeats 400000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_n : n = s[s.length - 2])
  (X : Tensor α [n])
  (Y : Tensor α s) :
-- imply
  let batch_size := s.take (s.length - 2)
  let k := s[s.length - 1]
  let Y' : Tensor α (batch_size ++ [n, k]) := cast (by rwa [h_n, EqAppendTake__ListGet.of.GeLength_2]) Y
  let X' := X.broadcast (batch_size ++ [1, n]) (by simp)
  X.matmul Y ≃ (X'.batch_dot Y').select ⟨s.length - 2, by simp [batch_size]⟩ ⟨0, by grind⟩ := by
-- proof
  unfold Tensor.matmul
  apply SEq.of.Eq_Cast
  ·
    split_ifs with h h h h h
    ·
      grind
    ·
      grind
    ·
      grind
    ·
      simp
      congr 1
      apply Eq.of.SEq
      apply SEqBatchDotS.of.SEq.SEq
      ·
        apply SEqBroadcastS.of.SEq.Eq.Dvd
        ·
          rw [h_n]
          simp
        ·
          apply SEqResize_0.of.Eq_Get_0.GtLength_0
          ·
            rw [← h_n]
            grind
          ·
            grind
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp [h_n]
        ·
          simp [h_n]
          rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
        ·
          rw [ResizeCast.eq.Cast_Resize.of.Eq]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp [h_n]
              rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
            ·
              apply SEqResize.of.Eq_Get (i := ⟨(s.take (s.length - 2)).length, by grind⟩)
              grind
          ·
            rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
    ·
      simp
      grind
    ·
      grind
  ·
    congr
    simp [Tensor.matmul_shape]
    simp [show s ≠ [] by grind]
    rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]


-- created on 2026-01-07
-- updated on 2026-07-10
