import Def.Data.Holor.Reshape
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqReshapeS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.SEqSelectS.of.SEq
import Instance.LinearAlgebra.Matrix.Matmul
import Def.Data.Holor.Bmm
open Bool List Tensor
set_option maxHeartbeats 200000


@[path, cast]
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
  let X' := X.reshape (batch_size ++ [1, n]) (by simp)
  X.einsum Y ≃ (X'.bmm Y').select ⟨s.length - 2, by simp [batch_size]⟩ ⟨0, by grind⟩ := by
-- proof
  unfold einsum
  apply SEq.of.Eq_Cast.Eq
  ·
    simp
    split_ifs with h h
    ·
      grind
    ·
      grind
    ·
      simp
      apply Eq.of.SEq
      apply SEqSelectS.of.SEq
      apply SEqBmmS.of.SEq.SEq
      ·
        apply SEqReshapeS.of.SEq.Eq.Dvd
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
    simp [Tensor.matmul_shape]
    simp [show s ≠ [] by grind]
    rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [Drop.eq.ListGet.of.GtLength_0 (by omega)]


-- created on 2026-01-07
-- updated on 2026-10-26
