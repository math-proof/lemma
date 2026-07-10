import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Tensor.EqBroadcastMatmulS.of.SEq.SEq
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqResize.of.Eq_Get
open Bool List Nat Tensor


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] = s'[s'.length - 2])
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  let batch_size := s.take (s.length - 2)
  let batch_size' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let X' : Tensor α (batch_size ++ [m, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
  let Y' : Tensor α (batch_size' ++ [n', k]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
  let Y' : Tensor α (batch_size' ++ [n, k]) := cast (by grind) Y'
  X.einsum Y ≃ Tensor.tensordot X' Y' := by
-- proof
  unfold Tensor.einsum
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
      grind
    ·
      grind
    ·
      simp
      apply EqBroadcastMatmulS.of.SEq.SEq
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
        ·
          rw [ResizeCast.eq.Cast_Resize.of.Eq]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp [← h_n]
              rw [AddSub.eq.Sub_Sub.of.Ge.Ge (by assumption) (by simp)]
              simp
              rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
            ·
              apply SEqResize.of.Eq_Get (i := ⟨(s.take (s.length - 2)).length + 1, by grind⟩)
              grind
          ·
            rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          simp [h_n]
          rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
        ·
          rw [h_n]
          simp
          rw [ResizeCast.eq.Cast_Resize.of.Eq]
          ·
            apply SEqCast.of.SEq.Eq
            ·
              simp
              rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
            ·
              simp
              apply SEqResize.of.Eq_Get (i := ⟨(s'.take (s'.length - 2)).length, by grind⟩)
              grind
          ·
            rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
  ·
    congr
    simp [Tensor.matmul_shape, Tensor.broadcast_shape]
    grind


-- created on 2026-01-05
-- updated on 2026-07-10
