import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.EqBroadcastMatmulS.of.SEq.SEq
import Lemma.Tensor.EqBroadcastMatmulS.of.Eq.Eq
import Lemma.Nat.EqMax.of.Lt
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Nat.EqAddMulDiv
import Lemma.Bool.SEq.is.EqCast.of.Eq
open List Nat Bool Tensor


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] < s'[s'.length - 2])
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
  let X' : Tensor α (batch_size ++ [m, n']) := cast (by simp) (X'.resize ⟨batch_size.length + 1, by grind⟩ n')
  let Y' : Tensor α (batch_size' ++ [n', k]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) Y
  X.matmul Y ≃ Tensor.broadcast_matmul X' Y' := by
-- proof
  unfold Tensor.matmul
  apply SEq.of.Eq_Cast
  .
    split_ifs
    .
      grind
    .
      grind
    .
      grind
    .
      grind
    .
      grind
    .
      simp
      apply EqBroadcastMatmulS.of.SEq.SEq
      .
        apply SEqCastS.of.SEq.Eq.Eq
        .
          simp
        .
          simp
        .
          rw [EqMax.of.Lt h_n]
      .
        apply SEqCastS.of.SEq.Eq.Eq
        .
          simp
        .
          rw [List.EqAppendTake__ListGet.of.GeLength_2 (by grind)]
        .
          rw [EqMax.of.Lt h_n]
          rw [ResizeCast.eq.Cast_Resize.of.Eq]
          .
            simp
            apply SEqCast.of.SEq.Eq
            .
              simp
              rw [List.EqAppendTake__ListGet.of.GeLength_2 (by grind)]
            .
              sorry
              erw [List.LengthTake.eq.Min_Length]
          .
            rw [List.EqAppendTake__ListGet.of.GeLength_2 (by grind)]
  .
    congr
    simp [Tensor.matmul_shape, Tensor.broadcast_shape]
    grind


-- created on 2026-01-10
