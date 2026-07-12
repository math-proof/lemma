import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.EqTensordotS.of.SEq.SEq
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqResize.of.Eq_Get
open Bool List Nat Tensor


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
      apply EqTensordotS.of.SEq.SEq
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          simp
        ·
          rw [EqMax.of.Lt h_n]
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp
        ·
          rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
        ·
          rw [EqMax.of.Lt h_n]
          rw [ResizeCast.eq.Cast_Resize.of.Eq]
          ·
            simp
            apply SEqCast.of.SEq.Eq
            ·
              simp
              rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
            ·
              apply SEqResize.of.Eq_Get (i := ⟨(s'.take (s'.length - 2)).length, by grind⟩)
              simp
          ·
            rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
  ·
    congr
    simp [Tensor.matmul_shape, Tensor.broadcast_shape]
    grind


-- created on 2026-01-10
-- updated on 2026-07-10
