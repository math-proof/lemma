import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
import Lemma.Tensor.SEqReshapeS.of.SEq.Eq.Dvd
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool List Nat Tensor
set_option maxHeartbeats 400000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s[s.length - 1] < n')
  (X : Tensor α s)
  (Y : Tensor α [n']) :
-- imply
  let batch_size := s.take (s.length - 2)
  let k := s[s.length - 2]
  let n := s[s.length - 1]
  let X' : Tensor α (batch_size ++ [k, n]) := cast (by rwa [EqAppendTake__ListGet.of.GeLength_2]) X
  let X' : Tensor α (batch_size ++ [k, n']) := cast (by simp) (X'.resize ⟨batch_size.length + 1, by grind⟩ n')
  let Y' := Y.reshape ((batch_size ++ [n', 1])) (by simp)
  X.einsum Y ≃ (X'.bmm Y').select ⟨s.length - 1, by simp [batch_size]; omega⟩ ⟨0, by grind⟩ := by
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
      simp
      apply Eq.of.SEq
      apply SEqSelectS.of.SEq
      apply SEqBmmS.of.SEq.SEq
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          rw [EqMax.of.Lt h_s']
          simp
        ·
          simp
        ·
          rw [EqMax.of.Lt h_s']
      ·
        apply SEqReshapeS.of.SEq.Eq.Dvd
        ·
          rw [EqMax.of.Lt h_s']
        ·
          apply SEqResize_0.of.Eq_Get_0.GtLength_0
          ·
            rw [EqMax.of.Lt h_s']
            grind
          ·
            grind
    ·
      simp
      grind
  ·
    congr
    simp [Tensor.matmul_shape]
    simp [show s ≠ [] by grind]
    simp [show s.length ≠ 1 by grind]
    rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by grind)]
    simp [EraseIdx.eq.Append_Drop_Add_1]
    simp [show s.length - 1 - (s.length - 2) = 1 by omega]
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    rw [DropLast.eq.Take_SubLength_1]


-- created on 2026-01-10
-- updated on 2026-07-10
