import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Nat.EqMax.of.Ge
import Lemma.Nat.EqMax.of.Lt
import Lemma.Tensor.Einsum.as.Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.EqTensordotS.of.SEq.SEq
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
open Bool List Tensor Nat
set_option maxHeartbeats 1000000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
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
  let X' : Tensor α (batch_size ++ [m, n ⊔ n']) := cast (by simp) (X'.resize ⟨batch_size.length + 1, by grind⟩ (n ⊔ n'))
  let Y' : Tensor α (batch_size' ++ [n ⊔ n', k]) := cast (by simp) (Y'.resize ⟨batch_size'.length, by grind⟩ (n ⊔ n'))
  X.einsum Y ≃ (Tensor.tensordot X' Y') := by
-- proof
  intro batch_size batch_size' m n n' k X' Y'
  simp [X', Y', batch_size, batch_size', m, n, n', k]
  if h_n : s[s.length - 1] < s'[s'.length - 2] then
    have := Einsum.as.Tensordot.of.LtGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' h_n X Y
    apply this.trans
    apply SEq.of.Eq
    apply EqTensordotS.of.SEq.SEq
    ·
      apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
      apply SEqResizeS.of.SEq.EqValS.Eq
      ·
        grind
      ·
        grind
      ·
        rfl
    ·
      apply SEqCastS.of.SEq.Eq.Eq (by rwa [EqAppendTake__ListGet.of.GeLength_2]) (by grind)
      rw [EqMax.of.Lt h_n]
      rw [ResizeCast.eq.Cast_Resize.of.Eq]
      ·
        symm
        apply SEqCast.of.SEq.Eq
        ·
          simp
          rwa [EqAppendTake__ListGet.of.GeLength_2]
        ·
          apply SEqResize.of.Eq_Get (i := ⟨(s'.take (s'.length - 2)).length, by grind⟩)
          simp
      ·
        rwa [EqAppendTake__ListGet.of.GeLength_2]
  else
    have := Einsum.as.Tensordot.of.GeGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' (by omega) X Y
    apply this.trans
    apply SEq.of.Eq
    apply EqTensordotS.of.SEq.SEq
    ·
      apply SEqCastS.of.SEq.Eq.Eq (by rwa [EqAppendTake__ListGet.of.GeLength_2]) (by simp)
      rw [EqMax.of.Ge (by omega)]
      rw [ResizeCast.eq.Cast_Resize.of.Eq]
      ·
        symm
        apply SEqCast.of.SEq.Eq
        ·
          simp
          rw [EqAppendTake__ListGet.of.GeLength_2 (by grind)]
          rw [AddSub.eq.Sub_Sub.of.Ge.Ge (by grind) (by simp)]
          simp
        ·
          apply SEqResize.of.Eq_Get (i := ⟨(s.take (s.length - 2)).length + 1, by grind⟩)
          grind
      ·
        rwa [EqAppendTake__ListGet.of.GeLength_2]
    ·
      apply SEqCastS.of.SEq.Eq.Eq (by grind) (by grind)
      apply SEqResizeS.of.SEq.EqValS.Eq
      ·
        grind
      ·
        grind
      ·
        rfl


-- created on 2026-07-20
