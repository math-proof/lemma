import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.ListGet.of.GeLength_1
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Tensor.EqReshapeMatmulS.of.Eq.Eq
import Lemma.Tensor.Matmul.as.ReshapeMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.ReshapeMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.ResizeCast.as.Resize.of.Eq
import Lemma.Tensor.SEqResize.of.Eq_Get
open Bool List Nat Tensor
set_option maxHeartbeats 1000000


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] ≥ s'[s'.length - 2])
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
  let Y' : Tensor α (batch_size' ++ [n, k]) := cast (by simp) (Y'.resize ⟨batch_size'.length, by grind⟩ n)
  X.einsum Y ≃ (Tensor.tensordot X' Y') := by
-- proof
  if h_n_eq : s[s.length - 1] = s'[s'.length - 2] then
    have := Matmul.as.ReshapeMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' h_n_eq X Y
    apply SEq.trans this
    apply SEq.of.Eq
    apply EqReshapeMatmulS.of.Eq.Eq
    ·
      rfl
    ·
      apply EqCastS.of.SEq.Eq
      ·
        simp [h_n_eq]
      ·
        rw [ResizeCast.eq.Cast_Resize.of.Eq]
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          simp_all
          rwa [EqAppendTake__ListGet.of.GeLength_2]
        ·
          simp
          rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by grind)]
          simp
          rw [AddSub.eq.Sub_Sub.of.Ge.Ge (by grind) (by grind)]
          simp
          rw [Drop.eq.ListGet.of.GeLength_1 (by grind)]
        ·
          simp
          symm
          apply SEqResize.of.Eq_Get (i := ⟨(s'.take (s'.length - 2)).length, by grind⟩)
          simpa
        ·
          rwa [EqAppendTake__ListGet.of.GeLength_2]
  else
    apply Matmul.as.ReshapeMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' (by omega) X Y


-- created on 2026-01-13
-- updated on 2026-07-10
