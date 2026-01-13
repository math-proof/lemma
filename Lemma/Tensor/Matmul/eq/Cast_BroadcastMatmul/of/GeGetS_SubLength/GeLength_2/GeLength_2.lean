import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqMulDiv
import Lemma.Tensor.Append.eq.Cast.of.Eq_0
import Lemma.Tensor.EqBroadcastMatmulS.of.Eq.Eq
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Repeat.eq.Cast.of.EqMul_Get
open Bool List Nat Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length ≥ 2)
  (h_s' : s'.length ≥ 2)
  (h_n : s[s.length - 1] ≥ s'[s'.length - 2])
  (X : Tensor α s)
  (Y : Tensor α s') :
-- imply
  X.matmul Y =
    let batch_size := s.take (s.length - 2)
    let batch_size' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let X : Tensor α (batch_size ++ [m, n]) := cast
      (by
        congr
        simp [batch_size, m, n]
        conv_lhs => rw [← EqAppendTake__Drop s (s.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s
      )
      X
    let Y : Tensor α (batch_size' ++ [n', k]) := cast
      (by
        congr
        simp [batch_size', n', k]
        conv_lhs => rw [← EqAppendTake__Drop s' (s'.length - 2)]
        apply EqAppendS.of.Eq.left
        apply Drop.eq.ListGetS.of.GeLength_2 h_s'
      )
      Y
    let q := n / n'
    let r := n % n'
    let Y : Tensor α (batch_size' ++ [n, k]) := cast
      (by simp [q, r, EqAddMulDiv])
      ((cast (by simp [batch_size']) (Y.repeat q ⟨s'.length - 2, by simp [batch_size']⟩) : Tensor α (batch_size' ++ [q * n', k])) ++ (0 : Tensor α (batch_size' ++ [r, k])))
    cast
      (by
        congr
        simp [batch_size, batch_size', m, k, Tensor.matmul_shape, Tensor.broadcast_shape]
        grind
      )
      (Tensor.broadcast_matmul X Y) := by
-- proof
  if h_n_eq : s[s.length - 1] = s'[s'.length - 2] then
    have := Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' h_n_eq X Y
    simp_all
    apply EqBroadcastMatmulS.of.Eq.Eq
    ·
      rfl
    ·
      apply EqCastS.of.SEq.Eq
      ·
        simp [h_n_eq]
        apply EqMulDiv
      ·
        rw [Append.eq.Cast.of.Eq_0]
        ·
          simp
          apply SEq_Cast.of.SEq.Eq
          ·
            simp_all
          ·
            rw [Repeat.eq.Cast.of.EqMul_Get]
            ·
              simp
              apply SEq_Cast.of.SEq.Eq
              ·
                simp_all [EqMulDiv]
                rw [ListGetS.eq.Drop.of.GeLength_2 h_s']
                simp
              ·
                rfl
            ·
              simp_all
              apply EqMulDiv
        ·
          simp_all
  else
    apply Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2 h_s h_s' (by omega) X Y


-- created on 2026-01-13
