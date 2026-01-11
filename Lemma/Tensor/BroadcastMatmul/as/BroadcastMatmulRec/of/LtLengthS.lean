import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.ZipWith_AppendS.eq.AppendZipWithS
import sympy.tensor.tensor
open Bool List


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length < s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  X.broadcast_matmul Y ≃ (X.broadcast (s'.take (s'.length - s.length) ++ s ++ [m, n]) (by simp)).broadcast_matmul_rec Y (by grind) := by
-- proof
  unfold Tensor.broadcast_matmul
  simp [h]
  apply SEqCast.of.SEq.Eq
  ·
    simp [Tensor.broadcast_shape]
    split_ifs with h₀ h₁
    ·
      omega
    ·
      omega
    ·
      simp
      rw [Append_Append.eq.AppendAppend]
      apply EqAppendS.of.Eq
      have h_s := EqAppendTake__Drop s' (s'.length - s.length)
      conv_lhs =>
        arg 3
        rw [← h_s]
      rw [ZipWith_AppendS.eq.AppendZipWithS (by rfl)]
      apply EqAppendS.of.Eq
      simp
  ·
    rfl


-- created on 2026-01-11
