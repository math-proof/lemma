import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import sympy.tensor.tensor
open List Bool


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length < s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  X.tensordot Y ≃ (X.reshape (s'.take (s'.length - s.length) ++ s ++ [m, n]) (by simp)).matmul Y (by grind) := by
-- proof
  unfold Tensor.tensordot
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
      rw [ZipWith_Append.eq.AppendZipWithS]
      apply EqAppendS.of.Eq
      simp
  ·
    rfl


-- created on 2026-01-11
