import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import sympy.tensor.tensor
open Bool List


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  X.broadcast_matmul Y ≃ X.broadcast_matmul_rec (Y.broadcast (s.take (s.length - s'.length) ++ s' ++ [n, k]) (by simp)) (by grind) := by
-- proof
  unfold Tensor.broadcast_matmul
  simp [h]
  split_ifs with h'
  ·
    omega
  ·
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
        rw [ZipWith__Append.eq.AppendZipWithS]
        apply EqAppendS.of.Eq
        simp
    ·
      rfl


-- created on 2026-01-11
