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
  (h : s.length = s'.length)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  X.broadcast_matmul Y = X.broadcast_matmul_rec Y (by grind) := by
-- proof
  unfold Tensor.broadcast_matmul
  simp [h]


-- created on 2026-01-12
