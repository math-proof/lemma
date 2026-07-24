import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Append.of.Eq
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
  X.tensordot Y = X.matmul Y (by grind) := by
-- proof
  unfold Tensor.tensordot
  simp [h]


-- created on 2026-01-12
