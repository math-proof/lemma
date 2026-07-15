import Lemma.Bool.EqCast.of.SEq
import Lemma.Nat.EqMax
import Lemma.Tensor.SEqResize.of.Eq_Get
open Bool Nat Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [m, n])
  (Y : Tensor α [n, k]) :
-- imply
  let X : Tensor α ([] ++ [m, n]) := X
  X.tensordot Y (s' := []) = X.bmm Y := by
-- proof
  unfold Tensor.tensordot
  simp
  unfold Tensor.matmul
  rfl


-- created on 2026-07-15
