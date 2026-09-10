import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
open Matrix Tensor


@[main]
private lemma main
  [CommRing α]
-- given
  (A : Tensor α [n, n])
  (B : Tensor α [n, n]) :
-- imply
  (A @ B).det = A.det * B.det := by
-- proof
  apply Eq.trans (congrArg (id (α := Tensor α [])) (Det.eq.DetToMatrix (A @ B)))
  rw [ToMatrixDot.eq.MulToMatrixS, det_mul]
  rw [← Det.eq.DetToMatrix A, ← Det.eq.DetToMatrix B]
  rfl


-- created on 2020-08-20
-- updated on 2026-09-07
