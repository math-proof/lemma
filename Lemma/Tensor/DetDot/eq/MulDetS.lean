import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
open Tensor


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
  rw [ToMatrixDot.eq.MulToMatrixS, Matrix.det_mul]
  rw [← Det.eq.DetToMatrix A, ← Det.eq.DetToMatrix B]
  rfl


@[main]
private lemma trois
  [CommRing α]
-- given
  (A B C : Tensor α [n, n]) :
-- imply
  ((A @ B : Tensor α [n, n]) @ C).det = A.det * B.det * C.det := by
-- proof
  exact (main (A @ B) C).trans (congrArg (· * C.det) (main A B))


-- created on 2020-08-20
-- updated on 2026-09-07
-- updated on 2026-09-27
