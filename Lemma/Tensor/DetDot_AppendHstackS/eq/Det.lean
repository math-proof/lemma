import Lemma.Tensor.DetAppendHstackS.eq.MulDetS
import Lemma.Tensor.EqMul1
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import Lemma.Tensor.ToMatrixEye.eq.One
open Matrix Tensor


@[main]
private lemma main
  [CommRing α] [CharZero α]
-- given
  (A : Tensor α [n + n, n + n])
  (B : Tensor α [n, n]) :
-- imply
  (A @ ((Tensor.eye n).hstack B ++ (0 : Tensor α [n, n]).hstack (Tensor.eye n))).det = A.det := by
-- proof
  let I : Tensor α [n, n] := Tensor.eye n
  let P := I.hstack B ++ (0 : Tensor α [n, n]).hstack I
  apply Eq.trans (Det.eq.DetToMatrix (A @ P))
  rw [ToMatrixDot.eq.MulToMatrixS, det_mul]
  have hI : I.toMatrix.det = 1 := by
    rw [ToMatrixEye.eq.One]
    exact det_one
  have hP : P.toMatrix.det = 1 := by
    have h := DetAppendHstackS.eq.MulDetS.triu I I B
    rw [Det.eq.DetToMatrix P, Det.eq.DetToMatrix I] at h
    simp only [id] at h
    rw [h, hI]
    exact EqMul1 (1 : Tensor α [])
  rw [hP, mul_one]
  exact (Det.eq.DetToMatrix A).symm


-- created on 2020-08-18
-- updated on 2026-09-07
