import sympy.polys.polyroots
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import Lemma.Tensor.ToMatrixEye.eq.One
import Lemma.Tensor.ToMatrixT.eq.TToMatrix
open Tensor Matrix


@[main]
private lemma main
  [CommRing α] [CharZero α]
  {X : Tensor α [n, n]}
-- given
  (h : Xᵀ @ X = Tensor.eye (α := α) n) :
-- imply
  X.det² = 1 := by
-- proof
  let XT : Tensor α [n, n] := Xᵀ
  have h' : XT @ X = Tensor.eye (α := α) n := h
  have hm : (XT @ X).toMatrix = (Tensor.eye (α := α) n).toMatrix :=
    congrArg Tensor.toMatrix h'
  rw [ToMatrixDot.eq.MulToMatrixS, ToMatrixT.eq.TToMatrix, ToMatrixEye.eq.One] at hm
  have hd : (X.toMatrixᵀ * X.toMatrix).det = (1 : Matrix (Fin n) (Fin n) (Tensor α [])).det :=
    congrArg Matrix.det hm
  rw [det_mul, det_transpose, ← pow_two, det_one] at hd
  apply Eq.trans _ hd
  rw [Det.eq.DetToMatrix]
  rfl


-- created on 2026-09-07
