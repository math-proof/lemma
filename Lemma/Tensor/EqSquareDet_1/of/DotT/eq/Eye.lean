import Instance.Algebra.Polynomial.Polyroots
import Notation.Data.Tensor.Permute
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import Lemma.Tensor.ToMatrixEye.eq.One
import Lemma.Tensor.ToMatrixT.eq.TToMatrix
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  [CommRing α] [CharZero α]
  {X : Tensor α [n, n]}
-- given
  (h : Xᵀ ⬝ᵥ X = Tensor.eye (α := α) n) :
-- imply
  X.det² = 1 := by
-- proof
  let XT : Tensor α [n, n] := Xᵀ
  have h' : XT ⬝ᵥ X = Tensor.eye (α := α) n := h
  have hm : (XT ⬝ᵥ X).toMatrix = (Tensor.eye (α := α) n).toMatrix :=
    congrArg Tensor.toMatrix h'
  rw [ToMatrixDot.eq.MulToMatrixS, ToMatrixT.eq.TToMatrix, ToMatrixEye.eq.One] at hm
  have hd : ((X.toMatrix).transpose * X.toMatrix).det = (1 : Matrix (Fin n) (Fin n) (Tensor α [])).det :=
    congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two, Matrix.det_one] at hd
  apply Eq.trans _ hd
  rw [Det.eq.DetToMatrix]
  rfl


-- created on 2026-09-07
