import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.DetAppendHstackS.eq.PowNeg1
import Lemma.Tensor.Mul
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import sympy.matrices.determinant
import sympy.matrices.expressions.special
open Bool Matrix Tensor


private lemma det_eq_toMatrix_add_comm
  [CommRing α]
  {m n : ℕ}
  (X : Tensor α [m + n, n + m]) :
  (X.det : Tensor α []) = (cast (by simp [Nat.add_comm]) X : Tensor α [n + m, n + m]).toMatrix.det := by
  unfold Tensor.det
  rw [dif_neg (by simp : ¬[m + n, n + m].length > 2)]
  rw [dif_neg (by simp : ¬[m + n, n + m].length < 2)]
  simp [Nat.add_comm m n]


private lemma toMatrix_det_cast_square
  [CommRing α]
  {a b : ℕ}
  (h : a = b)
  (X : Tensor α [a, a]) :
  X.toMatrix.det = (cast (by rw [h]) X : Tensor α [b, b]).toMatrix.det := by
  subst h
  rfl


private lemma toMatrix_det_eq_toMatrix_det_cast
  [CommRing α]
  {m n : ℕ}
  (X : Tensor α [m + n, n + m]) :
  (cast (by simp [Nat.add_comm]) X : Tensor α [n + m, n + m]).toMatrix.det = (cast (congrArg (fun t => Tensor α [m + n, t]) (Nat.add_comm n m)) X).toMatrix.det := by
  apply Eq.trans (toMatrix_det_cast_square (Nat.add_comm n m) (cast (by simp [Nat.add_comm]) X : Tensor α [n + m, n + m]))
  apply congrArg Matrix.det
  apply congrArg Tensor.toMatrix
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  exact (cast_heq _ _).symm


@[main]
private lemma main
  [CommRing α] [CharZero α]
  {m n : ℕ}
-- given
  (A : Tensor α [m + n, m + n]) :
-- imply
  (A @ ((0 : Tensor α [m, n]).hstack (Tensor.eye m) ++ (Tensor.eye n).hstack (0 : Tensor α [n, m]))).det = (-1) ^ (m * n) * id (α := Tensor α []) A.det := by
-- proof
  let P := (0 : Tensor α [m, n]).hstack (Tensor.eye m) ++ (Tensor.eye n).hstack (0 : Tensor α [n, m])
  let Pcast : Tensor α [m + n, m + n] :=
    cast (congrArg (fun t => Tensor α [m + n, t]) (Nat.add_comm n m)) P
  have hs : [m + n, n + m] = [m + n, m + n] := by
    rw [Nat.add_comm n m]
  have hPcast : Pcast = cast (congrArg (Tensor α) hs) P := by
    simp [Pcast]
  have hdot : A @ P ≃ A @ Pcast := by
    rw [hPcast]
    exact SEqDotS.of.SEq.left (SEq_Cast.of.Eq hs P) A
  have hAP :
      cast (congrArg (fun t => Tensor α [m + n, t]) (Nat.add_comm n m)) (A @ P) =
        A @ Pcast := by
    apply Eq.trans _ (SEq.cast hdot)
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    exact (cast_heq _ _).symm
  apply Eq.trans (det_eq_toMatrix_add_comm (A @ P))
  apply Eq.trans (toMatrix_det_eq_toMatrix_det_cast (A @ P))
  rw [hAP]
  apply Eq.trans (congrArg Matrix.det (ToMatrixDot.eq.MulToMatrixS A Pcast))
  rw [det_mul]
  rw [← Det.eq.DetToMatrix A]
  have hP : Pcast.toMatrix.det = (P.det : Tensor α []) := by
    apply Eq.trans (toMatrix_det_eq_toMatrix_det_cast P).symm
    exact (det_eq_toMatrix_add_comm P).symm
  rw [hP, DetAppendHstackS.eq.PowNeg1]
  simp only [id]
  erw [mul_comm, Tensor.Mul]
  rfl


-- created on 2020-08-19
-- updated on 2026-09-06
