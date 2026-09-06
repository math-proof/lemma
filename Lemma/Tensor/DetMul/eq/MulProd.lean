import Mathlib.Data.Matrix.Mul
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Mul
import Lemma.Tensor.MulStack.eq.Stack_Mul
import Lemma.Tensor.Prod_0.eq.Prod_Get
import sympy.matrices.determinant
open Tensor Matrix
set_option maxHeartbeats 400000


@[main]
private lemma main
  [CommRing α]
-- given
  (a : Tensor α [n])
  (X : Tensor α [n, n]) :
-- imply
  ((([_ < n] a) * X).det : Tensor α []) = a.prod * id (α := Tensor α []) X.det := by
-- proof
  let ai : Fin n → Tensor α [] := fun i => id (α := Tensor α []) a[i]
  rw [MulStack.eq.Stack_Mul.fin X (fun _ : Fin n => a)]
  let Y : Tensor α [n, n] := [i < n] (a * id (α := Tensor α [n]) X[i])
  have h_mat : Y.toMatrix = (of fun i j => Mul.mul (ai j) (X.toMatrix i j)) := by
    ext i j
    simp [Tensor.toMatrix]
    have hrow := EqGetStack.fin (fun i : Fin n => a * id (α := Tensor α [n]) X[i]) i
    have hcell := GetMul.eq.MulGetS a (id (α := Tensor α [n]) X[i]) j
    have h1 : (Y[i][j] : Tensor α []) = ((a * id (α := Tensor α [n]) X[i])[j] : Tensor α []) :=
      congrArg (fun t : Tensor α [n] => (t[j] : Tensor α [])) hrow
    apply Eq.trans h1
    apply Eq.trans (by
      convert hcell
      rfl)
    apply Eq.of.EqDataS
    simp [HMul.hMul, Mul.mul]
    congr 1
  apply Eq.trans (Det.eq.DetToMatrix Y)
  rw [h_mat]
  apply Eq.trans (det_mul_row ai X.toMatrix)
  have h_prod : a.prod = ∏ i : Fin n, ai i := by
    apply Eq.trans (Prod_0.eq.Prod_Get a)
    congr
  rw [← h_prod]
  rw [Det.eq.DetToMatrix X]
  erw [Tensor.Mul]
  rfl


-- created on 2022-01-15
-- updated on 2026-09-06
