import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import torch.Tensor.permute
import torch.linalg.inv
import torch.functions
import Lemma.Tensor.Dot.eq.Eye.of.Dot.eq.Eye
import Lemma.Tensor.DotT_RotaryMatrix.eq.Eye
import Lemma.Tensor.Eq.is.ToMatrix
import Lemma.Tensor.EqToMatrixStack
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
import Lemma.Tensor.ToMatrixEye.eq.One
import Lemma.Tensor.ToMatrixT.eq.TToMatrix
open Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix.inv = θ.rotaryMatrixᵀ := by
-- proof
  apply Eq.of.ToMatrix
  have hleft : (θ.rotaryMatrix.inv).toMatrix = (θ.rotaryMatrix.toMatrix)⁻¹ := by
    unfold Tensor.inv
    simpa using EqToMatrixStack (f := fun i j => (θ.rotaryMatrix.toMatrix)⁻¹ i j)
  have hright : θ.rotaryMatrixᵀ.toMatrix = (θ.rotaryMatrix.toMatrix).transpose :=
    ToMatrixT.eq.TToMatrix θ.rotaryMatrix
  have hortho : θ.rotaryMatrix @ θ.rotaryMatrixᵀ = Tensor.eye (d + d) :=
    Dot.eq.Eye.of.Dot.eq.Eye (DotT_RotaryMatrix.eq.Eye θ)
  have hdot : (θ.rotaryMatrix @ θ.rotaryMatrixᵀ).toMatrix =
      θ.rotaryMatrix.toMatrix * (θ.rotaryMatrix.toMatrix).transpose := by
    apply Eq.trans (ToMatrixDot.eq.MulToMatrixS θ.rotaryMatrix θ.rotaryMatrixᵀ)
    exact congrArg (fun M => θ.rotaryMatrix.toMatrix * M) hright
  have hmul : θ.rotaryMatrix.toMatrix * (θ.rotaryMatrix.toMatrix).transpose =
      (1 : Matrix (Fin (d + d)) (Fin (d + d)) (Tensor ℝ [])) := by
    apply Eq.trans hdot.symm
    apply Eq.trans (congrArg toMatrix hortho)
    exact ToMatrixEye.eq.One
  have hinv : (θ.rotaryMatrix.toMatrix)⁻¹ = (θ.rotaryMatrix.toMatrix).transpose :=
    Matrix.inv_eq_right_inv hmul
  exact Eq.trans hleft (Eq.trans hinv hright.symm)


-- created on 2026-09-17
