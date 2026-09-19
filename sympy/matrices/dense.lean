import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import torch.Tensor
open scoped Matrix


/--
Convert a rank-2 `Tensor` to a mathlib `Matrix` of scalar tensors.

Mirrors [sympy.Matrix](https://github.com/sympy/sympy/blob/master/sympy/matrices/dense.py#L144).
-/
def Tensor.toMatrix (X : Tensor α [m, n]) : Matrix (Fin m) (Fin n) (Tensor α []) :=
  fun i j => X[i, j]


class PosDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  pd : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)


class NegDefAsymm {α : Type*} [Fintype α] (A : Matrix α α ℝ) : Prop where
  nd : PosDefAsymm (-A)


noncomputable instance [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) [PosDefAsymm A] :
    Invertible A.det := by
  apply invertibleOfNonzero
  apply isUnit_iff_ne_zero.mp
  apply A.isUnit_iff_isUnit_det.mp
  apply Matrix.isUnit_toLin'_iff.mp
  apply A.toLin'.isUnit_iff_ker_eq_bot.mpr
  apply Matrix.ker_toLin'_eq_bot_iff.mpr
  intro x hx
  by_contra h
  have hA : PosDefAsymm A := by infer_instance
  have hA := hA.pd x h
  have : x ⬝ᵥ A *ᵥ x = 0 := by
    rw [hx]
    simp
  linarith


noncomputable instance [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) [PosDefAsymm A] :
    Invertible A :=
  Matrix.invertibleOfDetInvertible A


noncomputable instance [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) [NegDefAsymm A] :
    Invertible A.det := by
  apply invertibleOfNonzero
  apply isUnit_iff_ne_zero.mp
  apply A.isUnit_iff_isUnit_det.mp
  apply Matrix.isUnit_toLin'_iff.mp
  apply A.toLin'.isUnit_iff_ker_eq_bot.mpr
  apply Matrix.ker_toLin'_eq_bot_iff.mpr
  intro x hx
  by_contra h
  have hA : PosDefAsymm (-A) := (inferInstance : NegDefAsymm A).nd
  have hA := hA.pd x h
  have : x ⬝ᵥ (-A) *ᵥ x = 0 := by
    rw [Matrix.neg_mulVec, hx]
    simp
  linarith


noncomputable instance [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) [NegDefAsymm A] :
    Invertible A :=
  Matrix.invertibleOfDetInvertible A
