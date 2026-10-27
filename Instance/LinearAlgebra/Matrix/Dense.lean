import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Instance.Data.Holor.Tensor.Part2
import Class.LinearAlgebra.Matrix.Dense
open scoped Matrix


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

