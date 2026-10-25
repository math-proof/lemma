import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part2
open Pointwise


/-- An invertible matrix defines a linear equivalence on Euclidean space. -/
noncomputable def Matrix.linear_equiv {d:ℕ} (A: Matrix (Fin d) (Fin d) ℝ) [Invertible A] :
EuclideanSpace' d ≃ₗ[ℝ] EuclideanSpace' d where
  toFun x := .toLp 2 (toLin' A x.ofLp)
  map_add' x y := by
    apply PiLp.ext; intro i; simp [map_add]
  map_smul' r x := by
    apply PiLp.ext; intro i; simp [map_smul]
  invFun x := .toLp 2 (toLin' A⁻¹ x.ofLp)
  left_inv x := by
    apply PiLp.ext; intro i; simp
  right_inv x := by
    apply PiLp.ext; intro i; simp

