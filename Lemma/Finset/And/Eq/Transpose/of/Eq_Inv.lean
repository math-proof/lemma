import Mathlib.LinearAlgebra.Matrix.SchurComplement
import sympy.sets.sets
import sympy.Basic
open Matrix


@[path]
private lemma main
  {n m : ℕ}
  {Lx Sx : Matrix (Fin n) (Fin n) ℝ}
  {Ly Sy : Matrix (Fin m) (Fin m) ℝ}
  {Lxy Sxy : Matrix (Fin n) (Fin m) ℝ}
-- given
  (hx : IsUnit Sx.det)
  (hy : IsUnit Sy.det)
  (h : Matrix.fromBlocks Lx Lxy Lxyᵀ Ly = (Matrix.fromBlocks Sx Sxy Sxyᵀ Sy)⁻¹) :
-- imply
  Lx = (Sx - Sxy * Sy⁻¹ * Sxyᵀ)⁻¹ ∧ Ly = (Sy - Sxyᵀ * Sx⁻¹ * Sxy)⁻¹ ∧
    Lxy = -Sx⁻¹ * Sxy * Ly ∧ Lxyᵀ = -Sy⁻¹ * Sxyᵀ * Lx := by
-- proof
  by_cases hS : IsUnit (Matrix.fromBlocks Sx Sxy Sxyᵀ Sy).det
  · let _ := Matrix.invertibleOfIsUnitDet Sx hx
    let _ := Matrix.invertibleOfIsUnitDet Sy hy
    let _ := Matrix.invertibleOfIsUnitDet _ hS
    have h1 : IsUnit (Sx - Sxy * ⅟Sy * Sxyᵀ).det := by
      have := hS
      rw [Matrix.det_fromBlocks₂₂] at this
      exact isUnit_of_mul_isUnit_right this
    have h2 : IsUnit (Sy - Sxyᵀ * ⅟Sx * Sxy).det := by
      have := hS
      rw [Matrix.det_fromBlocks₁₁] at this
      exact isUnit_of_mul_isUnit_right this
    let _ := Matrix.invertibleOfIsUnitDet _ h1
    let _ := Matrix.invertibleOfIsUnitDet _ h2
    have e1 := Matrix.invOf_fromBlocks₂₂_eq Sx Sxy Sxyᵀ Sy
    have e2 := Matrix.invOf_fromBlocks₁₁_eq Sx Sxy Sxyᵀ Sy
    simp only [Matrix.invOf_eq_nonsing_inv] at e1 e2
    obtain ⟨a1, b1, c1, d1⟩ := Matrix.fromBlocks_inj.mp (h.trans e1)
    obtain ⟨a2, b2, c2, d2⟩ := Matrix.fromBlocks_inj.mp (h.trans e2)
    refine ⟨a1, d2, ?_, ?_⟩
    · rw [b2, d2, Matrix.neg_mul, Matrix.neg_mul]
    · rw [c1, a1, Matrix.neg_mul, Matrix.neg_mul]
  · have h0 : (Matrix.fromBlocks Sx Sxy Sxyᵀ Sy)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hS
    rw [h0, ← Matrix.fromBlocks_zero] at h
    obtain ⟨a, b, c, d⟩ := Matrix.fromBlocks_inj.mp h
    let _ := Matrix.invertibleOfIsUnitDet Sx hx
    let _ := Matrix.invertibleOfIsUnitDet Sy hy
    have s1 : ¬IsUnit (Sx - Sxy * Sy⁻¹ * Sxyᵀ).det := by
      intro hu
      apply hS
      rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
      exact hy.mul hu
    have s2 : ¬IsUnit (Sy - Sxyᵀ * Sx⁻¹ * Sxy).det := by
      intro hu
      apply hS
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
      exact hx.mul hu
    rw [Matrix.nonsing_inv_apply_not_isUnit _ s1, Matrix.nonsing_inv_apply_not_isUnit _ s2, a, c, b, d]
    simp


-- created on 2023-04-30
