/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Abelian
import Theorem.v1.Atlas.LieGroups.code.SL2Basics
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

def SO2 : Subgroup SL2R where
  carrier := {A | (↑A : M2).transpose * ↑A = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    rw [Matrix.transpose_mul]
    have : (↑b : M2).transpose * (↑a : M2).transpose * ((↑a : M2) * (↑b : M2)) =
           (↑b : M2).transpose * ((↑a : M2).transpose * (↑a : M2)) * (↑b : M2) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [this, ha, Matrix.mul_one, hb]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_one,
               Matrix.transpose_one, Matrix.mul_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    set A : M2 := ↑a with hA
    have hdet : A.det = 1 := a.2
    have hAdj : (↑(a⁻¹) : M2) = A.adjugate := Matrix.SpecialLinearGroup.coe_inv a
    rw [hAdj]
    have htrans_eq : A.transpose = A.adjugate := by
      have h1 : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
      calc A.transpose
          = A.transpose * (A * A.adjugate) := by rw [h1, Matrix.mul_one]
        _ = (A.transpose * A) * A.adjugate := by rw [Matrix.mul_assoc]
        _ = 1 * A.adjugate := by rw [ha]
        _ = A.adjugate := by rw [Matrix.one_mul]
    rw [← htrans_eq, Matrix.transpose_transpose, htrans_eq,
        Matrix.mul_adjugate, hdet, one_smul]

def IwasawaA : Subgroup SL2R where
  carrier := {A | ∃ a : ℝ, 0 < a ∧ (↑A : M2) = !![a, 0; 0, a⁻¹]}
  mul_mem' := by
    intro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul, hxa, hyb]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  one_mem' := by
    refine ⟨1, one_pos, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_mem' := by
    intro x ⟨a, ha, hxa⟩
    refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hxa]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]

def IwasawaN : Subgroup SL2R where
  carrier := {A | ∃ x : ℝ, (↑A : M2) = !![1, x; 0, 1]}
  mul_mem' := by
    intro a b ⟨x, hxa⟩ ⟨y, hyb⟩
    refine ⟨x + y, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul, hxa, hyb]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  one_mem' := by
    refine ⟨0, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_mem' := by
    intro a ⟨x, hxa⟩
    refine ⟨-x, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hxa]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one]

def lieAlgK : Submodule ℝ M2 where
  carrier := {X | X.transpose = -X ∧ X.trace = 0}
  add_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Matrix.transpose_add, ha1, hb1, neg_add],
           by rw [Matrix.trace_add, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨by simp, Matrix.trace_zero (Fin 2) ℝ⟩
  smul_mem' := by
    intro c a ⟨ha1, ha2⟩
    exact ⟨by rw [Matrix.transpose_smul, ha1, smul_neg],
           by rw [Matrix.trace_smul, ha2, smul_zero]⟩

def lieAlgP : Submodule ℝ M2 where
  carrier := {X | X.transpose = X ∧ X.trace = 0}
  add_mem' := by
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Matrix.transpose_add, ha1, hb1],
           by rw [Matrix.trace_add, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨Matrix.transpose_zero, Matrix.trace_zero (Fin 2) ℝ⟩
  smul_mem' := by
    intro c a ⟨ha1, ha2⟩
    exact ⟨by rw [Matrix.transpose_smul, ha1],
           by rw [Matrix.trace_smul, ha2, smul_zero]⟩

end
