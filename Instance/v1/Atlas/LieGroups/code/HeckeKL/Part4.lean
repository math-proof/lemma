/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part3


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

instance HeckeAlgebra.instAlgebra (C : CoxeterGroupData) :
    Algebra HeckeCoeffRing (HeckeAlgebra C) where
  __ := HeckeAlgebra.instModule C
  algebraMap := heckeAlgebraMap C
  commutes' := by
    intro r x

    show heckeMul C (Finsupp.single 1 r) x = heckeMul C x (Finsupp.single 1 r)

    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun x => heckeMul C (Finsupp.single 1 r) x = heckeMul C x (Finsupp.single 1 r)) x
    ·
      simp only [show heckeMul C (Finsupp.single 1 r) 0 = 0 from by
        unfold heckeMul; have : ∀ (w₁ : C.W) (a₁ : HeckeCoeffRing),
          Finsupp.sum (0 : HeckeAlgebra C) (fun w₂ a₂ => (a₁ * a₂) • heckeMulBasis C w₁ w₂) = 0 :=
          fun _ _ => Finsupp.sum_zero_index
        rw [Finsupp.sum_single_index (by simp [zero_smul, Finsupp.sum])]

        simp [this]]
      simp only [show heckeMul C 0 (Finsupp.single 1 r) = 0 from Finsupp.sum_zero_index]
    ·
      intro x₁ x₂ h₁ h₂
      have hleft : ∀ (f g : HeckeAlgebra C),
          heckeMul C (Finsupp.single 1 r) (f + g) =
          heckeMul C (Finsupp.single 1 r) f + heckeMul C (Finsupp.single 1 r) g := by
        intro f g; unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        apply Finsupp.sum_add_index'
        · intro i; simp
        · intro i b₁ b₂; rw [mul_add, add_smul]
      have hright : ∀ (f g : HeckeAlgebra C),
          heckeMul C (f + g) (Finsupp.single 1 r) =
          heckeMul C f (Finsupp.single 1 r) + heckeMul C g (Finsupp.single 1 r) := by
        intro f g; unfold heckeMul
        apply Finsupp.sum_add_index'
        · intro i
          show (Finsupp.single 1 r).sum (fun w₂ a₂ => (0 * a₂) • heckeMulBasis C i w₂) = 0
          simp [zero_mul, zero_smul, Finsupp.sum]
        · intro i b₁ b₂
          conv_lhs => arg 2; ext w₂ a₂; rw [add_mul, add_smul]
          rw [← Finsupp.sum_add]
      rw [hleft, h₁, h₂, hright]
    ·
      intro w a

      have lhs_eq : heckeMul C (Finsupp.single 1 r) (Finsupp.single w a) =
          Finsupp.single w (r * a) := by
        unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
        have hb : heckeMulBasis C 1 w = Finsupp.single w 1 := by
          unfold heckeMulBasis; simp [C.length_one]
        rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]

      have rhs_eq : heckeMul C (Finsupp.single w a) (Finsupp.single 1 r) =
          Finsupp.single w (a * r) := by
        unfold heckeMul
        rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
        rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
        have hb : heckeMulBasis C w 1 = Finsupp.single w 1 :=
          heckeMulBasis_one_right C w
        rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [lhs_eq, rhs_eq]
      congr 1
      exact mul_comm r a
  smul_def' := by
    intro r x

    show r • x = heckeMul C (Finsupp.single 1 r) x
    apply @Finsupp.induction_linear C.W HeckeCoeffRing _
      (fun x => r • x = heckeMul C (Finsupp.single 1 r) x) x
    ·
      simp only [smul_zero]
      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_smul, Finsupp.sum])]

      simp [Finsupp.sum]
    ·
      intro x₁ x₂ h₁ h₂
      rw [smul_add, h₁, h₂]

      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      symm
      apply Finsupp.sum_add_index'
      · intro i; simp
      · intro i b₁ b₂; rw [mul_add, add_smul]
    ·
      intro w a
      rw [Finsupp.smul_single, smul_eq_mul]
      unfold heckeMul
      rw [Finsupp.sum_single_index (by simp [zero_mul, zero_smul, Finsupp.sum])]
      rw [Finsupp.sum_single_index (by simp [mul_zero, zero_smul])]
      have hb : heckeMulBasis C 1 w = Finsupp.single w 1 := by
        unfold heckeMulBasis; simp [C.length_one]
      rw [hb, Finsupp.smul_single, smul_eq_mul, mul_one]

end
