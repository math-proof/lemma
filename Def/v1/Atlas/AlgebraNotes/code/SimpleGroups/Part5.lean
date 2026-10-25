/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part3


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable def longitudeMap : Multiplicative (AddCircle (2 * Real.pi)) →* longitudeI where
  toFun x := Quotient.lift diagRotationToLongI
    diagRotationToLongI_periodic (Multiplicative.toAdd x)
  map_one' := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (0 : AddCircle (2 * Real.pi)) = 1
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (QuotientAddGroup.mk 0) = 1
    simp only [Quotient.lift_mk, diagRotationToLongI]
    ext1; ext1
    exact diagRotation_zero
  map_mul' x y := by
    show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
      (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd x) *
      Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (Multiplicative.toAdd y)
    induction Multiplicative.toAdd x using Quotient.inductionOn with
    | h a =>
      induction Multiplicative.toAdd y using Quotient.inductionOn with
      | h b =>
        show Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk a + QuotientAddGroup.mk b) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        change Quotient.lift diagRotationToLongI diagRotationToLongI_periodic
          (QuotientAddGroup.mk (a + b)) =
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk a) *
          Quotient.lift diagRotationToLongI diagRotationToLongI_periodic (QuotientAddGroup.mk b)
        simp only [Quotient.lift_mk, diagRotationToLongI]
        ext1; ext1
        exact (diagRotation_add a b).symm

def SL2.HasEigenvalues (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  (↑M : Matrix (Fin 2) (Fin 2) F).charpoly =
    (Polynomial.X - Polynomial.C s) * (Polynomial.X - Polynomial.C s⁻¹)

def SL2.IsConjToDiag (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
    (P * M * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Matrix.diagonal ![s, s⁻¹]

end OneParamSubgroupTheorem
end SimpleGroups
