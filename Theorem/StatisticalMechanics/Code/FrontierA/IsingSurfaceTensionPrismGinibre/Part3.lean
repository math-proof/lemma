/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part3
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem abs_oddPrismDobrushinField_le_plusField
    (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    |oddPrismDobrushinField n v| <= oddPrismPlusField n v := by
  unfold oddPrismDobrushinField oddPrismPlusField
    oddRectangularPrismDobrushinSign
  by_cases hz : n < v.z.val <;>
    simp [hz, abs_of_nonneg
      (Nat.cast_nonneg (rectangularPrismBoundaryDegree v) :
        0 <= (rectangularPrismBoundaryDegree v : Real))]

theorem sum_oddPrismPlusField_spin
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ v, oddPrismPlusField n v * spin sigma v) =
      rectangularPrismPlusBoundaryInteraction sigma := by
  unfold oddPrismPlusField rectangularPrismPlusBoundaryInteraction
  rfl

theorem sum_oddPrismDobrushinField_spin
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ v, oddPrismDobrushinField n v * spin sigma v) =
      oddRectangularPrismDobrushinFaceInteraction n sigma := by
  simpa [oddPrismDobrushinField, mul_assoc] using
    rectangularPrismDobrushinBoundaryInteraction_eq_faces n sigma

theorem oddPrism_plus_inhomogeneousInteraction
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    inhomogeneousInteraction (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) sigma =
      -rectangularPrismPlusEnergy 1 sigma := by
  unfold inhomogeneousInteraction rectangularPrismPlusEnergy
  simp only [one_mul]
  rw [sum_oddPrismInternalEdges_bond, sum_oddPrismPlusField_spin]
  simp

theorem oddPrism_dobrushin_inhomogeneousInteraction
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    inhomogeneousInteraction (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismDobrushinField n) sigma =
      -oddRectangularPrismDobrushinEnergy 1 n sigma := by
  unfold inhomogeneousInteraction oddRectangularPrismDobrushinEnergy
  simp only [one_mul]
  rw [sum_oddPrismInternalEdges_bond, sum_oddPrismDobrushinField_spin]
  simp

theorem scaledInhomogeneousPartition_oddPrismPlus
    (beta : Real) (n : Nat) :
    scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) beta =
      rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n := by
  unfold scaledInhomogeneousPartition ZJ rectangularPrismPlusPartition Z
  apply Finset.sum_congr rfl
  intro sigma _
  rw [scaled_wJ_eq_exp_interaction,
    oddPrism_plus_inhomogeneousInteraction]
  congr 1
  ring

theorem scaledInhomogeneousPartition_oddPrismDobrushin
    (beta : Real) (n : Nat) :
    scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismDobrushinField n) beta =
      rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  unfold scaledInhomogeneousPartition ZJ rectangularPrismDobrushinPartition
    monomialInteractionPartition
  apply Finset.sum_congr rfl
  intro sigma _
  rw [scaled_wJ_eq_exp_interaction,
    oddPrism_dobrushin_inhomogeneousInteraction,
    sum_rectangularPrismDobrushinCoupling_eq]
  congr 1
  ring

theorem boundaryInterfaceFreeEnergy_oddPrism_eq
    (beta : Real) (n : Nat) :
    boundaryInterfaceFreeEnergy (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) (oddPrismDobrushinField n) beta =
      StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  unfold boundaryInterfaceFreeEnergy
  rw [scaledInhomogeneousPartition_oddPrismPlus,
    scaledInhomogeneousPartition_oddPrismDobrushin,
    StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio]


end
end StatMech.FrontierA
