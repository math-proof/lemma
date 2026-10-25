/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part9


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (cells : Finset (Nat × Nat))
    (hCR : forall p, p ∈ cells -> IsingCellCRAt F p.1 p.2) :
    reflectedRadialCellRegionBoundaryIntegral mesh F cells = 0 := by
  unfold reflectedRadialCellRegionBoundaryIntegral
  apply Finset.sum_eq_zero
  intro p hp
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR p hp)


theorem fkIsingSquareBoundaryRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero
    (n m : Nat) (hn : 0 < n) (hm : m <= n) (mesh : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < m ∧ p.2 + 2 < m) :
    reflectedRadialCellRegionBoundaryIntegral mesh
      (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm)
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m p.1 p.2 hn hm (hinterior p hp).1 (hinterior p hp).2


theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
    reflectedRadialCellRegionBoundaryIntegral mesh
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn)
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n p.1 p.2 hn (hinterior p hp).1 (hinterior p hp).2


theorem
    fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero
    (n : Nat) (hn : 0 < n) (gridScale normalizationScale : Real)
    (cells : Finset (Nat × Nat))
    (hinterior : forall p, p ∈ cells ->
      p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
    reflectedRadialCellRegionBoundaryIntegral gridScale
      (fun i j =>
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
            n hn i j /
          (Real.sqrt (2 * normalizationScale) : Complex))
      cells = 0 := by
  apply reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR
  intro p hp
  exact (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n p.1 p.2 hn (hinterior p hp).1 (hinterior p hp).2).div_const _


theorem
    fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero
    (n i j : Nat) (hn : 0 < n)
    (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n)
    (gridScale normalizationScale : Real) :
    reflectedRadialBilinearCellPathIntegral gridScale
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn i j / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn (i + 1) j / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn i (j + 1) / (Real.sqrt (2 * normalizationScale) : Complex))
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
          n hn (i + 1) (j + 1) /
            (Real.sqrt (2 * normalizationScale) : Complex)) = 0 := by
  apply reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR
  exact (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    n i j hn hi hj).div_const _


end
end StatMech.Universality
