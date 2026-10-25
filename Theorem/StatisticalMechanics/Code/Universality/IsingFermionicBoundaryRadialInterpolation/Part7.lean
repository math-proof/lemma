/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) :
    Continuous (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
      n m hn hm gridScale normalizationScale) :=
  finiteRadialGridInterpolant_continuous _ _ _

@[simp] theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin m) :
    fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
        n m hn hm gridScale normalizationScale
        (isingRadialGridPosition gridScale i.1 j.1) =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
        (Real.sqrt (2 * normalizationScale) : Complex) :=
  finiteRadialGridInterpolant_position m gridScale hgridScale _ i j


theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) (hgridScale : 0 < gridScale)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
      (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
        n m hn hm gridScale normalizationScale
        (isingRadialGridPosition gridScale i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) /
        (Real.sqrt (2 * normalizationScale) : Complex) := by
  rw [fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position
    _ _ _ _ _ _ hgridScale.ne']
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  rw [fkIsingSquareBoundaryRadialPatchFullObservable_projection]

end
end StatMech.Universality
