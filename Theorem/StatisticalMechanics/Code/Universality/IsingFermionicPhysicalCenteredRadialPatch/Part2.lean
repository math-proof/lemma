module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareCenteredRadialPatchDirection_available
    (n : Nat) (i j : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n i j)
      (fkIsingSquareCenteredRadialPatchDirection i.1 j.1) := by
  have hi := i.2
  have hj := j.2
  by_cases h : Even (i.1 + j.1)
  · simp [fkIsingSquareCenteredRadialPatchDirection, h,
      fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
    omega
  · simp [fkIsingSquareCenteredRadialPatchDirection, h,
      fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
    omega


end
end StatMech.Universality
