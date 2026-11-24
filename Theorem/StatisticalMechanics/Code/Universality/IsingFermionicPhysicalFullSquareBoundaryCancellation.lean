module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquarePerimeterDirection_available
    (n : Nat) (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareBoundaryVertex n (side, k))
      (fkIsingSquarePerimeterDirection side) := by
  have hk := k.isLt
  cases side <;>
    simp [fkIsingSquarePerimeterDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] <;> omega


end
end StatMech.Universality
