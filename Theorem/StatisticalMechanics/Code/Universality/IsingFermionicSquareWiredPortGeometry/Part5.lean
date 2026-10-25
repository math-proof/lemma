/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredPortIntPosition_directionDart
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortIntPosition n
        (fkIsingSquareDirectionDart n u d hd turn) =
      (4 * u.1 0, 4 * u.1 1) +
        fkIsingSquareWiredPortOffset d turn := by
  cases d <;> cases turn <;>
    simp [fkIsingSquareWiredPortIntPosition, fkIsingSquareDirectionDart,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareWiredPortOffset,
      Prod.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail] <;> omega


end
end StatMech.Universality
