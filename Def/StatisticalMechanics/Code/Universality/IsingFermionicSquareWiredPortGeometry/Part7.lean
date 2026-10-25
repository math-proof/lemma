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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredBondArcLength
    (n : Nat) (u : (fkSquareBoxPlanar n).V) :
    FKIsingSquareDirection → Fin 8 := by
  classical
  exact fun d => match d with
  | .east => if fkIsingSquareDirectionAvailable n u .north then 1
      else if fkIsingSquareDirectionAvailable n u .west then 3 else 5
  | .north => if fkIsingSquareDirectionAvailable n u .west then 1
      else if fkIsingSquareDirectionAvailable n u .south then 3 else 5
  | .west => if fkIsingSquareDirectionAvailable n u .south then 1
      else if fkIsingSquareDirectionAvailable n u .east then 3 else 5
  | .south => if fkIsingSquareDirectionAvailable n u .east then 1
      else if fkIsingSquareDirectionAvailable n u .north then 3 else 5

end
end StatMech.Universality
