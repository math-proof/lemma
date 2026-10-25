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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part13


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredLeftRingRemoved (n : Nat)
    (x : FKIsingSquareWiredSlotCarrier n) : Prop :=
  x.1.1 0 = -(n : Int) ∧
    (x.2 = 4 ∨ x.2 = 5 ∨ x.2 = 6 ∨
      (x.1.1 1 = -(n : Int) ∧ (x.2 = 7 ∨ x.2 = 0)) ∨
      (x.1.1 1 = (n : Int) ∧ (x.2 = 2 ∨ x.2 = 3)))


end
end StatMech.Universality
