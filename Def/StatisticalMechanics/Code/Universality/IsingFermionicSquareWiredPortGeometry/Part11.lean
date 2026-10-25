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
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredExpandedIntPosition (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredExpandedCarrier n → Int × Int
  | .inl x => fkIsingSquareWiredSlotIntPosition n x
  | .inr k =>
      let u := fkIsingSquareLeftVerticalLower n hn k
      (4 * u.1 0 - 2, 4 * u.1 1 + 3)

end
end StatMech.Universality
