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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part18


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredDartPhysicalBlackEquiv (n : Nat) :
    FKIsingMedialDart (fkSquareBoxPlanar n) ≃
      FKIsingSquareWiredPhysicalBlackCarrier n :=
  Equiv.ofBijective (fkIsingSquareWiredPhysicalBlackOfDart n)
    (fkIsingSquareWiredPhysicalBlackOfDart_bijective n)


noncomputable def fkIsingSquareWiredPhysicalBlackPortIntPosition (n : Nat) :
    FKIsingSquareWiredPhysicalBlackCarrier n → Int × Int :=
  fkIsingSquareWiredPortIntPosition n ∘
    (fkIsingSquareWiredDartPhysicalBlackEquiv n).symm

end
end StatMech.Universality
