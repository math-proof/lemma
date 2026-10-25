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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part8


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredDartSlot (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkSquareBoxPlanar n).V × Fin 8 :=
  (fkIsingSquareDartEndpoint n d,
    fkIsingSquareWiredPortSlot (fkIsingSquareDartDirection n d)
      (fkIsingSquareSideCorner d.2).2)


def fkIsingSquareWiredSlotAvailable (n : Nat)
    (x : (fkSquareBoxPlanar n).V × Fin 8) : Prop :=
  fkIsingSquareDirectionAvailable n x.1
    (fkIsingSquareWiredPortSlotDirection x.2)


noncomputable def fkIsingSquareWiredDartOfSlot (n : Nat)
    (x : (fkSquareBoxPlanar n).V × Fin 8)
    (h : fkIsingSquareWiredSlotAvailable n x) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionDart n x.1
    (fkIsingSquareWiredPortSlotDirection x.2) h
    (fkIsingSquareWiredPortSlotTurn x.2)

end
end StatMech.Universality
