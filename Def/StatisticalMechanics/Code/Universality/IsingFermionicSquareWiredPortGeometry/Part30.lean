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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part28


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredRingArcContains
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) (i : Fin 8) : Prop :=
  ∃ j : Fin (fkIsingSquareWiredBondArcLength n u d).val,
    i = fkIsingSquareWiredPortSlot d .counterclockwise +
      ⟨j.val, lt_trans j.isLt
        (fkIsingSquareWiredBondArcLength n u d).isLt⟩


def fkIsingSquareWiredForwardRingSlotWord
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    List (FKIsingSquareWiredSlotCarrier n) :=
  let L := fkIsingSquareWiredBondArcLength n u d
  let start := fkIsingSquareWiredPortSlot d .counterclockwise
  List.ofFn fun j : Fin (L.val + 1) =>
    (u, start + ⟨j.val, by omega⟩)

end
end StatMech.Universality
