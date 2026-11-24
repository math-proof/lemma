module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part28


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
