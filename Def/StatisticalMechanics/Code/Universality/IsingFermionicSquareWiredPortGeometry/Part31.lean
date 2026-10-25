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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part29


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredOrdinaryBondSlotVertexWord
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    List (FKIsingSquareWiredSlotCarrier n) :=
  let base := fkIsingSquareWiredBondArcBase n hn d
  let L := fkIsingSquareWiredBondArcLength n
    (fkIsingSquareDartEndpoint n base)
    (fkIsingSquareDartDirection n base)
  let start := (fkIsingSquareWiredDartSlot n base).2
  if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
    List.ofFn fun j : Fin L.val =>
      (fkIsingSquareDartEndpoint n base,
        start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
  else
    List.ofFn fun j : Fin L.val =>
      (fkIsingSquareDartEndpoint n base,
        start + ⟨L.val - j.val, by omega⟩)

end
end StatMech.Universality
