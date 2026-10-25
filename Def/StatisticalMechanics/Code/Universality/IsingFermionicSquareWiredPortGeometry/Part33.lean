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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part31


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredPortMacroVertexWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    List (FKIsingSquareWiredExpandedCarrier n) :=
  match d.2 with
  | .west | .east => [.inl (fkIsingSquareWiredDartSlot n d)]
  | .south =>
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map Sum.inl
  | .north =>
      match fkIsingSquareWiredBoundaryNorthIndex n hn d with
      | some k => [fkIsingSquareWiredExpandedEnd n hn k,
          fkIsingSquareWiredExpandedMiddle n hn k, .inr k]
      | none =>
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map Sum.inl

end
end StatMech.Universality
