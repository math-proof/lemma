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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part11


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredExpandedStart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalLower n hn k, 4)

def fkIsingSquareWiredExpandedMiddle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 6)

def fkIsingSquareWiredExpandedEnd
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 7)


end
end StatMech.Universality
