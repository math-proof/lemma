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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredExpandedBulgeEndpoints
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    Fin 3 → FKIsingSquareWiredExpandedCarrier n ×
      FKIsingSquareWiredExpandedCarrier n
  | 0 => (fkIsingSquareWiredExpandedStart n hn k, .inr k)
  | 1 => ((.inr k : FKIsingSquareWiredExpandedCarrier n),
      fkIsingSquareWiredExpandedMiddle n hn k)
  | 2 => (fkIsingSquareWiredExpandedMiddle n hn k,
      fkIsingSquareWiredExpandedEnd n hn k)


def fkIsingSquareWiredExpandedBulgeEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) (j : Fin 3) :
    Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
  s((fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).1,
    (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).2)


def fkIsingSquareWiredExpandedBulgeMidpoint
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) (j : Fin 3) : Int × Int :=
  fkIsingSquareWiredExpandedIntPosition n hn
      (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).1 +
    fkIsingSquareWiredExpandedIntPosition n hn
      (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).2


end
end StatMech.Universality
