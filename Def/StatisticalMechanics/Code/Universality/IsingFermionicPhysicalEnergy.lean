/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalLocalClosed.Part2


namespace StatMech.Universality

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredObservableGrid
    (n : Nat) (hn : 0 < n)
    (carrier : Nat → Nat → FKIsingSquareWiredCarrier n) :
    Nat → Nat → Complex :=
  fun i j ↦ (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
    (carrier i j)


def fkIsingSquareWiredIntegratedPrimitive
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n) :
    Nat → Nat → Real :=
  isingRectanglePrimitive
    (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
      (horizontalCarrier i j))
    (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
      (verticalCarrier i j))

end
end StatMech.Universality
