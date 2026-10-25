/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryRay.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredPrimitiveIncrement
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Real :=
  isingPrimitiveIncrement
    ((fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z)

end
end StatMech.Universality
