/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalLocalClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalLocalClosed


namespace StatMech.Universality

open Complex

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredFullMedialObservable
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Complex :=
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (e, .west)) +
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (e, .east))

end
end StatMech.Universality
