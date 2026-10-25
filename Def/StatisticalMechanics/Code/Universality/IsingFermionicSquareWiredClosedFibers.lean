/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredClosedFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable def fkIsingSquareWiredClosedComponentToPrimal
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig ∅)).ConnectedComponent →
      (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).ConnectedComponent :=
  fun C => (openSub (fkSquareBoxPlanar n).G (FK.edgeSetConfig ∅) ⊔
    (fkIsingSquareWiredDobrushinDomain n hn).wiring).connectedComponentMk
      (fkIsingSquareWiredCarrierPrimalLabel n hn C.out)

end StatMech.Universality
