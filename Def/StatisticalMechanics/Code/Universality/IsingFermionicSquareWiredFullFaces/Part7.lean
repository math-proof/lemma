/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

noncomputable def fkIsingSquareWiredFullLeftCycle
    (n : Nat) (hn : 0 < n) :
    Fin (2 * n) → StatMech.FrontierA.PermCycleClass
      (fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) :=
  fun k ↦ Quot.mk _ (fkIsingSquareWiredFullLeftDart n hn k)

end
end StatMech.Universality
