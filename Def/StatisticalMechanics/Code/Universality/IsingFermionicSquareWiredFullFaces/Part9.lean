/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

noncomputable def fkIsingSquareWiredFullCycle
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredFullCycleIndex n →
      StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset))
  | Sum.inl c => fkIsingSquareWiredFullInteriorCycle n hn c
  | Sum.inr (some k) => fkIsingSquareWiredFullLeftCycle n hn k
  | Sum.inr none => Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n)

end
end StatMech.Universality
