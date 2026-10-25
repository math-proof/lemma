/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExhaustive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredExhaustiveCarrierPrimalLabel (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredCarrier n → (fkSquareBoxPlanar n).V
  | .dart d | .bond d => fkIsingSquareDartEndpoint n d
  | .source => fkIsingSquareMarkedA n
  | .terminal => fkIsingSquareMarkedB n

end
end StatMech.Universality
