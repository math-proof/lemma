/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePrimalConnectivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSourcePhase.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareCarrierPrimalLabel (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> (fkSquareBoxPlanar n).V
  | .dart d => fkIsingSquareDartEndpoint n d
  | .source => fkIsingSquareMarkedA n
  | .terminal => fkIsingSquareMarkedB n

end
end StatMech.Universality
