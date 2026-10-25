/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredTangentCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredObservationCorrection (n : Nat) :
    FKIsingSquareWiredCarrier n → Int
  | .dart d | .bond d =>
      match (fkIsingSquareSideCorner d.2).2 with
      | .counterclockwise => 0
      | .clockwise => 4
  | .source | .terminal => 0


def fkIsingSquareWiredDirectedTangentCode (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareWiredCarrier n) : Int :=
  fkIsingSquareWiredCarrierTangentCode n hn x +
    fkIsingSquareWiredObservationCorrection n x

end
end StatMech.Universality
