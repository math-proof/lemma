/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredCarrierPhase (n : Nat) :
    FKIsingSquareWiredCarrier n → Fin 4
  | .source => 0
  | .terminal => 1
  | .dart d =>
      if (fkIsingSquareSideCorner d.2).2 = .clockwise then 2 else 3
  | .bond d =>
      if (fkIsingSquareSideCorner d.2).2 = .clockwise then 1 else 0

end
end StatMech.Universality
