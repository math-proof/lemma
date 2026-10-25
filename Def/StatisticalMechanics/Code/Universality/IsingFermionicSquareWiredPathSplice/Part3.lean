/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice.Part3
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredCarrierOddClass (n : Nat) :
    FKIsingSquareWiredCarrier n → Prop
  | .source => False
  | .terminal => True
  | .dart d =>
      (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  | .bond d =>
      (fkIsingSquareSideCorner d.2).2 = .clockwise

end
end StatMech.Universality
