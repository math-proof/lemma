/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredTangentCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredDirectedTangentCode_boundaryDart
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareWiredBoundaryDart n hn i)) =
      match i with
      | .bottom => 9
      | .west _ => 5
      | .north _ => 15
      | .top => 3 := by
  cases i <;>
    simp only [fkIsingSquareWiredBoundaryDart,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
  all_goals norm_num [fkIsingSquareCornerTangentCode,
    FKIsingSquareDirection.eighthTurn]

end
end StatMech.Universality
