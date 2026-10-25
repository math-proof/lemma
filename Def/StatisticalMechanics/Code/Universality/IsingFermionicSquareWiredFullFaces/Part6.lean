/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareWiredFullLeftDart (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (fkIsingSquareWiredBoundaryDart n hn (.west k)), by
    rw [fkIsingSquareWiredBoundaryDart_west_eq_leftEdge]
    rfl⟩

def fkIsingSquareWiredFullLeftBond (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.bond (fkIsingSquareWiredBoundaryDart n hn (.north k)), by
    simp [fkIsingSquareWiredCarrierColor, fkIsingSquareWiredBoundaryDart,
      fkIsingSquareDirectionDart_turn, fkIsingSquareWiredTurnColor]⟩

end
end StatMech.Universality
