/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part7


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredTransitionMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingSquareWiredCarrier n → FKIsingSquareWiredCarrier n
  | .source => .bond (fkIsingSquareWiredSourceDart n hn)
  | .terminal => .bond (fkIsingSquareWiredTerminalDart n hn)
  | .dart d => .dart (FKIsingMedialDart.localMate omega d)
  | .bond d =>
      if d = fkIsingSquareWiredSourceDart n hn then .source
      else if d = fkIsingSquareWiredTerminalDart n hn then .terminal
      else .bond (fkIsingSquareWiredBondMate n hn d)

end
end StatMech.Universality
